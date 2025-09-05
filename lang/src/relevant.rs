use crate::{
    Axiom,
    Binder1,
    BinderN,
    BType,
    Comp,
    LogOpN,
    OpCode,
    OpMode,
    Sig,
    Val,
    VType,
};

use std::collections::HashMap;
use std::collections::HashSet;

pub struct Relevant {
    base_types: HashSet<BType>,
    ops: HashSet<OpCode>,
}

impl Relevant {
    fn new() -> Self {
        Self{
            base_types: HashSet::new(),
            ops: HashSet::new(),
        }
    }
    pub fn union(self, other: Self) -> Self {
        let base_types =
            self.base_types.union(&other.base_types).cloned().collect();
        let ops =
            self.ops.union(&other.ops).cloned().collect();
        Self { base_types, ops }
    }
    pub fn add_base_type(mut self, t: BType) -> Self {
        self.base_types.insert(t);
        self
    }
    pub fn add_op(mut self, ident: String, types: Vec<VType>) -> Self {
        self.ops.insert(OpCode{ident,types});
        self
    }
    pub fn add_oc(mut self, oc: OpCode) -> Self {
        self.ops.insert(oc);
        self
    }
    pub fn base_types(&self) -> &HashSet<BType> {
        &self.base_types
    }
    pub fn ops(&self) -> &HashSet<OpCode> {
        &self.ops
    }
}

impl Comp {
    pub fn relevant(&self, sig: &Sig) -> Relevant {
        let mut rel = Relevant::new();
        match self {
            Self::Bind1(b, _x, m) => {
                match b {
                    Binder1::LogQuantifier(_q, xs, body) => {
                        rel = rel.union(body.relevant(sig));
                        for (_x,t) in xs {
                            for bt in t.clone().flatten() {
                                rel =
                                    rel.add_base_type(bt.unwrap_base().unwrap());
                            }
                        }
                    }
                    Binder1::LogOpN(op, vs) => {
                        for v in vs {
                            rel = rel.union(v.relevant(sig));
                        }
                        match op {
                            LogOpN::Or => {},
                            LogOpN::And => {},
                            LogOpN::Pred(code,_) => {
                                rel = rel.add_oc(code.clone());
                            }
                        }
                    }
                    Binder1::Eq(_, vs1, vs2) => {
                        for v in vs1 {
                            rel = rel.union(v.relevant(sig));
                        }
                        for v in vs2 {
                            rel = rel.union(v.relevant(sig));
                        }
                    }
                    b => todo!("relevant for {:?}", b),
                }
                rel = rel.union(m.relevant(sig));
            }
            Self::BindN(b, _xs, _m) => {
                match b {
                    BinderN::Call(_oc, _args) =>
                        todo!("relevant for BinderN::Call"),
                    _ => todo!("relevant for BinderN"),
                }
            }
            Self::Return(..) => {},
            m => todo!("relevant for {:?}", m),
        }
        rel
    }
}

impl Val {
    fn relevant(&self, sig: &Sig) -> Relevant {
        let mut rel = Relevant::new();
        match self {
            Self::Literal(..) => {},
            Self::OpCode(om, oc) => match om {
                OpMode::Const | OpMode::ZeroArgAsConst => {
                    rel = rel.add_oc(oc.clone());
                }
                OpMode::RelAbs => panic!("free RelAbs should be gone before checking 'relevant'"),
            }
            Self::Thunk(..) => panic!("Thunk should be gone before checking 'relevant'"),
            Self::Tuple(vs) => {
                for v in vs {
                    rel = rel.union(v.relevant(sig));
                }
            }
            Self::Var(..) => {},
        }
        rel
    }
}

impl Sig {
    pub fn relevant_with_axioms(&self, term: &Comp) -> (Relevant, Vec<Comp>) {
        let mut relevant = term.relevant(self);

        let mut inst_axioms: Vec<Comp> = Vec::new();
        for a in &self.axioms {
            if a.tas.len() == 0 {
                inst_axioms.push(a.body.clone());
            } else {
                for t in relevant.base_types() {
                    match a.inst_for(t) {
                        Some(a) => {
                            inst_axioms.push(a);
                        }
                        None => {}
                    }
                }
            }
        }

        // Add relevant items from axioms
        for a in &inst_axioms {
            relevant = relevant.union(a.relevant(self));
        }

        // Do not recurse...

        (relevant, inst_axioms)
    }
}

impl Axiom {
    /// Instantiate for the given BType, if it triggers a rule.
    pub fn inst_for(&self, b: &BType) -> Option<Comp> {
        for (l,r) in &self.inst_rules {
            match (l,b) {
                (BType::UI(name_l, args_l), BType::UI(name, args)) if name_l == name => {
                    println!("Matching {} with {}", l, b);
                    let mut matches: HashMap<String,VType> = HashMap::new();
                    for (a_l,a) in args_l.iter().zip(args) {
                        match a_l.clone().unwrap_base().unwrap().get_ta() {
                            Some(s) => {
                                matches.insert(s.clone(), a.clone());
                            },
                            None => {}
                        }
                    }
                    let mut args = Vec::new();
                    args.push(r.clone().expand_types(&matches));
                    println!("Subbing types {:?} for {:?}", &args, &self.tas);
                    let body = self.body.clone().expand_types_from_call(
                        &args,
                        &self.tas
                    ).unwrap();
                    println!("Inst axiom body: {:?}", &body);
                    return Some(body);
                }
                (l,b) => {
                    println!("Did not match {} with {}", l, b);
                }
            }
        }
        None
    }
}
