use crate::{
    BType,
    Binder1,
    BinderN,
    Builder,
    CType,
    Comp,
    LogOpN,
    MatchArm,
    Op,
    OpCode,
    RirFn,
    RirFnSig,
    Val,
    Ident,
    VType,
};

use std::collections::HashMap;

type Subs = HashMap<String, VType>;

fn expand_types_sig(
    xs: Vec<(Ident,Option<VType>)>, subs: &Subs
) -> Vec<(Ident,Option<VType>)> {
    xs.into_iter().map(|(x,t)| {
        let t = match t {
            Some(t) => Some(t.expand_aliases(subs)),
            None => None,
        };
        (x,t)
    }).collect()
}

fn expand_types_q(
    xs: Vec<(Ident,VType)>, subs: &Subs
) -> Vec<(Ident,VType)> {
    xs.into_iter().map(|(x,t)| {
        (x,t.expand_aliases(subs))
    }).collect()
}

fn expand_types_tas(
    tas: Vec<VType>, subs: &Subs
) -> Vec<VType> {
    tas
        .into_iter()
        .map(|t| t.expand_aliases(subs))
        .collect()
}

impl Binder1 {
    pub fn expand_types(self, subs: &Subs) -> Self {
        match self {
            Self::Eq(b, vs1, vs2) => Self::Eq(
                b,
                vs1.into_iter().map(|v| v.expand_types(subs)).collect(),
                vs2.into_iter().map(|v| v.expand_types(subs)).collect(),
            ),
            Self::LogQuantifier(q, xs, m) => Self::LogQuantifier(
                q,
                expand_types_q(xs, subs),
                Box::new(m.expand_types(subs)),
            ),
            Self::LogOp1(op, v) => Self::LogOp1(op, v.expand_types(subs)),
            Self::LogOpN(op, vs) => Self::LogOpN(
                op.expand_types(subs),
                vs.into_iter().map(|v| v.expand_types(subs)).collect(),
            ),
            Self::QMode(q, m) => Self::QMode(
                q,
                Box::new(m.expand_types(subs)),
            ),
        }
    }
}

impl Builder {
    pub fn expand_types(self, subs: &Subs) -> Self {
        let subs = subs.clone();
        self.map(move |c: Comp| c.expand_types(&subs))
    }
}

impl LogOpN {
    pub fn expand_types(self, subs: &Subs) -> Self {
        match self {
            LogOpN::Or => LogOpN::Or,
            LogOpN::And => LogOpN::And,
            LogOpN::Pred(oc,b) => LogOpN::Pred(oc.expand_types(subs), b),
        }
    }
}

impl OpCode {
    pub fn expand_types(mut self, subs: &Subs) -> Self {
        self.types = self.types
            .into_iter()
            .map(|vt| vt.expand_types(subs))
            .collect();
        self
    }
}

impl BinderN {
    pub fn expand_types(self, subs: &Subs) -> Self {
        match self {
            Self::Call(mut call) => {
                call.code = call.code.expand_types(subs);
                call.args = call.args.into_iter()
                    .map(|v| v.expand_types(subs))
                    .collect();
                Self::Call(call)
            }
            //     Self::Call(
            //     oc.expand_types(subs),
            //     vs.into_iter().map(|v| v.expand_types(subs)).collect(),
            // ),
            Self::Seq(m) => Self::Seq(Box::new(m.expand_types(subs))),
        }
    }
}

impl Comp {
    pub fn expand_types_from_call(
        self,
        targs: &Vec<VType>,
        tas: &Vec<String>,
    ) -> Option<Self> {
        if targs.len() == tas.len() {
            let subs = tas.iter().cloned().zip(targs.iter().cloned());
            Some(self.expand_types(&HashMap::from_iter(subs)))
        } else {
            None
        }
    }
    pub fn expand_types(self, subs: &Subs) -> Self {
        match self {
            Self::Apply(m, tas, vs) => Self::Apply(
                Box::new(m.expand_types(subs)),
                expand_types_tas(tas, subs),
                vs.into_iter().map(|v| v.expand_types(subs)).collect(),
            ),
            Self::BindN(b, ps, m) => Self::BindN(
                b.expand_types(subs),
                ps,
                Box::new(m.expand_types(subs)),
            ),
            Self::Bind1(b, x, m) => Self::Bind1(
                b.expand_types(subs),
                x,
                Box::new(m.expand_types(subs)),
            ),
            Self::Force(v) => Self::Force(v.expand_types(subs)),
            Self::Fun(xs, m) => Self::Fun(
                expand_types_sig(xs, subs),
                Box::new(m.expand_types(subs)),
            ),
            Self::Ite(cond, then_b, else_b) => Self::Ite(
                cond.expand_types(subs),
                Box::new(then_b.expand_types(subs)),
                Box::new(else_b.expand_types(subs)),
            ),
            Self::Match(target, arms) => Self::Match(
                target.expand_types(subs),
                arms.into_iter().map(|(m,c)| {
                    (m.expand_types(subs),
                     Box::new(c.expand_types(subs)),
                    )
                }).collect(),
            ),
            Self::Return(vs) => Self::Return(
                vs.into_iter().map(|v| v.expand_types(subs)).collect()
            ),
            // c => todo!("expand_types {:?}", c),
        }
    }
}

impl MatchArm {
    // For now, this does nothing
    fn expand_types(mut self, subs: &Subs) -> Self {
        self.code = self.code.expand_types(subs);
        self
    }
}

impl Val {
    pub fn expand_types(self, subs: &Subs) -> Self {
        match self {
            Self::Literal(l) => Self::Literal(l),
            Self::OpCode(om, oc) => Self::OpCode(om, oc.expand_types(subs)),
            Self::Thunk(m) => Self::Thunk(Box::new(m.expand_types(subs))),
            Self::Tuple(vs) => Self::Tuple(
                vs.into_iter().map(|v| v.expand_types(subs)).collect()
            ),
            Self::Var(name, args, path, is_neg) => Self::Var(
                name,
                args.into_iter().map(|a| a.expand_types(subs)).collect(),
                path,
                is_neg,
            ),
        }
    }
}

impl CType {
    pub fn expand_types(self, subs: &Subs) -> Self {
        self.expand_aliases(subs)
    }
}
    

impl VType {
    pub fn expand_types_from_call(
        self,
        targs: &Vec<VType>,
        tas: &Vec<String>,
    ) -> Result<Self,String> {
        if targs.len() == tas.len() {
            let subs = tas.iter().cloned().zip(targs.iter().cloned());
            Ok(self.expand_types(&HashMap::from_iter(subs)))
        } else {
            Err(format!("mismatch between number of type args: {:?} does not match expected {:?}", targs, tas))
        }
    }
    pub fn expand_types(self, subs: &Subs) -> Self {
        self.expand_aliases(subs)
    }
}

impl BType {
    pub fn expand_types(self, subs: &Subs) -> VType {
        self.expand_aliases(subs)
    }
}

impl Op {
    pub fn expand_types_from_call(
        self,
        targs: &Vec<VType>,
        tas: &Vec<String>,
    ) -> Option<Self> {
        if targs.len() == tas.len() {
            let subs = tas.iter().cloned().zip(targs.iter().cloned());
            Some(self.expand_types(&HashMap::from_iter(subs)))
        } else {
            None
        }
    }
    pub fn expand_types(self, subs: &Subs) -> Self {
        match self {
            Op::Const(mut op) => {
                op.vtype = op.vtype.expand_types(subs);
                Op::Const(op)
            }
            Op::Direct(c) => Op::Direct(c.expand_types(subs)),
            Op::Fun(mut op) => {
                op.inputs =
                    op.inputs.into_iter().map(|t| t.expand_types(subs)).collect();
                op.output = op.output.expand_types(subs);
                op.axioms =
                    op.axioms.into_iter().map(|a| a.expand_types(subs)).collect();
                Op::Fun(op)
            }
            Op::Pred(mut op) => {
                op.inputs =
                    op.inputs.into_iter().map(|t| t.expand_types(subs)).collect();
                op.axioms =
                    op.axioms.into_iter().map(|a| a.expand_types(subs)).collect();
                Op::Pred(op)
            }
            Op::Rec(mut op) => {
                op.inputs =
                    op.inputs.into_iter().map(|t| t.expand_types(subs)).collect();
                op.output = op.output.expand_types(subs);
                op.axioms =
                    op.axioms.into_iter().map(|a| a.expand_types(subs)).collect();
                op.def = op.def.expand_types(subs);
                Op::Rec(op)
            }
            Op::Symbol(mut op) => {
                op.inputs =
                    op.inputs.into_iter().map(|t| t.expand_types(subs)).collect();
                Op::Symbol(op)
            }
        }
    }
}

impl RirFn {
    pub fn expand_types(mut self, subs: &HashMap<String,VType>) -> Self {
        self.sig = self.sig.expand_types(subs);

        // Remove any type aliases that are shadowed by the type
        // abstractions.
        let mut subs = subs.clone();
        for a in self.sig.tas.iter() {
            subs.remove(a);
        }
        self.body = self.body.expand_types(&subs);
        self
    }
}

impl RirFnSig {
    pub fn expand_types(mut self, subs: &HashMap<String,VType>) -> Self {
        // Remove any type aliases that are shadowed by the type
        // abstractions.
        let mut subs = subs.clone();
        for a in self.tas.iter() {
            subs.remove(a);
        }

        self.inputs = self.inputs
            .into_iter()
            .map(|(p,t)| (p, t.expand_types(&subs)))
            .collect();
        self.output = self.output.expand_types(&subs);
        self
    }
}
