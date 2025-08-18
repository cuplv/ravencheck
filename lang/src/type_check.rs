use crate::{
    Binder1,
    BinderN,
    Comp,
    CType,
    Literal,
    LogOpN,
    Op,
    Sig,
    Sort,
    Val,
    VName,
    VType,
    Pattern,
};

use std::collections::HashMap;

#[derive(Clone,Debug)]
pub struct TypeContext {
    bindings: HashMap<VName, VType>,
    sig: Sig,
}

impl TypeContext {
    pub fn new(sig: Sig) -> Self {
        TypeContext{
            bindings: HashMap::new(),
            sig,
        }
    }
    fn plus(mut self, x: VName, t: VType) -> Self {
        self.bindings.insert(x,t);
        self
    }
    fn append(mut self, c: Vec<(VName,VType)>) -> Self {
        self.bindings.extend(c.into_iter());
        self
    }
    fn get(&self, x: &VName) -> Result<VType, TypeError> {
        match self.bindings.get(x) {
            Some(t) => Ok(t.clone()),
            None => Err(format!("Unbound identifier {:?}", x)),
        }
    }
}

type TypeError = String;

fn unwrap_one<T: Clone>(v: &Vec<T>) -> Result<T, TypeError> {
    if v.len() != 1 {
        Err(format!("Got multi-binder or multi-return"))
    } else {
        Ok(v[0].clone())
    }
}

impl Comp {
    pub fn type_check(&self, t: &CType, sig: &Sig) -> Result<(), TypeError> {
        let inferred = self.type_of(TypeContext::new(sig.clone()))?;
        if t == &inferred {
            Ok(())
        } else {
            Err(format!("Expected type {:?}, got {:?}", t, inferred))
        }
    }
    fn type_check_r(&self, t: &CType, tc: TypeContext) -> Result<(), TypeError>
    {
        let ct = self.type_of(tc)?;
        if t == &ct {
            Ok(())
        } else {
            Err(format!("Expected type {:?}, got {:?}", t, ct))
        }
    }
    pub fn type_of(&self, mut tc: TypeContext) -> Result<CType, TypeError> {
        match self {
            Self::Apply(m, vs) => match m.type_of(tc.clone())? {
                CType::Fun(ts, ct) => {
                    if ts.len() != vs.len() {
                        return Err(format!(
                            "Function expected {} arg(s) of type {:?}, but was applied to {} value(s).",
                            ts.len(),
                            ts,
                            vs.len(),
                        ))
                    }
                    for (v,t) in vs.iter().zip(ts) {
                        let vt = v.type_of(tc.clone())?;
                        if vt != t {
                            return Err(format!(
                                "Function expected {:?}, but value {:?} has type {:?}",
                                t,
                                v,
                                vt,
                            ))
                        }
                    }
                    Ok(*ct)
                }
                ct => Err(format!(
                    "Non-fun {:?} applied as function",
                    ct,
                )),
            }
            Self::Bind1(Binder1::Eq(_, args1, args2), x, m) => {
                assert!(args1.len() == 1);
                assert!(args2.len() == 1);
                let t1 = args1[0].type_of(tc.clone())?;
                let t2 = args2[0].type_of(tc.clone())?;
                if t1 != t2 {
                    Err(format!("Tried to Eq {:?} against {:?}", t1, t2))
                } else if t1.contains_thunk() {
                    Err(format!("Cannot Eq values that contain thunks: {:?}", t1))
                } else {
                    m.type_of(tc.plus(x.clone(), VType::prop()))
                }
            }
            Self::Bind1(Binder1::LogNot(v), x, m) => {
                v.type_check_r(&VType::prop(), tc.clone())?;
                m.type_of(tc.plus(x.clone(), VType::prop()))
            }
            Self::Bind1(Binder1::LogOpN(op, vs), x, m) => {
                match op {
                    LogOpN::And | LogOpN::Or => {
                        for v in vs {
                            v.type_check_r(&VType::prop(), tc.clone())?;
                        }
                        m.type_of(tc.plus(x.clone(), VType::prop()))
                    }
                    op => panic!("Unexpected op in type_check: {:?}", op),
                }
            }
            Self::Bind1(Binder1::LogQuantifier(_q, xs, body), x, m) => {
                for (_,vt) in xs {
                    let () = vt.validate(&tc.sig)?;
                }
                body.type_check_r(
                    &CType::return_prop(),
                    tc.clone().append(xs.clone()),
                )?;
                m.type_of(
                    tc.plus(x.clone(), VType::prop()),
                )
            }
            Self::BindN(BinderN::Call(_name, _args), _xs, _m) => {
                panic!(
                    "BinderN::Call should only appear in phases after type_check"
                )
            }
            Self::BindN(BinderN::Seq(m1), ps, m) => {
                let p = unwrap_one(ps)?;
                let vt = m1.type_of(tc.clone())?.unwrap_return()?;
                let ct2 = p.bindings(vt)?;
                m.type_of(tc.append(ct2))
            }
            Self::Force(v) => {
                match v.type_of(tc)? {
                    VType::Thunk(ct) => Ok(*ct),
                    vt => Err(format!(
                        "Non-thunk {:?} with type {:?} in Force position.",
                        v,
                        vt,
                    ))
                }
            }
            Self::Fun(xs, m) => {
                let mut ts = Vec::new();
                for (x,o) in xs.clone().into_iter() {
                    match o {
                        Some(t) => {
                            let () = t.validate(&tc.sig)?;
                            ts.push(t.clone());
                            tc = tc.plus(x, t);
                        }
                        None => {
                            return Err(format!(
                                "No type annotation for {:?}",
                                x,
                            ))
                        }
                    }
                }
                Ok(CType::fun(ts, m.type_of(tc)?))
            }
            Self::Ite(cond, then_b, else_b) => {
                cond.type_check_r(&VType::prop(), tc.clone())?;
                let then_t = then_b.type_of(tc.clone())?;
                let else_t = else_b.type_of(tc)?;
                if then_t == else_t {
                    Ok(then_t)
                } else {
                    Err(format!(
                        "
if-then-else has branches with mismatched types: {:?} vs. {:?}",
                        then_t,
                        else_t,
                    ))
                }
            }
            Self::Return(vs) => {
                if vs.len() == 1 {
                    Ok(CType::Return(vs[0].type_of(tc)?))
                } else {
                    Err(format!("Multi-return {:?}", vs))
                }
            }
        }
    }
}

impl CType {
    fn unwrap_return(self) -> Result<VType, TypeError> {
        match self {
            CType::Return(t) => Ok(t),
            ct => Err(format!("Expected Return(..), got {:?}", ct)),
        }
    }
}

impl Pattern {
    fn bindings(self, t: VType) -> Result<Vec<(VName,VType)>, TypeError> {
        match (self, t) {
            (Pattern::NoBind, _) => Ok(Vec::new()),
            (Pattern::Atom(x), t) => Ok(vec![(x,t)]),
            (Pattern::Tuple(ps), VType::Tuple(ts)) => {
                if ps.len() == ts.len() {
                    let mut out = Vec::new();
                    for (p,t) in ps.into_iter().zip(ts) {
                        out.append(&mut p.bindings(t)?);
                    }
                    Ok(out)
                } else {
                    Err(format!(
                        "Pattern tuple size mismatch: {:?} vs. {:?}",
                        ps,
                        ts,
                    ))
                }
            }
            (p,t) => {
                Err(format!(
                    "Pattern {:?} does not match value {:?}",
                    p,
                    t,
                ))
            }
        }
    }
}

impl Sig {
    fn get_type(&self, s: String) -> Result<VType, TypeError> {
        for (name, op) in self.ops.clone() {
            if name == s {
                match op {
                    Op::Const(op) => {
                        return Ok(op.vtype)
                    }
                    Op::Direct(m) => {
                        match m.type_of(TypeContext::new(self.clone()))? {
                            CType::Return(t) => return Ok(t),
                            _ => return Err(format!(
                                "
signature function \"{}\" did not have a computation type",
                                s,
                            )),
                        }
                    }
                    Op::Fun(op) => {
                        return Ok(VType::fun_v(
                            op.inputs,
                            op.output,
                        ))
                    },
                    Op::Pred(op) => {
                        return Ok(VType::fun_v(
                            op.inputs,
                            VType::prop(),
                        ))
                    },
                    Op::Rec(op) => {
                        return Ok(VType::fun_v(
                            op.inputs,
                            op.output,
                        ))
                    }
                    Op::Symbol(op) => {
                        return Ok(VType::fun_v(
                            op.inputs,
                            VType::prop(),
                        ))
                    },
                }
            }
        }
        Err(format!("Identifier {:?} is not bound or declared as a primitive operation. The following operations are declared: {:?}", s, self.all_op_names()))
    }
}

impl Val {
    fn type_check_r(&self, t: &VType, tc: TypeContext) -> Result<(), TypeError>
    {
        let vt = self.type_of(tc)?;
        if t == &vt {
            Ok(())
        } else {
            Err(format!("Expected type {:?}, got {:?}", t, vt))
        }
    }
    fn type_of(&self, tc: TypeContext) -> Result<VType, TypeError> {
        match self {
            Self::Literal(l) => match l {
                Literal::LogTrue => Ok(VType::prop()),
                Literal::LogFalse => Ok(VType::prop()),
                l => panic!("No type for literal {:?}", l),
            }
            Self::Thunk(m) => Ok(VType::Thunk(Box::new(m.type_of(tc)?))),
            Self::Tuple(vs) => {
                let mut ts = Vec::new();
                for v in vs {
                    ts.push(v.type_of(tc.clone())?);
                }
                Ok(VType::Tuple(ts))
            }
            Self::Var(x) => {
                match tc.get(x) {
                    Ok(t) => Ok(t),
                    Err(_) => match x {
                        VName::Manual(s) => tc.sig.get_type(s.clone()),
                        VName::Auto(_n) => panic!("Unbound auto var {:?}", x),
                    }
                }
            }
        }
    }
}

impl CType {
    pub fn validate(&self, sig: &Sig) -> Result<(), TypeError> {
        match self {
            Self::Fun(ts, ct) => {
                for t in ts {
                    match t.validate(sig) {
                        Ok(()) => {},
                        Err(e) => return Err(e),
                    }
                }
                ct.validate(sig)
            }
            Self::Return(vt) => vt.validate(sig),
        }
    }
}

impl VType {
    pub fn validate(&self, sig: &Sig) -> Result<(), TypeError> {
        match self {
            Self::Atom(Sort::Prop) => Ok(()),
            Self::Atom(Sort::UI(s)) => {
                if sig.sorts.contains(s) {
                    Ok(())
                } else {
                    Err(format!("Sort {} is undeclared", s))
                }
            }
            Self::Thunk(ct) => {
                ct.validate(sig)
            }
            Self::Tuple(ts) => {
                for t in ts {
                    match t.validate(sig) {
                        Ok(()) => {},
                        Err(e) => return Err(e),
                    }
                }
                Ok(())
            }
        }
    }
}
