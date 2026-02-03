use crate::{
    Binder1,
    BinderN,
    Comp,
    IGen,
    Ident,
    NodeApply,
    NodeSeq,
    Pattern,
    Val,
};

use std::collections::HashMap;

fn try_vec_1<T>(mut v: Vec<T>) -> Result<T, Vec<T>> {
    if v.len() == 1 {
        Ok(v.pop().unwrap())
    } else {
        Err(v)
    }
}

impl Binder1 {
    pub fn unroll_rec(self, defs: &HashMap<String, Comp>, igen: &mut IGen) -> Self { match self {
        Binder1::Eq(b, vs1, vs2) => {
            let vs1 = vs1.into_iter()
                .map(|v| v.unroll_rec(defs, igen)).collect();
            let vs2 = vs2.into_iter()
                .map(|v| v.unroll_rec(defs, igen)).collect();
            Binder1::Eq(b, vs1, vs2)
        }
        Binder1::LogQuantifier(q, xs, m) => {
            let m = Box::new(m.unroll_rec(defs, igen));
            Binder1::LogQuantifier(q, xs, m)
        }
        Binder1::LogOp1(o, v) => {
            let v = v.unroll_rec(defs, igen);
            Binder1::LogOp1(o, v)
        }
        Binder1::LogOpN(o, vs) => {
            let vs = vs.into_iter().map(|v| v.unroll_rec(defs, igen)).collect();
            Binder1::LogOpN(o, vs)
        }
        Binder1::QMode(q, m) => Binder1::QMode(q, Box::new(m.unroll_rec(defs, igen))),
    }}
}

impl NodeSeq {
    pub fn unroll_rec(mut self, defs: &HashMap<String, Comp>, igen: &mut IGen) -> Self {
        self.content = Box::new((*self.content).unroll_rec(defs, igen));
        self
    }
}

impl BinderN {
    pub fn unroll_rec(self, defs: &HashMap<String, Comp>, igen: &mut IGen) -> Self { match self {
        BinderN::Call(c) => BinderN::Call(c),
        BinderN::Seq(m) if m.unroll => {
            BinderN::Seq(m.unroll_rec(defs, igen))
        }
        BinderN::Seq(m) => {
            panic!("Got no-unroll for {:?}", m);
            // BinderN::Seq(m)
        }
    }}
}

impl NodeApply {
    fn unroll_rec(mut self, defs: &HashMap<String, Comp>, igen: &mut IGen) -> Self {
        if self.unroll {
            self.f = Box::new(self.f.unroll_rec(defs, igen));
        } else {
            // panic!("Got no-unroll for {:?}", &self.f)
        }
        self.vals = self.vals.into_iter()
            .map(|v| v.unroll_rec(defs, igen))
            .collect();
        self
    }
}

impl Comp {
    pub fn unroll_rec(self, defs: &HashMap<String, Comp>, igen: &mut IGen) -> Self { match self {
        Self::Apply(e) => Self::Apply(e.unroll_rec(defs, igen)),
        Self::Bind1(b, x, m) => Self::Bind1(b.unroll_rec(defs, igen), x, Box::new(m.unroll_rec(defs, igen))),
        Self::BindN(b, ps, m2) => match try_vec_1(ps) {
            // For a "let _ = ..", we don't actually want to unroll
            // the right side of the let, since this is being used as
            // an instantiation.
            Ok(Pattern::NoBind) => Self::BindN(b, vec![Pattern::NoBind], Box::new(m2.unroll_rec(defs, igen))),
            Ok(p) => Self::BindN(b.unroll_rec(defs, igen), vec![p], Box::new(m2.unroll_rec(defs, igen))),
            Err(ps) => Self::BindN(b.unroll_rec(defs, igen), ps, Box::new(m2.unroll_rec(defs, igen))),
        }
        Self::Force(v) => Self::Force(v.unroll_rec(defs, igen)),
        Self::Fun(xs, m) => {
            let m = Box::new(m.unroll_rec(defs, igen));
            Self::Fun(xs, m)
        }
        Self::Ite(v, m1, m2) => {
            let v = v.unroll_rec(defs, igen);
            let m1 = Box::new(m1.unroll_rec(defs, igen));
            let m2 = Box::new(m2.unroll_rec(defs, igen));
            Self::Ite(v, m1, m2)
        }
        Self::Match(v, arms) => {
            let v = v.unroll_rec(defs, igen);
            let arms = arms.into_iter()
                .map(|(a, m)| (a, Box::new(m.unroll_rec(defs, igen))))
                .collect();
            Self::Match(v, arms)
        }
        Self::Return(vs) => Self::Return(vs.into_iter().map(|v| v.unroll_rec(defs, igen)).collect()),
    }}
}

impl Val {
    pub fn unroll_rec(self, defs: &HashMap<String, Comp>, igen: &mut IGen) -> Self { match self {
        Val::Thunk(m) => Val::Thunk(Box::new(m.unroll_rec(defs, igen))),
        Val::Tuple(vs) => Val::Tuple(vs.into_iter().map(|v| v.unroll_rec(defs, igen)).collect()),
        Val::Var(Ident::Manual(x), ts, path, true) => {
            match defs.get(&x) {
                Some(def) => {
                    Val::Thunk(Box::new(def.clone().rename(igen).builder().flatten().build_no_context()))
                }
                None => Val::Var(Ident::Manual(x), ts, path, true),
            }
        }
        v => v,
    }}
}
