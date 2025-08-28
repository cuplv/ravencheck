use crate::{
    Binder1,
    BinderN,
    Comp,
    Sig,
    Val,
    VName,
    VType,
};

fn expand_types_sig(
    xs: Vec<(VName,Option<VType>)>, sig: &Sig
) -> Vec<(VName,Option<VType>)> {
    xs.into_iter().map(|(x,t)| {
        let t = match t {
            Some(t) => Some(t.expand_aliases(&sig.type_aliases)),
            None => None,
        };
        (x,t)
    }).collect()
}

fn expand_types_q(
    xs: Vec<(VName,VType)>, sig: &Sig
) -> Vec<(VName,VType)> {
    xs.into_iter().map(|(x,t)| {
        (x,t.expand_aliases(&sig.type_aliases))
    }).collect()
}

fn expand_types_tas(
    tas: Vec<VType>, sig: &Sig
) -> Vec<VType> {
    tas
        .into_iter()
        .map(|t| t.expand_aliases(&sig.type_aliases))
        .collect()
}

impl Binder1 {
    pub fn expand_types(self, sig: &Sig) -> Self {
        match self {
            Self::Eq(b, vs1, vs2) => Self::Eq(
                b,
                vs1.into_iter().map(|v| v.expand_types(sig)).collect(),
                vs2.into_iter().map(|v| v.expand_types(sig)).collect(),
            ),
            Self::LogQuantifier(q, xs, m) => Self::LogQuantifier(
                q,
                expand_types_q(xs, sig),
                Box::new(m.expand_types(sig)),
            ),
            Self::LogNot(v) => Self::LogNot(v.expand_types(sig)),
            Self::LogOpN(op, vs) => Self::LogOpN(
                op,
                vs.into_iter().map(|v| v.expand_types(sig)).collect(),
            ),
        }
    }
}

impl BinderN {
    pub fn expand_types(self, sig: &Sig) -> Self {
        match self {
            Self::Call(s, vs) => Self::Call(
                s,
                vs.into_iter().map(|v| v.expand_types(sig)).collect(),
            ),
            Self::Seq(m) => Self::Seq(Box::new(m.expand_types(sig))),
        }
    }
}

impl Comp {
    pub fn expand_types(self, sig: &Sig) -> Self {
        match self {
            Self::Apply(m, tas, vs) => Self::Apply(
                Box::new(m.expand_types(sig)),
                expand_types_tas(tas, sig),
                vs.into_iter().map(|v| v.expand_types(sig)).collect(),
            ),
            Self::BindN(b, ps, m) => Self::BindN(
                b.expand_types(sig),
                ps,
                Box::new(m.expand_types(sig)),
            ),
            Self::Bind1(b, x, m) => Self::Bind1(
                b.expand_types(sig),
                x,
                Box::new(m.expand_types(sig)),
            ),
            Self::Force(v) => Self::Force(v.expand_types(sig)),
            Self::Fun(xs, m) => Self::Fun(
                expand_types_sig(xs, sig),
                Box::new(m.expand_types(sig)),
            ),
            Self::Ite(cond, then_b, else_b) => Self::Ite(
                cond.expand_types(sig),
                Box::new(then_b.expand_types(sig)),
                Box::new(else_b.expand_types(sig)),
            ),
            Self::Return(vs) => Self::Return(
                vs.into_iter().map(|v| v.expand_types(sig)).collect()
            ),
        }
    }
}

impl Val {
    pub fn expand_types(self, sig: &Sig) -> Self {
        match self {
            Self::Thunk(m) => Self::Thunk(Box::new(m.expand_types(sig))),
            Self::Tuple(vs) => Self::Tuple(
                vs.into_iter().map(|v| v.expand_types(sig)).collect()
            ),
            v => v,
        }
    }
}
