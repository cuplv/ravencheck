use crate::{
    Binder1,
    BinderN,
    Comp,
    NodeApply,
    NodeSeq,
    Pattern,
    Val,
};

fn try_vec_1<T>(mut v: Vec<T>) -> Result<T, Vec<T>> {
    if v.len() == 1 {
        Ok(v.pop().unwrap())
    } else {
        Err(v)
    }
}

impl NodeSeq {
    pub fn erase_wildcard_lets(mut self) -> Self {
        self.content = Box::new((*self.content).erase_wildcard_lets());
        self
    }
}

impl Binder1 {
    pub fn erase_wildcard_lets(self) -> Self { match self {
        Binder1::Eq(b, vs1, vs2) => {
            let vs1 = vs1.into_iter()
                .map(|v| v.erase_wildcard_lets()).collect();
            let vs2 = vs2.into_iter()
                .map(|v| v.erase_wildcard_lets()).collect();
            Binder1::Eq(b, vs1, vs2)
        }
        Binder1::LogQuantifier(q, xs, m) => {
            let m = Box::new(m.erase_wildcard_lets());
            Binder1::LogQuantifier(q, xs, m)
        }
        Binder1::LogOp1(o, v) => {
            let v = v.erase_wildcard_lets();
            Binder1::LogOp1(o, v)
        }
        Binder1::LogOpN(o, vs) => {
            let vs = vs.into_iter().map(|v| v.erase_wildcard_lets()).collect();
            Binder1::LogOpN(o, vs)
        }
        Binder1::QMode(q, m) => Binder1::QMode(q, Box::new(m.erase_wildcard_lets())),
    }}
}

impl BinderN {
    pub fn erase_wildcard_lets(self) -> Self { match self {
        BinderN::Call(c) => BinderN::Call(c),
        BinderN::Seq(m) => BinderN::Seq(m.erase_wildcard_lets()),
    }}
}

impl NodeApply {
    fn erase_wildcard_lets(mut self) -> Self {
        self.f = Box::new(self.f.erase_wildcard_lets());
        self
    }
}

impl Comp {
    pub fn erase_wildcard_lets(self) -> Self { match self {
        Self::Apply(e) => Self::Apply(e.erase_wildcard_lets()),
        Self::Bind1(b, x, m) => Self::Bind1(b.erase_wildcard_lets(), x, Box::new(m.erase_wildcard_lets())),
        Self::BindN(b, ps, m2) => match try_vec_1(ps) {
            Ok(Pattern::NoBind) => m2.erase_wildcard_lets(),
            Ok(p) => Self::BindN(b.erase_wildcard_lets(), vec![p], Box::new(m2.erase_wildcard_lets())),
            Err(ps) => Self::BindN(b.erase_wildcard_lets(), ps, Box::new(m2.erase_wildcard_lets())),
        }
        Self::Force(v) => Self::Force(v.erase_wildcard_lets()),
        Self::Fun(xs, m) => {
            let m = Box::new(m.erase_wildcard_lets());
            Self::Fun(xs, m)
        }
        Self::Ite(v, m1, m2) => {
            let v = v.erase_wildcard_lets();
            let m1 = Box::new(m1.erase_wildcard_lets());
            let m2 = Box::new(m2.erase_wildcard_lets());
            Self::Ite(v, m1, m2)
        }
        Self::Match(v, arms) => {
            let v = v.erase_wildcard_lets();
            let arms = arms.into_iter()
                .map(|(a, m)| (a, Box::new(m.erase_wildcard_lets())))
                .collect();
            Self::Match(v, arms)
        }
        Self::Return(vs) => Self::Return(vs.into_iter().map(|v| v.erase_wildcard_lets()).collect()),
    }}
}

impl Val {
    pub fn erase_wildcard_lets(self) -> Self { match self {
        Val::Thunk(m) => Val::Thunk(Box::new(m.erase_wildcard_lets())),
        Val::Tuple(vs) => Val::Tuple(vs.into_iter().map(|v| v.erase_wildcard_lets()).collect()),
        v => v,
    }}
}
