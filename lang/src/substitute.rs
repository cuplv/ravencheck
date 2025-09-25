use crate::{
    Binder1,
    BinderN,
    Comp,
    Pattern,
    Val,
    VName,
};

impl Binder1 {
    fn substitute(self, x: &VName, v: &Val) -> Self {
        match self {
            Self::Eq(pos, args1, args2) => {
                let args1 =
                    args1.into_iter().map(|a| a.substitute(x,v));
                let args2 =
                    args2.into_iter().map(|a| a.substitute(x,v));
                Self::Eq(pos, args1.collect(), args2.collect())
            }
            Self::LogQuantifier(q, xs, m) => {
                let shadowed = xs.iter().any(|(x2,_)| x == x2);
                if shadowed {
                    Self::LogQuantifier(q,xs,m)
                } else {
                    let m2 = m.substitute(x,v);
                    Self::LogQuantifier(q, xs, Box::new(m2))
                }
            }
            Self::LogNot(v2) => Self::LogNot(v2.substitute(x,v)),
            Self::LogOpN(op, vs) => {
                let mut vs2 = Vec::new();
                for v2 in vs {
                    vs2.push(v2.substitute(x,v));
                }
                Self::LogOpN(op.clone(), vs2)
            }
        }
    }
}

impl BinderN {
    fn substitute(self, x: &VName, v: &Val) -> Self {
        match self {
            Self::Call(oc,vs) => Self::Call(
                oc,
                vs.into_iter().map(|v1| v1.substitute(x,v)).collect(),
            ),
            Self::Seq(m) => Self::Seq(Box::new(m.substitute(x, v))),
        }
    }
}

impl Comp {
    pub fn substitute(self, x: &VName, v: &Val) -> Self {
        match self {
            Self::Apply(m, targs, vs) => {
                Self::apply(
                    m.substitute(x,v),
                    targs,
                    vs
                        .into_iter()
                        .map(|v1| v1.substitute(x,v))
                        .collect::<Vec<Val>>()
                )
            }
            Self::Return(vs) => {
                Self::return_many(
                    vs
                        .into_iter()
                        .map(|e| e.substitute(x,v))
                        .collect::<Vec<Val>>()
                )
            }
            Self::Bind1(b, x2, m) => {
                let b2 = b.substitute(x,v);
                let m2 = if *x == x2 {
                    m.clone()
                } else {
                    Box::new(m.substitute(x,v))
                };
                Self::Bind1(b2, x2.clone(), m2)
            }
            Self::BindN(b, ps, m) => {
                let b2 = b.substitute(x,v);
                let m2 = if ps.iter().any(|p| p.contains(x)) {
                    m
                } else {
                    Box::new(m.substitute(x,v))
                };
                Self::BindN(b2, ps, m2)
            }
            Self::Force(v1) => Self::Force(v1.substitute(x,v)),
            Self::Fun(xs, m) => {
                let names: Vec<&VName> = xs.iter().map(|(x,_)| x).collect();
                if !names.contains(&x) {
                    Self::Fun(xs, Box::new(m.substitute(x,v)))
                } else {
                    Self::Fun(xs, m)
                }
            }
            Self::Ite(cond, then_b, else_b) => {
                Self::ite(
                    cond.substitute(x,v),
                    then_b.substitute(x,v),
                    else_b.substitute(x,v),
                )
            }
            Self::Match(target, arms) => {
                let mut new_arms = Vec::new();
                for (arm, comp) in arms {
                    let shadows = arm.binders
                        .clone()
                        .into_iter()
                        .map(|p| p.unwrap_vname().unwrap())
                        .collect::<Vec<_>>();
                    if !shadows.contains(&x) {
                        new_arms.push((arm, Box::new(comp.substitute(x,v))));
                    } else {
                        new_arms.push((arm, comp))
                    }
                }
                Self::Match(
                    target.substitute(x,v),
                    new_arms,
                )
            }
            // c => todo!("substitute for {:?}", c)
        }
    }
    pub fn substitute_many(mut self, ss: &Vec<(VName,Val)>) -> Self {
        for (x,v) in ss {
            self = self.substitute(x,v)
        }
        self
    }
}

impl Pattern {
    fn contains(&self, x: &VName) -> bool {
        match self {
            Self::NoBind => false,
            Self::Atom(y) => x == y,
            Self::Tuple(ps) => ps.iter().any(|p| p.contains(x)),
        }
    }
}

impl Val {
    fn substitute(self, x: &VName, v: &Val) -> Self {
        match self {
            Self::Var(x2, _, _) if *x == x2 => { v.clone() },
            Self::Thunk(c) => Self::Thunk(Box::new(c.substitute(x,v))),
            Self::Tuple(vs) => Self::Tuple(
                vs
                    .into_iter()
                    .map(|v1| v1.substitute(x,v))
                    .collect()
            ),
            _ => self,
        }
    }
}
