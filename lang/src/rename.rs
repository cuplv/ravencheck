use crate::{
    Binder1,
    BinderN,
    Comp,
    Gen,
    Pattern,
    Val,
    VName,
    VType,
};

impl Binder1 {
    fn rename_r(self, gen: &mut Gen) -> Self {
        match self {
            Self::Eq(pos, vs1, vs2) => Self::Eq(
                pos,
                vs1.into_iter().map(|v| v.rename_r(gen)).collect(),
                vs2.into_iter().map(|v| v.rename_r(gen)).collect(),
            ),
            Self::LogNot(v) => Self::LogNot(v.rename_r(gen)),
            Self::LogOpN(op, vs) => {
                let vs2 = vs
                    .into_iter()
                    .map(|v| v.rename_r(gen))
                    .collect();
                Self::LogOpN(op, vs2)
            }
            Self::LogQuantifier(q, xs, m) => {
                // Start with xs = [(x1,s1), (x2,s2), ...]

                // Create ys = [y1, y2, ...]
                let ys: Vec<VName> = gen.next_many(xs.len());
                // Then subs = [(x1, Var(y1)), (x2, Var(y2)), ...]
                let subs: Vec<(VName,Val)> = xs
                    .iter()
                    .zip(&ys)
                    .map(|((x,_),y)| (x.clone(), y.clone().val()))
                    .collect();
                // And new_sig = [(y1,s1), (y2,s2), ...]
                let new_sig: Vec<(VName,VType)> = xs
                    .into_iter()
                    .zip(ys)
                    .map(|((_,s),y)| (y, s))
                    .collect();
                Self::LogQuantifier(q, new_sig, Box::new(
                    m.rename_r(gen).substitute_many(&subs)
                ))
            }
        }
    }
}

impl BinderN {
    fn rename_r(self, gen: &mut Gen) -> Self {
        match self {
            Self::Call(..) => todo!(),
            Self::Seq(m) => Self::Seq(Box::new(m.rename_r(gen))),
        }
    }
}

impl Comp {
    /// Replace all variables in a comp with unique auto-generated
    /// variables, using the given Gen.  The given Gen will
    /// be advanced to cover the new names.
    pub fn rename(self, gen: &mut Gen) -> Self {
        self.advance_gen(gen);
        self.rename_r(gen)
    }

    pub fn rename_r(self, gen: &mut Gen) -> Self {
        match self {
            Self::Apply(m, targs, vs) => {
                let m2 = m.rename_r(gen);
                let mut vs2 = Vec::new();
                for v in vs.into_iter() {
                    vs2.push(v.rename_r(gen));
                }
                Self::apply(m2, targs, vs2)
            }
            Self::Return(vs) => {
                let vs2 = vs
                    .into_iter()
                    .map(|v| v.rename_r(gen))
                    .collect();
                Self::Return(vs2)
            }
            Self::Bind1(b,x,m) => {
                // Rename any vars introduced within the binder.
                let b2 = b.rename_r(gen);
                // Create a fresh replacement for the bound variable.
                let x2 = gen.next();
                let m2 = m
                    // Rename any vars introduced in the sub-comp.
                    .rename_r(gen)
                    // Substitute the replacement into the sub-comp.
                    .substitute(&x, &x2.clone().val());
                Self::Bind1(b2,x2,Box::new(m2))
            }
            Self::BindN(b,ps,m) => {
                // Rename any vars introduced within the binder.
                let b2 = b.rename_r(gen);

                // Create a renamed pattern, and collect all
                // substitutions that occured.
                let mut ps2 = Vec::new();
                let mut subs = Vec::new();
                for p in ps {
                    let (p2, mut ss) = p.rename_r(gen);
                    ps2.push(p2);
                    subs.append(&mut ss);
                }

                let m2 = m
                    // Rename any vars introduced in the sub-comp.
                    .rename_r(gen)
                    // Substitute the replacements into the sub-comp.
                    .substitute_many(&subs);
                Self::BindN(b2, ps2, Box::new(m2))
            }
            Self::Force(v) => Self::Force(v.rename_r(gen)),
            Self::Fun(names, m) => {
                let mut new_m = m.rename_r(gen);
                let mut new_names = Vec::new();
                for (name,t) in names {
                    let new_name = gen.next();
                    new_m = new_m.substitute(&name, &new_name.clone().val());
                    new_names.push((new_name,t));
                }
                Self::Fun(new_names, Box::new(new_m))
            }
            Self::Ite(cond, then_b, else_b) => {
                Self::ite(
                    cond.rename_r(gen),
                    then_b.rename_r(gen),
                    else_b.rename_r(gen),
                )
            }
        }
    }
}

impl Pattern {
    fn rename_r(self, gen: &mut Gen) -> (Self, Vec<(VName,Val)>) {
        match self {
            Self::NoBind => (Self::NoBind, Vec::new()),
            Self::Atom(x) => {
                let y = gen.next();
                (Self::Atom(y.clone()), vec![(x,y.val())])
            }
            Self::Tuple(ps) => {
                let mut ps2 = Vec::new();
                let mut ss = Vec::new();
                for p in ps.into_iter() {
                    let (p2, mut ss_p) = p.rename_r(gen);
                    ps2.push(p2);
                    ss.append(&mut ss_p);
                }
                (Self::Tuple(ps2), ss)
            }
        }
    }
}

impl Val {
    fn rename_r(self, gen: &mut Gen) -> Self {
        match self {
            Self::Literal(l) => Self::Literal(l),
            Self::OpCode(om,oc) => Self::OpCode(om,oc),
            Self::Thunk(m) => Self::Thunk(Box::new(m.rename_r(gen))),
            Self::Tuple(vs) => Self::Tuple(
                vs.into_iter().map(|v| v.rename_r(gen)).collect()
            ),
            // Remember, vars get renamed at their introduction point,
            // not at their use-points.
            Self::Var(n,ts) => Self::Var(n,ts),
        }
    }
}
