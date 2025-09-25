use crate::{
    Binder1,
    BinderN,
    Comp,
    Pattern,
    Val,
    VName,
};

/// A bit of state used to auto-generate fresh variable names.
#[derive(Copy, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Gen(u32);

impl Gen {
    pub fn next(&mut self) -> VName {
        let n = VName::Auto(self.0);
        self.0 = self.0 + 1;
        n
    }
    pub fn next_many(&mut self, n: usize) -> Vec<VName> {
        let mut names = Vec::with_capacity(n);
        for _ in 0..n {
            names.push(self.next());
        }
        names
    }
    fn advance(&mut self, x: &VName) {
        match x {
            VName::Manual(_s) => {},
            VName::Auto(n) => {
                self.0 = self.0.max(n + 1);
            }
        }
    }
    pub fn new() -> Self {
        Gen(0)
    }
}

impl Binder1 {
    fn advance_gen(&self, gen: &mut Gen) {
        match self {
            Self::Eq(_, vs1, vs2) => {
                for v in vs1 {
                    v.advance_gen(gen);
                }
                for v in vs2 {
                    v.advance_gen(gen);
                }
            }
            Self::LogQuantifier(_q, xs, m) => {
                for (x,_) in xs {
                    gen.advance(x);
                }
                m.advance_gen(gen);
            }
            Self::LogNot(v) => v.advance_gen(gen),
            Self::LogOpN(_op, vs) => {
                for v in vs {
                    v.advance_gen(gen);
                }
            }
        }
    }
}

impl BinderN {
    fn advance_gen(&self, gen: &mut Gen) {
        match self {
            Self::Call(_oc, _vs) => todo!(),
            Self::Seq(m) => {
                m.advance_gen(gen);
            }
        }
    }
}

impl Comp {
    /// Advance the given Gen past any VName appearing in the
    /// computation.
    pub fn advance_gen(&self, gen: &mut Gen) {
        match self {
            Self::Apply(m,_,vs) => {
                m.advance_gen(gen);
                for v in vs {
                    v.advance_gen(gen);
                }
            }
            Self::Bind1(b, x, m) => {
                b.advance_gen(gen);
                gen.advance(&x);
                m.advance_gen(gen);
            }
            Self::BindN(b, ps, m) => {
                b.advance_gen(gen);
                for p in ps {
                    p.advance_gen(gen);
                }
                m.advance_gen(gen);
            }
            Self::Force(v) => {
                v.advance_gen(gen);
            }
            Self::Fun(xs, m) => {
                for (x,_) in xs {
                    gen.advance(x);
                }
                m.advance_gen(gen);
            }
            Self::Ite(cond, then_b, else_b) => {
                cond.advance_gen(gen);
                then_b.advance_gen(gen);
                else_b.advance_gen(gen);
            }
            Self::Match(v, arms) => {
                v.advance_gen(gen);
                for (arm, comp) in arms.iter() {
                    for p in arm.binders.iter() {
                        p.advance_gen(gen);
                    }
                    comp.advance_gen(gen);
                }
            }
            Self::Return(vs) => {
                for v in vs {
                    v.advance_gen(gen);
                }
            }
            // c => todo!("advance_gen {:?}", c),
        }
    }
    /// Returns a Gen that has advanced beyond any VName
    /// appearing in the computation.
    pub fn get_gen(&self) -> Gen {
        let mut gen = Gen::new();
        self.advance_gen(&mut gen);
        gen
    }
}

impl Pattern {
    fn advance_gen(&self, gen: &mut Gen) {
        match self {
            Pattern::NoBind => {}
            Pattern::Atom(x) => {
                gen.advance(x);
            }
            Pattern::Tuple(ps) => {
                for p in ps {
                    p.advance_gen(gen);
                }
            }
        }
    }
}

impl Val {
    fn advance_gen(&self, gen: &mut Gen) {
        match self {
            Val::EnumCon(_, vs) => {
                for v in vs {
                    v.advance_gen(gen);
                }
            }
            Val::Literal(_l) => {},
            Val::OpCode(..) => {},
            Val::Thunk(m) => m.advance_gen(gen),
            Val::Tuple(vs) => {
                for v in vs {
                    v.advance_gen(gen);
                }
            }
            Val::Var(x,_,_) => gen.advance(x),
        }
    }
}
