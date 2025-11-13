use crate::{
    Binder1,
    BinderN,
    Comp,
    Pattern,
    Val,
    Ident,
};

/// A bit of state used to auto-generate fresh variable names.
#[derive(Copy, Debug, Clone, PartialEq, Eq, Hash)]
pub struct IGen(u32);

impl IGen {
    pub fn next(&mut self) -> Ident {
        let n = Ident::Auto(self.0);
        self.0 = self.0 + 1;
        n
    }
    pub fn next_many(&mut self, n: usize) -> Vec<Ident> {
        let mut names = Vec::with_capacity(n);
        for _ in 0..n {
            names.push(self.next());
        }
        names
    }
    fn advance(&mut self, x: &Ident) {
        match x {
            Ident::Manual(_s) => {},
            Ident::Auto(n) => {
                self.0 = self.0.max(n + 1);
            }
        }
    }
    pub fn new() -> Self {
        IGen(0)
    }
}

impl Binder1 {
    fn advance_igen(&self, igen: &mut IGen) {
        match self {
            Self::Eq(_, vs1, vs2) => {
                for v in vs1 {
                    v.advance_igen(igen);
                }
                for v in vs2 {
                    v.advance_igen(igen);
                }
            }
            Self::LogQuantifier(_q, xs, m) => {
                for (x,_) in xs {
                    igen.advance(x);
                }
                m.advance_igen(igen);
            }
            Self::LogNot(v) => v.advance_igen(igen),
            Self::LogOpN(_op, vs) => {
                for v in vs {
                    v.advance_igen(igen);
                }
            }
        }
    }
}

impl BinderN {
    fn advance_igen(&self, igen: &mut IGen) {
        match self {
            Self::Call(_oc, vs) => {
                for v in vs {
                    v.advance_igen(igen);
                }
            }
            Self::Seq(m) => {
                m.advance_igen(igen);
            }
        }
    }
}

impl Comp {
    /// Advance the given IGen past any Ident appearing in the
    /// computation.
    pub fn advance_igen(&self, igen: &mut IGen) {
        match self {
            Self::Apply(m,_,vs) => {
                m.advance_igen(igen);
                for v in vs {
                    v.advance_igen(igen);
                }
            }
            Self::Bind1(b, x, m) => {
                b.advance_igen(igen);
                igen.advance(&x);
                m.advance_igen(igen);
            }
            Self::BindN(b, ps, m) => {
                b.advance_igen(igen);
                for p in ps {
                    p.advance_igen(igen);
                }
                m.advance_igen(igen);
            }
            Self::Force(v) => {
                v.advance_igen(igen);
            }
            Self::Fun(xs, m) => {
                for (x,_) in xs {
                    igen.advance(x);
                }
                m.advance_igen(igen);
            }
            Self::Ite(cond, then_b, else_b) => {
                cond.advance_igen(igen);
                then_b.advance_igen(igen);
                else_b.advance_igen(igen);
            }
            Self::Match(v, arms) => {
                v.advance_igen(igen);
                for (arm, comp) in arms.iter() {
                    for p in arm.binders.iter() {
                        p.advance_igen(igen);
                    }
                    comp.advance_igen(igen);
                }
            }
            Self::Return(vs) => {
                for v in vs {
                    v.advance_igen(igen);
                }
            }
        }
    }
    /// Returns an `IGen` that has advanced beyond any `Ident`
    /// appearing in the computation.
    pub fn get_igen(&self) -> IGen {
        let mut igen = IGen::new();
        self.advance_igen(&mut igen);
        igen
    }
}

impl Pattern {
    fn advance_igen(&self, igen: &mut IGen) {
        match self {
            Pattern::NoBind => {}
            Pattern::Atom(x) => {
                igen.advance(x);
            }
            Pattern::Tuple(ps) => {
                for p in ps {
                    p.advance_igen(igen);
                }
            }
        }
    }
}

impl Val {
    fn advance_igen(&self, igen: &mut IGen) {
        match self {
            Val::Literal(_l) => {},
            Val::OpCode(..) => {},
            Val::Thunk(m) => m.advance_igen(igen),
            Val::Tuple(vs) => {
                for v in vs {
                    v.advance_igen(igen);
                }
            }
            Val::Var(x,_,_,_) => igen.advance(x),
        }
    }
}
