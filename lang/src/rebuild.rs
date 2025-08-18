use crate::{
    Binder1,
    BinderN,
    Comp,
    LogOpN,
    Pattern,
    Quantifier,
    SName,
    Val,
    VName,
    VType,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Rebuild {
    Call(SName, Vec<Val>, Vec<Pattern>),
    Eq(bool, Vec<Val>, Vec<Val>, VName),
    Quantifier(Quantifier, Vec<(VName,VType)>, Comp, VName),
    Not(Val, VName),
    LogOpN(LogOpN, Vec<Val>, VName),
    Bind1(Binder1, VName),
}

impl Comp {
    pub fn rebuild(self, rb: Rebuild) -> Comp {
        match rb {
            Rebuild::Bind1(b,x) => {
                Self::Bind1(b, x, Box::new(self))
            }
            Rebuild::Call(s,vs,ps) => {
                Self::BindN(
                    BinderN::Call(s,vs),
                    ps,
                    Box::new(self)
                )
            }
            Rebuild::Eq(pos, vs1, vs2, x) => {
                Self::eq_ne(
                    pos,
                    vs1,
                    vs2,
                    x,
                    self
                )
            }
            Rebuild::Quantifier(q,ps,body,x) => {
                Self::quant_many(q,ps,body,x,self)
            }
            Rebuild::Not(v,x) => {
                Self::Bind1(Binder1::LogNot(v), x, Box::new(self))
            }
            Rebuild::LogOpN(op, vs, x) => {
                Self::Bind1(
                    Binder1::LogOpN(op, vs),
                    x,
                    Box::new(self),
                )
            }
        }
    }
    pub fn rebuild_from_stack(mut self, mut anti_stack: Vec<Rebuild>) -> Self {
        anti_stack.reverse();
        for rb in anti_stack {
            self = self.rebuild(rb);
        }
        self
    }
}
