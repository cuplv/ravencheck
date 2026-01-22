use crate::{
    Binder1,
    BinderN,
    Call,
    Comp,
    LogOp1,
    LogOpN,
    Pattern,
    Quantifier,
    Val,
    Ident,
    VType,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Rebuild {
    Call(Call, Vec<Pattern>),
    Eq(bool, Vec<Val>, Vec<Val>, Ident),
    QMode(Quantifier, Comp, Ident),
    Quantifier(Quantifier, Vec<(Ident,VType)>, Comp, Ident),
    LogOp1(LogOp1, Val, Ident),
    LogOpN(LogOpN, Vec<Val>, Ident),
    Bind1(Binder1, Ident),
}

impl Comp {
    pub fn rebuild(self, rb: Rebuild) -> Comp {
        match rb {
            Rebuild::Bind1(b,x) => {
                Self::Bind1(b, x, Box::new(self))
            }
            Rebuild::Call(c,ps) => {
                Self::BindN(
                    BinderN::Call(c),
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
            Rebuild::QMode(q,body,x) => {
                Self::Bind1(
                    Binder1::QMode(q,Box::new(body)),
                    x,
                    Box::new(self)
                )
            }
            Rebuild::Quantifier(q,ps,body,x) => {
                Self::quant_many(q,ps,body,x,self)
            }
            Rebuild::LogOp1(b,v,x) => {
                Self::Bind1(Binder1::LogOp1(b,v), x, Box::new(self))
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
