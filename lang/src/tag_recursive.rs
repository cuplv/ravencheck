use crate::{
    Builder,
    Binder1,
    BinderN,
    Comp,
    IGen,
    LogOpN,
    OpCode,
    Sig,
};

use std::collections::HashSet;

type Recs = HashSet<OpCode>;

impl Binder1 {
    pub fn tag_recursive(
        self, sig: &Sig,
        igen: &mut IGen,
        recs: &Recs
    ) -> Self {
        match self {
            Self::LogQuantifier(q, xs, m) => Self::LogQuantifier(
                q, xs, Box::new(m.tag_recursive(sig,igen, recs))
            ),
            b => b,
        }
    }
}

impl Builder {
    pub fn guard_recursive(self) -> Builder {
        self
            .or(
                OpCode::special_recursive()
                    .as_zero_arg_as_const()
                    .ret()
                    .builder()
                    .not()
            )
    }    
}

impl Comp {
    pub fn tag_recursive(
        self,
        sig: &Sig,
        igen: &mut IGen,
        recs: &Recs,
    ) -> Self {
        match self {
            Self::Bind1(b, x, m) => {
                let rest = Self::Bind1(
                    b.clone().tag_recursive(sig, igen, recs),
                    x,
                    Box::new(m.tag_recursive(sig,igen, recs)),
                );
                match b {
                    Binder1::LogOpN(LogOpN::Pred(code,_),_) if recs.contains(&code) => {
                        rest
                            .builder()
                            .guard_recursive()
                            .build_with(igen)
                            .partial_eval_single_case(sig, igen)
                    }
                    _ => rest,
                }
            }
            Self::BindN(b, ps, m) => {
                let rest = Self::BindN(
                    b.clone(),
                    ps,
                    Box::new(m.tag_recursive(sig, igen, recs)),
                );
                match b {
                    BinderN::Call(call) if recs.contains(&call.code) => {
                        // We have encountered a recursive call, so the
                        // remainder of this condition should be implied
                        // by the recursive flag.
                        rest
                            .builder()
                            .guard_recursive()
                            .build_with(igen)
                            .partial_eval_single_case(sig, igen)
                    }
                    _ => rest,
                }
            }
            Self::Ite(cond, then_b, else_b) => Self::Ite(
                cond,
                Box::new(then_b.tag_recursive(sig, igen, recs)),
                Box::new(else_b.tag_recursive(sig, igen, recs)),
            ),
            Self::Match(target, arms) => Self::Match(
                target,
                arms
                    .into_iter()
                    .map(|(arm, comp)| {
                        (arm, Box::new(comp.tag_recursive(sig, igen, recs)))
                    })
                    .collect(),
            ),
            Self::Return(vs) => Self::Return(vs),
            m => todo!("tag_recursive for {:?}", m),
        }
    }
}
