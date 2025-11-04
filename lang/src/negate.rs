use crate::{
    Binder1,
    Comp,
    LogOpN,
    neg_normal_form::DemandSet,
    IGen,
    Sig,
};

impl Binder1 {
    pub fn negate(&self, sig: &Sig, dem: &mut DemandSet, igen: &mut IGen) -> Self {
        match self {
            Self::Eq(is_pos, vs1, vs2) =>
                Self::Eq(!is_pos, vs1.clone(), vs2.clone()),
            Self::LogQuantifier(q, xs, m) => {
                let m_neg = m
                    .negate_with(igen)
                    .partial_eval_single_case(sig,igen);
                Self::LogQuantifier(
                    q.invert(),
                    xs.clone(),
                    Box::new(m_neg),
                )
            }
            Self::LogNot(_v) =>
                panic!("Tried to directly negate a LogNot binder."),
            Self::LogOpN(op, vs) => match op {
                LogOpN::And => {
                    let vs_neg =
                        vs.iter().map(|v| v.demand_negative(dem,igen)).collect();
                    Self::LogOpN(LogOpN::Or, vs_neg)
                }
                LogOpN::Or => {
                    let vs_neg =
                        vs.iter().map(|v| v.demand_negative(dem,igen)).collect();
                    Self::LogOpN(LogOpN::And, vs_neg)
                }
                LogOpN::Pred(s,is_neg) =>
                    Self::LogOpN(LogOpN::Pred(s.clone(), !is_neg), vs.clone()),
                // op => todo!("Negation for {:?}", op),
            }
        }
    }
}

impl Comp {
    /// Negate a prop-type Comp.
    pub fn negate(&self) -> Self {
        let mut igen = self.get_igen();
        self.negate_with(&mut igen)
    }
    
    pub fn negate_with(&self, igen: &mut IGen) -> Self {
        let x1 = igen.next();
        let x2 = igen.next();
        // Simply sequence the Comp into a new LogNot node. Later,
        // normalization will eliminate this node by inverting logical
        // operators and quantifiers.
        Self::seq(
            self.clone(),
            x1.clone(),
            Self::not(x1, x2.clone(), Self::return1(x2))
        )
    }
}
