use crate::{
    Binder1,
    Comp,
    Literal,
    Val,
    VName,
    Gen,
    Sig,
};

use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DemandVal {
    Positive,
    Negative(VName),
    Both(VName),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DemandSet(HashMap<VName, DemandVal>);

impl DemandSet {
    pub fn empty() -> Self { DemandSet(HashMap::new()) }
    pub fn get(&self, x: &VName) -> Option<DemandVal> {
        match self.0.get(x) {
            Some(y) => Some(y.clone()),
            None => None,
        }
    }
    pub fn add_positive(&mut self, x: &VName) {
        match self.0.get(x) {
            Some(DemandVal::Both(_y)) => {},
            Some(DemandVal::Positive) => {},
            Some(DemandVal::Negative(y)) => {
                self.0.insert(x.clone(),DemandVal::Both(y.clone()));
            }
            None => {
                self.0.insert(x.clone(),DemandVal::Positive);
            }
        }
    }
    /// First VName arg is the demanded name, second is the what the
    /// negation should be named as.  The returned value is what the
    /// negation has already been named as, if any.
    pub fn add_negative(&mut self, x: &VName, y: &VName) -> VName {
        match self.0.get(x) {
            Some(DemandVal::Both(y2)) => y2.clone(),
            Some(DemandVal::Negative(y2)) => y2.clone(),
            Some(DemandVal::Positive) => {
                self.0.insert(x.clone(),DemandVal::Both(y.clone()));
                y.clone()
            }
            None => {
                self.0.insert(x.clone(),DemandVal::Negative(y.clone()));
                y.clone()
            }
        }
    }
    /// Adds a negative demand for the given VName. If a negative
    /// demand already exists, add return the negative version's
    /// name. If not, generate a unique name for the negative version
    /// and return it.
    pub fn add_negative_gen(&mut self, x: &VName, gen: &mut Gen) -> VName {
        match self.0.get(x) {
            Some(DemandVal::Both(x2)) => x2.clone(),
            Some(DemandVal::Negative(x2)) => x2.clone(),
            Some(DemandVal::Positive) => {
                let x2 = gen.next();
                self.0.insert(x.clone(), DemandVal::Both(x2.clone()));
                x2
            }
            None => {
                let x2 = gen.next();
                self.0.insert(x.clone(), DemandVal::Negative(x2.clone()));
                x2
            }
        }
    }
}

impl Binder1 {
    fn neg_normal_form_r(&self, sig: &Sig, dem: &mut DemandSet, gen: &mut Gen) -> Self {
        match self {
            Self::Eq(pos, vs1, vs2) => {
                for v in vs1 {
                    v.demand_positive(dem);
                }
                for v in vs2 {
                    v.demand_positive(dem);
                }
                Self::Eq(*pos, vs1.clone(), vs2.clone())
            }
            Self::LogQuantifier(q, xs, m) => {
                let m2 = m.neg_normal_form_r(sig, dem, gen);
                Self::LogQuantifier(*q, xs.clone(), Box::new(m2))
            }
            Self::LogOpN(op, vs) => {
                // Demand all of the args
                for v in vs {
                    v.demand_positive(dem);
                }

                // let mut vs2 = Vec::new();
                // for v in vs {
                //     match v {
                //         Val::Var(n) => {
                //             dem.add_positive(n);
                //             vs2.push(Val::Var(n.clone()));
                //         }
                //         Val::Literal(l) => {
                //             vs2.push(Val::Literal(l.clone()));
                //         },
                //         // I'm worried about the demand-set here, but
                //         // normalization itself for the body of a
                //         // thunk is not necessary, since it will be
                //         // normalized later when it is forced.
                //         //
                //         // Val::Thunk(m) => {
                //         //     let v2 = Val::Thunk(Box::new(
                //         //         m.neg_normal_form_r(dem,gen)
                //         //     ));
                //         //     vs2.push(v2);
                //         // }
                //         Val::Thunk(m) => {
                //             vs2.push(Val::Thunk(m.clone()));
                //         }
                //     }
                // }
                Self::LogOpN(op.clone(), vs.clone())
            }
            _ => todo!("neg_normal_form_r for {:?}", self),
        }
    }    
}

impl Comp {
    /// Convert a computation into normal form.  This may require the
    /// creation of new variables, so we require a Gen.
    pub fn neg_normal_form(self, sig: &Sig, gen: &mut Gen) -> Self {
        self.neg_normal_form_r(sig, &mut DemandSet::empty(), gen)
    }

    fn neg_normal_form_r(&self, sig: &Sig, dem: &mut DemandSet, gen: &mut Gen) -> Self {
        match self {
            Self::Return(vs) => {
                for v in vs {
                    match v {
                        Val::Var(x,_) => { dem.add_positive(x); }
                        _ => {},
                    }
                }
                Self::Return(vs.clone())
            }
            Self::Bind1(Binder1::LogNot(v), x, m) => {
                let m2 = m.neg_normal_form_r(sig,dem,gen);
                match dem.get(x) {
                    None => m2,
                    Some(DemandVal::Positive) => {
                        // Get the negative version of the value,
                        // recording a negative demand if it's a
                        // variable.
                        let v_neg = v.demand_negative(dem,gen);
                        // Replace x's with the negative value.
                        m2.substitute(x, &v_neg)
                    }
                    Some(DemandVal::Negative(y1)) => {
                        // Record a positive demand for the value (if
                        // it's a variable).
                        v.demand_positive(dem);
                        // Replace y1's with the (positive) value. The
                        // positive x (negative value) is not
                        // demanded, so there are no x's in m2 to
                        // replace with anything.
                        m2.substitute(&y1, v)
                    }
                    Some(DemandVal::Both(y1)) => {
                        v.demand_positive(dem);
                        let v_neg = v.demand_negative(dem,gen);
                        m2
                            .substitute(&y1,v)
                            .substitute(x,&v_neg)
                    }
                }
            }
            Self::Bind1(b, x, m) => {
                let m2 = m.neg_normal_form_r(sig,dem,gen);
                match dem.get(x) {
                    None => {
                        // println!("{:?} was not demanded by {:?}", x, m2);
                        m2
                    }
                    Some(DemandVal::Positive) => {
                        let b2p = b.neg_normal_form_r(sig,dem,gen);
                        Self::Bind1(b2p, x.clone(), Box::new(m2))
                    }
                    Some(DemandVal::Negative(y)) => {
                        let b2n = b.negate(sig,dem,gen).neg_normal_form_r(sig,dem,gen);
                        Self::Bind1(b2n, y.clone(), Box::new(m2))
                    }
                    Some(DemandVal::Both(y)) => {
                        let b2p = b.neg_normal_form_r(sig,dem,gen);
                        let b2n = b.negate(sig,dem,gen).neg_normal_form_r(sig,dem,gen);
                        Self::Bind1(b2p, x.clone(), Box::new(
                            Self::Bind1(b2n, y.clone(), Box::new(m2))
                        ))
                    }
                }
            }
            Self::BindN(b, ps, m) => {
                Self::BindN(
                    b.clone(),
                    ps.clone(),
                    Box::new(m.neg_normal_form_r(sig,dem,gen)),
                )
            }
            Self::Ite(cond, then_b, else_b) => {
                cond.demand_positive(dem);
                Self::ite(
                    cond.clone(),
                    then_b.neg_normal_form_r(sig,dem,gen),
                    else_b.neg_normal_form_r(sig,dem,gen),
                )
            }
            Self::Apply(_m, _targs, _vs) => {
                panic!(
                    "Apply should be gone before neg_normal_form_r: {:?}",
                    self,
                )
            }
            _ => todo!("neg_normal_form_r for {:?}", self),
        }
    }
}

impl Val {
    /// Record positive demand if the value is a Var. Note that
    /// nothing gets demanded inside of Thunks.
    pub fn demand_positive(&self, dem: &mut DemandSet) {
        match self {
            Self::Var(x, _) => {
                dem.add_positive(x);
            }
            Self::Tuple(vs) => {
                for v in vs {
                    v.demand_positive(dem);
                }
            }
            _ => {},
        }
    }
    /// Generate the negation of the value, recording a negative
    /// demand if it's a Var.
    pub fn demand_negative(
        &self,
        dem: &mut DemandSet,
        gen: &mut Gen
    ) -> Self {
        match self {
            Self::Var(x, types) => {
                let x2 = dem.add_negative_gen(&x,gen);
                Self::Var(x2, types.clone())
            }
            Self::Literal(Literal::LogTrue) =>
                Self::Literal(Literal::LogFalse),
            Self::Literal(Literal::LogFalse) =>
                Self::Literal(Literal::LogTrue),
            _ => panic!("Can't demand (negative) non-prop value {:?}", self),
        }
    }
}
