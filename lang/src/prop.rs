use crate::{
    CaseName,
    Comp,
    CType,
    IGen,
    Sig,
};

use std::fmt;

/// The Comp cases in a Prop are normal-form and prop-type.
pub struct Prop {
    pub cases: Vec<(CaseName, Comp)>,
    pub single_case: Comp,
    igen: IGen,
}

pub enum Error {
    Parse(syn::Error),
    Type(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Parse(e) =>
                write!(f, "parse error: {}", e),
            Error::Type(s) =>
                write!(f, "type error: {}", s),
        }
    }
}

pub type Result<A> = std::result::Result<A, Error>;

impl Prop {
    pub fn negate(&mut self, sig: &Sig) {
        for (_,c) in self.cases.iter_mut() {
            *c = c.negate().normal_form_single_case(sig, &mut self.igen);
        }
        self.single_case = self.single_case.negate().normal_form_single_case(sig, &mut self.igen);
    }

    pub fn is_single_case(&self) -> bool {
        self.cases.len() == 1
    }
}

impl Comp {
    pub fn as_prop(mut self, sig: &Sig) -> Result<Prop> {
        self = self.expand_types(&sig.type_aliases());
        match self.type_check(&CType::return_prop(), sig) {
            Ok(()) => {
                let mut igen = self.get_igen();
                let cases = self.clone().normal_form_x(
                    sig,
                    &mut igen,
                    CaseName::root(),
                    true,
                );
                let single_case = self.clone().normal_form_x(
                    sig,
                    &mut igen,
                    CaseName::root(),
                    false,
                ).pop().unwrap().1;
                Ok(Prop{cases, single_case, igen})
            }
            Err(e) => Err(Error::Type(e)),
        }
    }
}
