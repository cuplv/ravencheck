use crate::{
    CaseName,
    Comp,
    CType,
    Gen,
    parse_str_cbpv,
    Sig,
};

use std::fmt;

/// The Comp cases in a Prop are normal-form and prop-type.
pub struct Prop {
    pub cases: Vec<(CaseName, Comp)>,
    vgen: Gen,
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
    pub fn parse(input: &str, sig: &Sig) -> Result<Self> {
        match parse_str_cbpv(input) {
            Ok(c) => c.as_prop(sig),
            Err(e) => Err(Error::Parse(e)),
        }
    }

    pub fn negate(&mut self, sig: &Sig) {
        for (_,c) in self.cases.iter_mut() {
            *c = c.negate().normal_form_single_case(sig, &mut self.vgen);
        }
    }

    pub fn is_single_case(&self) -> bool {
        self.cases.len() == 1
    }
}

impl Comp {
    pub fn as_prop(mut self, sig: &Sig) -> Result<Prop> {
        self = self.expand_types(&sig.type_aliases);
        match self.type_check(&CType::return_prop(), sig) {
            Ok(()) => {
                let mut vgen = self.get_gen();
                let cases = self.normal_form_x(
                    sig,
                    &mut vgen,
                    CaseName::root()
                );
                Ok(Prop{cases, vgen})
            }
            Err(e) => Err(Error::Type(e)),
        }
    }
}
