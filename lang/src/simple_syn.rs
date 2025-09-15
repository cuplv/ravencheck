use syn::{
    Block,
    Ident,
    ItemFn,
    PatType,
    Type,
};

use crate::VType;

type Error = String;

pub struct SimpleFn {
    pub name: Ident,
    pub tas: Vec<Ident>,
    pub inputs: Vec<PatType>,
    pub output: Type,
    pub block: Block,
}

impl SimpleFn {
    pub fn from_syn(item: ItemFn) -> Result<Self, Error> {
        todo!()
    }
}
