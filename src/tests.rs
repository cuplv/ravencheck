#[crate::check_module(crate)]
#[rvn_should_panic("Op 'x' is undefined")]
mod polymorphic_no_inst_rules {
    #[assume]
    fn foo<T>(a: T) -> bool { a == x }
}

#[crate::check_module(crate)]
#[rvn_should_panic("polymorphic, but has no instantiation rules.")]
mod polymorphic_with_inst_rules {
    #[assume]
    fn foo<T>(a: T) -> bool { a == a }
}

#[crate::export_module(crate)]
#[rvn_should_panic("polymorphic, but has no instantiation rules.")]
#[declare_types(HashSet<_>)]
#[allow(unused_imports)]
mod no_inst_export {
    use std::collections::HashSet;
    use std::hash::Hash;

    #[declare]
    #[phantom]
    pub fn member<T>(e: &T, s: &HashSet<T>) -> bool
    where T: Eq + Hash
    {
        s.contains(e)
    }

    #[assume]
    fn distinguisher<T>(s1: HashSet<T>, s2: HashSet<T>) -> bool {
        s1 == s2 || exists(|e: T| {
            member::<T>(e,s1) != member::<T>(e,s2)
        })
    }
}

#[crate::check_module(crate)]
#[rvn_should_panic("polymorphic, but has no instantiation rules.")]
mod no_inst_import {
    #[import]
    #[allow(unused_imports)]
    use crate::tests::no_inst_export::*;

    #[verify]
    fn my_prop<T>(s: HashSet<T>) -> bool {
        s == s
    }
}
