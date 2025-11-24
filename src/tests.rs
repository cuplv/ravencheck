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

#[crate::export_module(crate)]
#[declare_types(HashSet<_>)]
pub mod my_set {
    pub use std::collections::HashSet;
    use std::hash::Hash;

    #[declare]
    pub fn member<T>(e: &T, s: &HashSet<T>) -> bool
    where T: Eq + Hash
    {
        s.contains(e)
    }

    #[assume]
    #[for_type(HashSet<T> => <T>)]
    fn distinguisher<T>(s1: HashSet<T>, s2: HashSet<T>) -> bool {
        s1 == s2 || exists(|e: T| {
            member::<T>(e,s1) != member::<T>(e,s2)
        })
    }
}

pub use my_set as my_set_by_other_name;

#[crate::export_module(crate)]
#[allow(dead_code)]
pub mod my_set_client1 {
    #[import]
    use crate::tests::my_set::*;
    use std::hash::Hash;

    #[define]
    pub fn bi_member<T>(e1: &T, e2: &T, s: &HashSet<T>) -> bool
    where T: Eq + Hash
    {
        member::<T>(e1, s)
            && member::<T>(e2, s)
    }
}

#[crate::export_module(crate)]
#[allow(dead_code)]
pub mod my_set_client2 {
    #[import]
    use crate::tests::my_set_by_other_name::*;
    use std::hash::Hash;

    #[define]
    pub fn tri_member<T>(e1: &T, e2: &T, e3: &T, s: &HashSet<T>) -> bool
    where T: Eq + Hash
    {
        member::<T>(e1, s)
            && member::<T>(e2, s)
            && member::<T>(e3, s)
    }
}

/// This module imports my_set twice, once transitively through
/// my_set_client1 and once through my_set_client2. However, imports
/// are idempotent, and every item in in my_set is only
/// declared/defined once. This is true despite the fact that my_set
/// is imported under two different names between client1 and client2.
#[crate::check_module(crate)]
#[allow(unused_imports)]
mod my_set_client3 {
    #[import]
    use crate::tests::my_set_client1::*;
    #[import]
    use crate::tests::my_set_client2::*;

    #[verify]
    fn five_member<T>(e1: T, e2: T, e3: T, e4: T, e5: T, s: HashSet<T>) -> bool {
        (bi_member::<T>(e1, e2, s) && tri_member::<T>(e3, e4, e5, s))
            == (tri_member::<T>(e1, e2, e3, s) && bi_member::<T>(e4, e5, s))
    }
}

/// In this module, my_set is imported three times. Again, only the
/// first import of my_set has the effect of defining/declaring its
/// items.
#[crate::check_module(crate)]
#[allow(unused_imports)]
mod my_set_client4 {
    #[import]
    use crate::tests::my_set::*;
    #[import]
    use crate::tests::my_set_client1::*;
    #[import]
    use crate::tests::my_set_client2::*;

    #[verify]
    fn five_member<T>(e1: T, e2: T, e3: T, e4: T, e5: T, s: HashSet<T>) -> bool {
        (bi_member::<T>(e1, e2, s) && tri_member::<T>(e3, e4, e5, s))
            == (tri_member::<T>(e1, e2, e3, s) && bi_member::<T>(e4, e5, s))
    }
}

/// In this module, my_set is imported twice. In addition, this module
/// directly declares `HashSet` in addition to declaring through those
/// imports. In this case, an error *is* thrown: the `declare_types`
/// attribute does not ensure idempotence in the same way that imports
/// do.
#[crate::check_module(crate)]
#[declare_types(HashSet<_>)]
#[rvn_should_panic("You tried to define type HashSet, but it was already defined")]
#[allow(unused_imports)]
mod my_set_client5 {
    #[import]
    use crate::tests::my_set_client1::*;
    use crate::tests::my_set_client2::*;

    #[verify]
    fn five_member<T>(e1: T, e2: T, e3: T, e4: T, e5: T, s: HashSet<T>) -> bool {
        (bi_member(e1, e2, s) && tri_member(e3, e4, e5, s))
            == (tri_member(e1, e2, e3, s) && bi_member(e4, e5, s))
    }
}
