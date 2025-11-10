#[ravencheck::check_module]
#[declare_types(u32)]
pub mod rvn_u32 {
    #[declare]
    pub fn le(x: u32, y: u32) -> bool {
        x <= y
    }

    #[assume]
    fn le_reflexive(x: u32) -> bool {
        le(x,x)
    }

    #[verify]
    fn exists_less_or_eq(x: u32) -> bool {
        exists(|y: u32| le(y,x))
    }

    #[declare]
    pub const ZERO: u32 = 0;

    #[assume]
    fn zero_is_least(x: u32) -> bool {
        le(ZERO, x)
    }

    #[define]
    pub fn ge(a: u32, b: u32) -> bool {
        le(b,a)
    }

    #[verify]
    fn greater_or_eq_to_zero(x: u32) -> bool {
        ge(x, ZERO)
    }

    #[falsify]
    fn less_or_eq_to_zero(x: u32) -> bool {
        le(x, ZERO)
    }
}

#[ravencheck::export_module]
#[declare_types(HashSet<_>)]
pub mod rvn_hashset {
    pub use std::collections::HashSet;
    use std::hash::Hash;

    #[declare]
    pub fn member<T>(elem: &T, set: &HashSet<T>) -> bool
    where T: Eq + Hash
    {
        set.contains(elem)
    }

    #[assume]
    #[inst_for(HashSet<T> => <T>)]
    fn member_defines_eq<T>(s1: HashSet<T>, s2: HashSet<T>) -> bool {
        let some_difference = exists(|e: T| {
            member::<T>(e,s1) != member::<T>(e,s2)
        });

        s1 == s2 || some_difference
    }

    #[declare]
    pub fn insert<T>(elem: T, mut set: HashSet<T>) -> HashSet<T>
    where T: Eq + Hash
    {
        set.insert(elem);
        set
    }

    #[assume(insert::<T>(elem1, set1) => set2)]
    fn insert_def() -> bool {
        forall(|elem2: T| {
            member::<T>(elem2, set2) ==
                (member::<T>(elem2, set1) || elem1 == elem2)
        })
    }
}
