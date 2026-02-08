#[ravencheck::module]
// Make the `u32` type visible to Ravencheck
// as an uninterpreted sort.
#[declare_types(u32)]
#[allow(dead_code)]
pub mod rvn_u32 {
    // Make a constant `ZERO` visible to Ravencheck.
    // Ravencheck doesn't see the right-hand side
    // of the `=`.
    #[declare]
    pub const ZERO: u32 = 0;

    // Ravencheck only sees the signature of this function,
    // so the body can contain arbitrary code.
    #[declare]
    pub fn less_or_eq(a: u32, b: u32) -> bool {
        a <= b
    }

    // Because we use #[define] here,
    // Ravencheck sees both the signature and the body.
    // This means that the body cannot include mutable assignments,
    // method calls, or any functions/constants/types
    // that have not already been made visible to Ravencheck.
    // Operators are restricted to `!`, `==`, `!=`, `&&`, and `||`.
    #[define]
    pub fn less_than(a: u32, b: u32) -> bool {
        less_or_eq(a,b) && a != b
    }

    // Assume the anti-symmetric property for `less_or_eq`.
    // This definition only exists at verification time,
    // so we can use Ravencheck-only operators like `forall`.
    //
    // Because we used #[define] to introduce `less_or_eq`,
    // Ravencheck knows nothing about its behavior
    // except what we tell it with #[assume].
    #[assume]
    fn le_anti_symmetric() -> bool {
        forall(|x: u32, y: u32| {
            implies(
                less_or_eq(x,y) && less_or_eq(y,x),
                x == y
            )
        })
    }

    // We can also universally quantify `x` by taking it as an
    // argument to the function.
    #[assume]
    fn le_reflexive(x: u32) -> bool { less_or_eq(x,x) }

    // Assume that `ZERO` is less than or equal to every `u32`.
    #[assume]
    fn zero_is_least() -> bool {
        forall(|x: u32| less_or_eq(ZERO, x))
    }

    // Check that no `u32` is less than `ZERO`.
    // The `x` argument to the function is universally quantified.
    // We can also explicitly quantify it using `forall`,
    // like in the #[assume] conditions.
    #[verify]
    fn zero_is_smallest(x: u32) -> bool {
        !(less_than(x, ZERO))
    }
}

#[ravencheck::module]
pub mod import_example {
    // Here, `#[import]` makes all the #[declare], #[define] and
    // #[assume] items from the `rvn_u32` module visible to Ravencheck
    // in this module as well.
    #[import]
    use crate::doc_examples::rvn_u32::*;

    /// `in_range(a,b,c)` is true when `c` is greater than or equal to
    /// `a` and less than `b`.
    #[define]
    pub fn in_range(lower: u32, upper: u32, x: u32) -> bool {
        less_or_eq(lower, x)
            && less_than(x, upper)
    }

    // Check that if the lower bound is smaller than the upper bound,
    // then at least one `u32` is in the range.
    #[verify]
    pub fn range_not_empty(lower: u32, upper: u32) -> bool {
        implies(
            less_than(lower, upper),
            exists(|x: u32| in_range(lower, upper, x))
        )
    }
}

#[ravencheck::module]
#[declare_types(u16)]
#[rvn_should_panic("> Cannot check 'prop1': sort cycle ⤷ u16 → u32 ⤴ in case root")]
#[allow(dead_code)]
mod sort_cycle {
    #[import]
    use crate::doc_examples::rvn_u32::*;
    #[declare]
    fn u16_to_u32(x: u16) -> u32 { x.into() }
    #[declare]
    fn le_cross_type(x: u16, y: u32) -> bool {
        less_or_eq(u16_to_u32(x), y)
    }
    #[verify]
    pub fn prop1() -> bool {
        exists(|x: u16| less_than(ZERO, u16_to_u32(x)))
            && exists(|x: u32| {
                forall(|y: u16| {
                    le_cross_type(y,x)
                })
            })
    }
}

#[ravencheck::module]
#[declare_types(u32)]
#[allow(dead_code)]
mod incomplete {
    #[define]
    type Nat = u32;

    #[declare]
    pub fn add(a: Nat, b: Nat) -> Nat {
        a + b
    }
    #[declare]
    pub fn less_or_eq(a: Nat, b: Nat) -> bool {
        a <= b
    }

    #[assume]
    fn add_left(a: Nat, b: Nat) -> bool {
        less_or_eq(a, add(a,b))
    }
    
    #[assume]
    fn add_commute(a: Nat, b: Nat) -> bool {
        add(a,b) == add(b,a)
    }
    
    #[falsify]
    fn add_right1(a: Nat, b: Nat) -> bool {
        less_or_eq(b, add(a,b))
    }
    #[verify]
    fn add_right2(a: Nat, b: Nat) -> bool {
        let _ = add(b,a);
        less_or_eq(b, add(a,b))
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
    #[for_type(HashSet<T> => <T>)]
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
