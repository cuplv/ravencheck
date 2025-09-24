#[crate::check_module(crate)]
#[declare_types(u32)]
#[allow(dead_code)]
mod my_mod {
    #[declare]
    const ZERO: u32 = 0;

    /// We can't use numeric operators (<=, >, +, etc) in code that
    /// the solver sees, so we declare these functions to stand in for
    /// them.
    #[declare]
    fn le(a: u32, b: u32) -> bool {
        a <= b
    }

    #[define]
    fn lt(a: u32, b: u32) -> bool
    {
        le(a,b) && a != b
    }

    #[define]
    fn ge(a: u32, b: u32) -> bool
    {
        le(b,a)
    }

    #[define]
    fn gt(a: u32, b: u32) -> bool
    {
        ge(a,b) && a != b
    }

    /// The 'dec' function subtracts one from a u32, or returns ZERO
    /// if the argument was already ZERO.
    ///
    /// 'inc' and 'dec' form the basic interface to u32 that we will
    /// use to write functions over u32 that the solver understands.
    #[declare]
    fn dec(a: u32) -> u32 {
        if a == 0 {
            0
        } else {
            a - 1
        }
    }

    /// The 'inc' function adds one to a u32.
    #[declare]
    fn inc(a: u32) -> u32 {
        a + 1
    }

    // This axiom over inc and dec is what allows us to verify the
    // add_zeros annotation later.
    #[assume]
    fn inc_dec() -> bool {
        forall(|a: u32| {
            implies(
                a != ZERO,
                inc(dec(a)) == a
            )
        })
    }

    /// 'add' is a recursively-defined function that the solver
    /// understands. The solver can use the function body to
    /// inductively verify annotations on 'add'.
    ///
    /// When 'add' is used in other verification conditions, the
    /// solver will treat it as uninterpreted and assume
    /// previously-verified annotations as axioms.
    #[define]
    #[recursive]
    fn add(a: u32, b: u32) -> u32
    {
        if a == ZERO {
            b
        } else {
            inc(
                add(dec(a), b)
            )
        }
    }

    // This annotation is verified with respect to the function body
    // of 'add'.
    #[annotate(add(a,b) => c)]
    fn add_zeros() -> bool {
        implies(a == ZERO, b == c)
        && implies(b == ZERO, a == c)
    }

    // This condition can be verified only because we have declared
    // the 'add_zeros' annotation above.
    #[verify]
    fn simple_zeros() -> bool {
        add(ZERO, ZERO) == ZERO
    }

    // The following annotation does not verify under the current
    // assumptions. What axioms on 'ZERO' and 'le' are needed to fix
    // it?

    // #[annotate(add)]
    // fn add_monotonic() -> bool {
    //     |a: u32, b: u32|
    //     |c: u32|
    //     le(a,c) && le(a,b)
    // }
}
