// Calling declared/uninterpreted functions under existential
// operators is tricky.  If one of the existentially quantified types
// is also output by the function, we have a self-loop sort-cycle.
//
// For example, this #[verify] property will fail, since it can't be
// decidably queried.
#[ravencheck::check_module]
#[allow(unused_imports)]
// For testing, you can write ravencheck modules that *should* panic
// with a particular error message by using the following attribute.
#[rvn_should_panic("sort cycle?")]
mod call_creates_cycles {
    #[import]
    // You can find this mod at the bottom of this file.
    use crate::def_and_eq::my_u32::*;

    #[verify]
    pub fn prop_that_fails_to_compile() -> bool {
        // A u32 is existentially quantified, and the double function
        // call also outputs a u32: sort-cycle!
        exists(|x: u32| {
            double(ZERO) == ZERO
        })
    }
}

// The best way to avoid this cycle will depend on the overall
// context. But here are some strategies.
#[ravencheck::check_module]
#[allow(unused_imports)]
mod avoiding_cycles {
    #[import]
    use crate::def_and_eq::my_u32::*;

    // The simplest fix is to move the function call out of the
    // existential. In this case, we can do so because the quantified
    // 'x' is not an input to the function.
    #[verify]
    pub fn moving_the_function_call() -> bool {
        let double_zero = double(ZERO);
        exists(|x: u32| {
            double_zero == ZERO
        })
    }

    // If you can't move the function call---maybe because an
    // existentially-quantified value is one of the call's
    // inputs---then you can use the 'def_and_eq' operator to assert
    // that some value is equal to the output of the function, without
    // actually demanding that the function be called.  Since the
    // function is not actually called, it creates no sort edge.
    //
    // In this condition, 'def_and_eq' is used to assert that (1)
    // double(ZERO) has a defined output, and (2) that the output is
    // equal to ZERO.
    //
    // Unfortunately, this assertion is falsifiable, because the
    // solver is not convinced that the first assertion is true: we
    // never actually call 'double', and so the solver does not know
    // that 'double(ZERO)' must have a defined output.
    #[falsify]
    pub fn removing_the_function_call() -> bool {
        exists(|x: u32| {
            def_and_eq(double(ZERO), ZERO)
        })
    }

    // We can fix verification by instantiating 'double' for ZERO.
    // The usual way to do this is to call the function for the
    // relevant input.
    //
    // The result looks similar to 'moving_the_function_call()' above,
    // but we don't need to name and explicitly reference the output
    // of double(ZERO). Our call tells the solver that (1) the output
    // is defined, and it infers from the 'double_zero' axiom that (2)
    // the defined output must be equal to ZERO.
    #[verify]
    pub fn instantiating_by_call() -> bool {
        let _ = double(ZERO);
        exists(|x: u32| {
            def_and_eq(double(ZERO), ZERO)
        })
    }

    // Alternatively, we can fix verification by *assuming* that
    // 'double(ZERO)' is defined, again without actually calling the
    // function.
    //
    // Here, by *assuming* 'def_and_eq(double(ZERO), a)' for some u32
    // 'a', we are telling the solver to assume (1) that double(ZERO)
    // has a defined output, and (2) that the output is equal to 'a'.
    //
    // The first assumption then allows us to verify the condition
    // just like actually calling 'double(ZERO)' helped us in the
    // last example.
    //
    // This strategy is more verbose than simply calling the function,
    // but could be useful in cases where there is absolutely nowhere
    // that the function call can be safely moved to.
    #[verify]
    pub fn instantiating_by_assumption() -> bool {
        forall(|a: u32| {
            implies(
                def_and_eq(double(ZERO), a),
                exists(|x: u32| {
                    def_and_eq(double(ZERO), ZERO)
                })
            )
        })
    }

    // def_and_eq can also be used for calls to enum constructors, and
    // supports polymorphic functions.
    //
    // Just remember that the left argument to def_and_eq must always
    // be (syntactically) a call to an uninterpreted function
    // (declared function, recursive function, or enum constructor).
    //
    // The right argument can be any expression.
    #[verify]
    pub fn def_and_eq_constructor(a: u32) -> bool {
        let l1 = MyList::<u32>::Cons(a, MyList::<u32>::Nil);
        exists(|x: u32| {
            def_and_eq(
                MyList::<u32>::Cons(x, MyList::<u32>::Nil),
                l1,
            )
        })
    }
}

#[ravencheck::export_module]
#[declare_types(u32)]
#[allow(dead_code)]
mod my_u32 {
    #[declare]
    pub const ZERO: u32 = 0;

    #[declare]
    pub fn double(u: u32) -> u32 {
        u + u
    }

    #[assume]
    fn double_zero() -> bool {
        double(ZERO) == ZERO
    }

    #[define]
    enum MyList<A> {
        Nil,
        Cons(A, Box<MyList<A>>),
    }
}
