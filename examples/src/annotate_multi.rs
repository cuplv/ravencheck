#[ravencheck::check_module]
#[allow(dead_code)]
mod rvn {
    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    enum Nat {
        // The zero variant
        Z,
        // The successor variant. The sub-value needs to go inside a
        // Box (i.e. needs to get heap-allocated) so that Nat has a
        // fixed byte-size, which is a requirement for all types in
        // Rust.
        //
        // You unbox a value `n: Box<Nat>` using `*n`.
        //
        // You re-box a value `n: Nat` using `Box::new(n)`.
        S(Box<Nat>)
    }

    impl Nat {
        // This is a convenience function for the Rust tests at the
        // bottom of this file. We don't declare it to Ravencheck.
        fn from_usize(n: usize) -> Self {
            if n == 0 {
                Self::Z
            } else {
                Self::S(Box::new(Self::from_usize(n - 1)))
            }
        }
    }

    /// A trivial function that pattern-matches a Nat to the bottom
    /// `Z` value, and then returns `Z`.
    #[define]
    #[recursive]
    fn get_zero(a: Nat) -> Nat {
        match a {
            Nat::Z => Nat::Z,
            // Note that `a_minus` must be unboxed (*) before passing
            // it to `get_zero`.
            Nat::S(a_minus) => get_zero(*a_minus),
        }
    }

    // This is equivalent to the following #[annotate(..)] condition.
    #[annotate_multi]
    #[for_values(a: Nat)]
    #[for_call(get_zero(a) => z)]
    fn always_zero1() -> bool {
        z == Nat::Z
    }

    #[annotate(get_zero(a) => z)]
    fn always_zero2() -> bool {
        z == Nat::Z
    }

    #[define]
    #[recursive]
    fn add(a: Nat, b: Nat) -> Nat {
        match a {
            Nat::Z => b,
            Nat::S(a_minus) =>
                // We unbox `a_minus` before calling `add`, and then
                // re-box the output of `add` so that we can wrap it
                // in Nat::S.
                Nat::S(Box::new(add(*a_minus,b))),
        }
    }

    // The following 'add_commutativity' property for 'add' does not
    // directly verify, but the same property for 'add_alt' does
    // directly verify.
    //
    //     add(a,b) == add(b,a)
    //
    // We need to do some preliminary work to verify the unmodified
    // 'add'.


    // First, we need two lemmas. We'll just assume these for now, but
    // we should ultimately verify them.
    //
    // First, assume that you can commute an S from one argument to
    // the other, without moving the arguments themselves:
    //
    //     add(a, S(b)) == add(S(a), b)
    //
    #[assume]
    fn add_commute_s() -> bool {
        forall(|a: Nat, b: Nat| {
            add(a, Nat::S(b))
                == add(Nat::S(a), b)
        })
    }

    // Then, assume that adding a Z on the right produces the left
    // argument unchanged. We only need this for the right
    // side. Because the definition of 'add' pattern-matches the left
    // argument, it's "immediately obvious" from the 'add' definition
    // that Z on the right produces the left argument.
    //
    //     add(a, Z) == a
    #[assume]
    fn add_z_right() -> bool {
        forall(|a: Nat| {
            add(a, Nat::Z) == a
        })
    }

    // Now we can verify add_commutative. But to do so, we need to add
    // a "quantifier instantiation".
    //
    // In the inductive verification condition, the calls to both
    // add(a,b) and add(b,a) are unrolled by one step.
    //
    // When a=Z, and b=S(b_minus), this unrolling produces the
    // verification condition:
    //
    //     b == S(add(b_minus, Z))
    //
    // Our 'add_z_right' assumption takes care of that! It allows the
    // solver to tranform the condition to:
    //
    //     b == S(b_minus)
    //
    // and we know that's true by construction. When b=Z, we get the
    // same thing but flipped, which 'add_z_right' can equally take
    // care of.
    //
    // The tricky case is a=S(a_minus) and b=S(b_minus), which after
    // unrolling gives us the condition:
    //
    //     S(add(a_minus, S(b_minus))) ==
    //     S(add(b_minus, S(a_minus)))
    //
    // If we were writing a manual proof, we could solve this in two
    // steps. First, apply our assumed 'add_commute_s' rule to move
    // the S:
    //
    //     S(add(a_minus,    S(b_minus))) ==
    //     S(add(S(b_minus), a_minus   ))
    //
    // Second, apply our add_commutative assumption, which is valid
    // for both adds since each has a structurally-smaller argument
    // than the original call.
    //
    //     S(add(S(b_minus), a_minus)) ==
    //     S(add(S(b_minus), a_minus))
    //
    // Done! Unfortunately, the solver can't take that first step,
    // using 'add_commute_s'. The reason is that it isn't sure that
    // the call 'add(S(b_minus), a_minus)' actually produces a
    // value. We have't called 'add' with those specific arguments
    // anywhere in our verification condition or in the
    // single-unrolling of either call to 'add', and so (for
    // decidability reasons), it assumes that 'add(S(b_minus),
    // a_minus)' is undefined, and that 'add_commute_s' cannot be
    // applied.
    //
    // We fix this by telling the solver that 'add(S(b_minus),
    // a_minus)' is indeed defined, using the 'for_inst' line below.
    #[annotate_multi]
    // In order to make the 'for_inst' call, we quantify a_minus.
    #[for_values(a: Nat, a_minus: Nat, b: Nat)]
    #[for_call(add(a,b) => c)]
    #[for_call(add(b,a) => d)]
    // Assert that 'add(b, a_minus)' has a value. We don't need to
    // actually reference that value in the verification condition.
    #[for_inst(add(b, a_minus))]
    fn add_commutative() -> bool {
        // First consider the a == Z case.
        implies(a == Nat::Z, c == d) &&
        // Then, for the a == S(a_minus) case, assume the relation
        // between a and a_minus.
        implies(
            a == Nat::S(a_minus),
            c == d,
        )
    }

    // Now, let's look at a simpler example of quantifier
    // instantiation *without* induction.
    //
    // First, verify the following property:

    #[annotate_multi]
    #[for_values(a: Nat, b: Nat, b_plus: Nat)]
    #[for_call(add(a,b) => c)]
    #[for_call(add(a,b_plus) => c_plus)]
    fn add_s() -> bool {
        implies(
            b_plus == Nat::S(b),
            c_plus == Nat::S(c),
        )
    }

    // Then, verify the following property non-inductively, just using
    // the assumptions and verified annotations we have on 'add' so
    // far (no unrolling).
    //
    // This problem can be solved by applying 'add_commutative' and
    // 'add_s' to transform one side of the equation. But once again,
    // the solver doesn't know that the intermediate expression
    // 'add(b, Nat::S(a))' actually has a defined value, so it can't
    // apply the rules: we need an instantiation.
    //

    #[verify]
    fn add_s_c2() -> bool {
        forall(|a: Nat, b: Nat, a_minus: Nat| {
            // Since we are not in an inductive proof, we can simply
            // let-bind the expressions that need instantiation, and
            // ignore what those values actually are.
            let _ = add(b, Nat::S(a));
            // Since we aren't unrolling 'add' in this problem, the
            // solver doesn't even know that Nat::S(add(b,a)) has a
            // value! We need to instantiate that as well.
            let _ = Nat::S(add(b,a));

            let goal =
                add(Nat::S(a), b) == Nat::S(add(a,b));

            // Finally, to prove the goal, we need to match on
            // 'a'. This instructs the solver to only consider the
            // cases in which 'a' is Z or S of something, and to
            // ignore the case in which it is neither. That case isn't
            // real, of course, but once again, the solver doesn't
            // know.
            match a {
                Nat::Z => goal,
                Nat::S(a_minus) => goal,
            }
        })
    }

    // This version of 'add' is more verbose than the original, but
    // makes verification of 'commute' more straightforward, because
    // after unrolling, the two calls to 'add_alt' both apply to the
    // same pair of values---a_minus and b_minus---just in different
    // orders.
    #[define]
    #[recursive]
    fn add_alt(a: Nat, b: Nat) -> Nat {
        match a.clone() {
            Nat::Z => b,
            Nat::S(a_minus) => match b {
                Nat::Z => a,
                Nat::S(b_minus) =>
                    Nat::S(Box::new(
                        Nat::S(Box::new(
                            add_alt(*a_minus, *b_minus)
                        ))
                    ))
            }
        }
    }

    // The #[annotate_multi] command allows you to recursively verify
    // multiple function calls together, allowing for conditions like
    // commutativity.
    //
    // Unlike #[annotate(..)], you must explicitly forall-quantify the
    // inputs to the calls with the #[for_values] line.
    #[annotate_multi]
    #[for_values(a: Nat, b: Nat)]
    #[for_call(add_alt(a,b) => c)]
    #[for_call(add_alt(b,a) => d)]
    fn add_alt_commutative() -> bool {
        c == d
    }

    #[define]
    #[recursive]
    fn max(a: Nat, b: Nat) -> Nat {
        match a {
            Nat::Z => b,
            Nat::S(a_minus) => match b {
                Nat::Z => Nat::S(a_minus),
                Nat::S(b_minus) => {
                    let c = max(*a_minus, *b_minus);
                    Nat::S(Box::new(c))
                }
            }
        }
    }

    #[annotate_multi]
    #[for_values(a: Nat, b: Nat)]
    #[for_call(max(a,b) => c)]
    #[for_call(max(b,a) => d)]
    fn max_commutative() -> bool {
        c == d
    }

    // Here are some normal Rust tests that actually run the above
    // functions, just to check that we haven't made any simple
    // mistakes in their definitions.
    #[test]
    fn max1() {
        assert!(
            max(Nat::from_usize(1), Nat::from_usize(0)) == Nat::from_usize(1)
        )
    }
    #[test]
    fn max2() {
        assert!(
            max(Nat::from_usize(0), Nat::from_usize(1)) == Nat::from_usize(1)
        )
    }
    #[test]
    fn max3() {
        assert!(
            max(Nat::from_usize(7), Nat::from_usize(7)) == Nat::from_usize(7)
        )
    }
    #[test]
    fn max4() {
        assert!(
            max(Nat::from_usize(7), Nat::from_usize(20)) == Nat::from_usize(20)
        )
    }
    #[test]
    fn max5() {
        assert!(
            max(Nat::from_usize(7), Nat::from_usize(2)) == Nat::from_usize(7)
        )
    }
    #[test]
    fn add1() {
        assert!(
            add(Nat::from_usize(1), Nat::from_usize(2)) == Nat::from_usize(3)
        )
    }
    #[test]
    fn add2() {
        assert!(
            add(Nat::from_usize(2), Nat::from_usize(1)) == Nat::from_usize(3)
        )
    }
}

#[ravencheck::check_module]
#[allow(dead_code)]
mod small_inductive {
    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    enum Nat { Z, S(Box<Nat>) }

    #[define]
    #[recursive]
    fn add(a: Nat, b: Nat) -> Nat {
        match a {
            Nat::Z => b,
            Nat::S(a_minus) =>
                // We unbox `a_minus` before calling `add`, and then
                // re-box the output of `add` so that we can wrap it
                // in Nat::S.
                Nat::S(Box::new(add(*a_minus,b))),
        }
    }

    #[annotate_multi]
    #[for_values(a: Nat, b: Nat, x: Nat, y: Nat)]
    #[for_call(add(a,b) => c)]
    #[for_call(add(x,y) => d)]
    fn add_z_left() -> bool {
        // First consider the a == Z case.
        implies(a == Nat::Z, b == c)
    }
}
