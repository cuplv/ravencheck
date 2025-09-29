#[crate::check_module(crate)]
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

    // The following commutativity property for 'add' does not
    // directly verify, but the same property for 'add_alt' does
    // directly verify.
    //
    // What extra annotation(s) would let us verify 'add' without
    // modifying it?

    // #[annotate_multi]
    // #[for_values(a: Nat, b: Nat)]
    // #[for_call(add(a,b) => c)]
    // #[for_call(add(b,a) => d)]
    // fn add_commutative() -> bool {
    //     c == d
    // }

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
