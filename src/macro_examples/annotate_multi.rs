#[crate::check_module(crate)]
#[allow(dead_code)]
mod rvn {
    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    enum Nat { Z, S(Box<Nat>) }

    impl Nat {
        fn from_usize(n: usize) -> Self {
            if n == 0 {
                Self::Z
            } else {
                Self::S(Box::new(Self::from_usize(n - 1)))
            }
        }
    }

    #[define]
    #[recursive]
    fn get_zero(a: Nat) -> Nat {
        match a {
            Nat::Z => Nat::Z,
            Nat::S(a_minus) => get_zero(*a_minus),
        }
    }

    // #[annotate_multi]
    // #[for_values(a: Nat)]
    // #[for_call(get_zero(a) => z)]
    // fn always_zero1() -> bool {
    //     z == Nat::Z
    // }

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
                Nat::S(Box::new(add(*a_minus,b))),
        }
    }

    // #[annotate_multi]
    // #[for_values(a: Nat, b: Nat)]
    // #[for_call(add(a,b) => c)]
    // #[for_call(add(b,a) => d)]
    // fn add_commutative() -> bool {
    //     c == d
    // }

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

    // #[annotate_multi]
    // #[for_values(a: Nat, b: Nat)]
    // #[for_call(max(a,b) => c)]
    // #[for_call(max(b,a) => d)]
    // fn max_commutative() -> bool {
    //     c == d
    // }

    #[test]
    fn max1() {
        assert!(
            max(Nat::from_usize(1), Nat::from_usize(0)) == Nat::from_usize(1)
        )
    }
    fn max2() {
        assert!(
            max(Nat::from_usize(0), Nat::from_usize(1)) == Nat::from_usize(1)
        )
    }
    fn max3() {
        assert!(
            max(Nat::from_usize(7), Nat::from_usize(7)) == Nat::from_usize(7)
        )
    }
    fn max4() {
        assert!(
            max(Nat::from_usize(7), Nat::from_usize(20)) == Nat::from_usize(20)
        )
    }
    fn max5() {
        assert!(
            max(Nat::from_usize(7), Nat::from_usize(2)) == Nat::from_usize(7)
        )
    }
}
