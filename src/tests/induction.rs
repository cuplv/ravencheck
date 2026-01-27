#[crate::check_module(crate)]
#[allow(dead_code)]
mod induction {
    #[define]
    enum Nat { Z, S(Box<Nat>) }

    #[define]
    #[recursive]
    fn add(x: Nat, y: Nat) -> Nat {
        match x {
            Nat::Z => y,
            Nat::S(x_sub) => Nat::S(Box::new(add(*x_sub, y))),
        }
    }

    #[annotate_multi]
    #[for_values(x: Nat, y: Nat, sy: Nat)]
    #[for_call(add(x,y) => xy)]
    #[for_call(add(x,sy) => xsy)]
    fn factor_s_right_good() -> Bool {
        implies(
            sy == Nat::S(y),
            Nat::S(xy) == xsy
        )
    }

    #[annotate_multi]
    #[should_fail]
    #[for_values(x: Nat, y: Nat, sy: Nat)]
    #[for_call(add(x,y) => xy)]
    #[for_call(add(x,sy) => xsy)]
    fn factor_s_right_oops() -> Bool {
        implies(
            sy == Nat::S(y),
            // This line uses != in place of ==
            Nat::S(xy) != xsy
        )
    }

    #[annotate_multi]
    #[should_fail]
    #[for_values(x: Nat, y: Nat, z: Nat)]
    #[for_call(add(x,x) => xx)]
    fn prop_0() -> bool {
        // Should obviously fail.
        add(y,y) == add(z,z)
    }

    #[annotate_multi]
    #[should_fail]
    #[for_values(x: Nat)]
    #[for_call(add(x,x) => xx)]
    fn prop_1() -> bool {
        // Here is a second version that should fail, which quantifies
        // y and z in a different way.
        forall(|y: Nat, z: Nat| {
            add(y,y) == add(z,z)
        })
    }
}
