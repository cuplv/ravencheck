#[ravencheck::check_module]
#[allow(dead_code)]
mod rvn {
    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    enum Nat { Z, S(Box<Nat>) }

    #[define]
    #[recursive]
    fn le(a: &Nat, b: &Nat) -> bool {
        match a {
            Nat::Z => true,
            Nat::S(a_minus) => match b {
                Nat::Z => false,
                Nat::S(b_minus) => le(a_minus, b_minus),
            }
        }
    }

    #[annotate_multi]
    #[for_values(a: Nat)]
    #[for_call(le(a,a) => result1)]
    fn le_reflexive() -> bool {
        result1 == true
    }

    // This only verifies when 'le_reflexive' has been given as an
    // annotation.
    #[verify]
    fn le_reflexive_direct() -> bool {
        forall(|a: Nat| le(a,a))
    }

    #[annotate_multi]
    #[for_values(a: Nat, b: Nat)]
    #[for_call(le(a,b) => res_a_b)]
    #[for_call(le(b,a) => res_b_a)]
    fn le_total() -> bool {
        res_a_b || res_b_a
    }

    // This is marked as a 'should_fail', so it isn't actually added
    // to the assumption context for later verification tasks.
    #[annotate_multi]
    #[should_fail]
    #[for_values(a: Nat, b: Nat)]
    #[for_call(le(a,b) => res_a_b)]
    #[for_call(le(b,a) => res_b_a)]
    fn le_all_eq() -> bool {
        res_a_b && res_b_a
    }

    #[annotate_multi]
    #[for_values(a: Nat, b: Nat)]
    #[for_call(le(a,b) => res_a_b)]
    #[for_call(le(b,a) => res_b_a)]
    fn le_antireflexive() -> bool {
        implies(
            res_a_b && res_b_a,
            a == b,
        )
    }

    #[annotate_multi]
    #[for_values(a: Nat, b: Nat, c: Nat)]
    #[for_call(le(a,b) => res_a_b)]
    #[for_call(le(b,c) => res_b_c)]
    #[for_call(le(a,c) => res_a_c)]
    fn le_transitive() -> bool {
        implies(
            res_a_b && res_b_c,
            res_a_c,
        )
    }

    // A sanity check, testing the recursion guards.
    #[annotate_multi]
    #[should_fail]
    #[for_values(a: Nat, b: Nat)]
    #[for_call(le(a,b) => result1)]
    fn should_fail() -> bool {
        false
    }

    #[falsify]
    fn should_really_fail() -> bool {
        false
    }
}
