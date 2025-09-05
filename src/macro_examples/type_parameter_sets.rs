#[crate::check_module(crate)]
#[declare_types(u32, HashSet<_>)]
#[allow(dead_code)]
mod my_mod {
    use std::collections::HashSet;
    use std::hash::Hash;

    #[declare]
    fn member_poly<E: Eq + Hash>(e: E, s: HashSet<E>) -> bool {
        s.contains(&e)
    }

    #[declare]
    fn empty_poly<E: Eq + Hash>() -> HashSet<E> {
        HashSet::new()
    }

    #[assume((HashSet<E>, E))]
    fn empty_no_member<E: Eq + Hash>() -> bool {
        forall(|e: E| !member_poly::<E>(e, empty_poly::<E>()))
    }

    #[declare]
    fn member_u32(e: u32, s: HashSet<u32>) -> bool {
        member_poly::<u32>(e,s)
    }

    #[assume((HashSet<E>, E))]
    fn equal_or_dist<E: Eq + Hash>() -> bool {
        forall(|s1: HashSet<E>, s2: HashSet<E>| {
            s1 == s2 || exists(|e: E| {
                member_poly::<E>(e, s1)
                    != member_poly::<E>(e, s2)
            })
        })
    }

    #[verify]
    fn empty_eq() -> bool {
        forall(|s: HashSet<u32>| {
            implies(
                forall(|e: u32| !member_poly::<u32>(e,s)),
                s == empty_poly::<u32>(),
            )
        })
    }

    #[verify]
    fn trivial_u32() -> bool {
        forall(|e: u32, s1: HashSet<u32>, s2: HashSet<u32>| {
            implies(
                s1 == s2 && member_u32(e,s1),
                member_u32(e,s2),
            )
        })
    }

    #[verify]
    fn trivial_u32_poly() -> bool {
        forall(|e: u32, s1: HashSet<u32>, s2: HashSet<u32>| {
            implies(
                s1 == s2 && member_poly::<u32>(e,s1),
                member_poly::<u32>(e,s2),
            )
        })
    }
}
