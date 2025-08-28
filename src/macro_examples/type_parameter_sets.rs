#[crate::check_module(crate)]
#[declare_types(u32, HashSet<_>)]
#[allow(dead_code)]
mod my_mod {
    use std::collections::HashSet;

    #[declare]
    fn member_u32(e: u32, s: HashSet<u32>) -> bool {
        s.contains(&e)
    }

    #[verify]
    fn trivial() -> bool {
        forall(|e: u32, s1: HashSet<u32>, s2: HashSet<u32>| {
            implies(
                s1 == s2 && member_u32(e,s1),
                member_u32(e,s2),
            )
        })
    }
}
