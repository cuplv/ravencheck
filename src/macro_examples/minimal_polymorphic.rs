#[crate::check_module(crate)]
#[declare_types(u32, HashSet<_>)]
#[allow(dead_code)]
pub mod my_mod {
    use std::collections::HashSet;
    use std::hash::Hash;

    #[declare]
    pub fn member<E: Eq + Hash>(e: E, s: HashSet<E>) -> bool {
        s.contains(&e)
    }

    #[assume]
    #[for_type(HashSet<E> => <E>)]
    fn equal_or_distinguisher<E: Eq + Hash>() -> bool {
        forall(|a:HashSet<E>,b:HashSet<E>| {
            a == b || exists(|e:E| member::<E>(e,a) !=  member::<E>(e,b))
        })
    }

    #[falsify]
    fn prop1<E: Eq + Hash>() -> bool {
        forall(|a: HashSet<E>, b: HashSet<E>| a == b)
    }

    #[verify]
    fn prop2<E: Eq + Hash>() -> bool {
        forall(|e: E, s: HashSet<E>| member::<E>(e,s) == member::<E>(e,s))
    }
    #[verify]
    fn prop3<E: Eq + Hash>() -> bool {
        forall(|s1: HashSet<E>, s2: HashSet<E>| {
            (exists(|e:E| member::<E>(e,s1) != member::<E>(e,s2)))
                || s1 == s2
        })
    }
    #[falsify]
    fn prop4<E: Eq + Hash>() -> bool {
        forall(|s1: HashSet<E>, s2: HashSet<E>| {
            (exists(|e:E| member::<E>(e,s1) != member::<E>(e,s2)))
                && s1 == s2
        })
    }
}
