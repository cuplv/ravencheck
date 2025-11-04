#[ravencheck::check_module]
#[declare_types(u32, HashSet<_>)]
#[allow(dead_code)]
pub mod my_mod {
    use std::collections::HashSet;
    use std::hash::Hash;

    #[declare]
    pub fn member<E: Eq + Hash>(e: &E, s: &HashSet<E>) -> bool {
        s.contains(e)
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

    #[declare]
    fn set_empty<E: Eq + Hash>() -> HashSet<E> {
        HashSet::new()
    }

    #[assume]
    #[for_type(HashSet<E> => <E>)]
    fn set_empty_no_member<E>() -> bool {
        forall(|e: E| !member::<E>(e, set_empty::<E>()))
    }

    #[declare]
    pub fn set_filter<E: Eq + Hash>(
        f: impl Fn(&E) -> bool,
        s: HashSet<E>,
    ) -> HashSet<E> {
        let mut out = HashSet::new();
        for e in s.into_iter() {
            if f(&e) {
                out.insert(e);
            }
        }
        out
    }

    #[assume(set_filter::<D>(f, m) => m2)]
    fn member_after_filter() -> bool {
        forall(|e: D| {
            member::<D>(&e, &m2)
                == (member::<D>(&e, &m) && f(&e))
        })
    }

    #[verify]
    fn filter_false<E>() -> bool {
        forall(|s: HashSet<E>| {
            set_filter::<E>(|e: &E| false, s) == set_empty::<E>()
        })
    }
}
