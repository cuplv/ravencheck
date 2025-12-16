#[ravencheck::check_module]
#[declare_types(u32)]
#[allow(dead_code)]
mod my_mod {
    use std::collections::HashSet;

    #[declare]
    type MySet = HashSet<(u32, (u32, u32))>;

    #[declare]
    fn member(e: (u32, (u32, u32)), s: MySet) -> bool {
        s.contains(&e)
    }

    #[assume]
    fn equal_or_distinguisher() -> bool {
        forall(|a:MySet,b:MySet| {
            a == b || exists(|e: (u32, (u32, u32))| member(e,a) !=  member(e,b))
        })
    }

    #[declare]
    fn filter(f: fn((u32, (u32, u32))) -> bool, s: MySet) -> MySet {
        let mut out = HashSet::new();
        for e in s.into_iter() {
            if f(e) {
                out.insert(e);
            }
        }
        out
    }

    #[assume(filter(f, s1) => s2)]
    fn filter_def() -> bool {
        forall(|e: (u32, (u32, u32))| {
            member(e,s2) == (member(e,s1) && f(e))
        })
    }

    // This propety must fails, thus used #[falsify]
    #[falsify]
    fn filter_prop() -> bool {
        forall(|e: (u32, (u32, u32)), s: MySet| {
            implies(
                !member(e,s),
                s == filter(|(_, (y, z)): (u32, (u32, u32))| (y, (y, z)) != e, s),
            )
        })
    }


    // #[cfg(test)]
    // #[test]
    // fn filter_test() {
    //     let a = HashSet::from([1,2]);
    //     let f = |x| x >= 2;
    //     let b = filter(f, a.clone());
    //     let c = filter(|_| false, a);
    //     let d = filter(f, b.clone());
    //     assert!(b == HashSet::from([2]));
    //     assert!(c == HashSet::new());
    //     assert!(b == d);
    // }
}
