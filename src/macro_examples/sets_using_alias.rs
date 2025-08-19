#[crate::check_module(crate)]
pub mod my_mod {
    use std::collections::HashSet;

    #[declare]
    type MySet = HashSet<u32>;

    #[declare]
    type MyU32 = u32;

    #[declare]
    fn empty_set() -> MySet {
        HashSet::new()
    }

    #[declare]
    fn member(e: MyU32, s: MySet) -> bool {
        s.contains(&e)
    }

    #[assume]
    fn equal_or_distinguisher() -> bool {
        forall(|a:MySet,b:MySet| {
            a == b || exists(|e:MyU32| member(e,a) !=  member(e,b))
        })
    }

    #[assume]
    fn empty_set_no_member() -> bool {
        forall(|e: MyU32| {
            !member(e, empty_set())
        })
    }

    #[declare]
    fn union(a: MySet, b: MySet) -> MySet {
        a.union(&b).cloned().collect()
    }

    #[annotate(union)]
    fn union_def(a: MySet, b: MySet, c: MySet) -> bool {
        forall(|e: MyU32| {
            member(e,c) == (member(e,a) || member(e,b))
        })
    }

    #[verify]
    fn union_idempotent() -> bool {
        forall(|a: MySet, b: MySet| {
            union(union(a,b), b) == union(a,b)
        })
    }

    #[cfg(test)]
    mod normal_tests {
        use super::*;
    
        #[test]
        fn union_empty_set() {
            assert!(
                union(empty_set(), empty_set()) == empty_set()
            )
        }

        #[test]
        fn empty_is_empty() {
            assert!(
                !member(1, empty_set())
            )
        }
    }
}
