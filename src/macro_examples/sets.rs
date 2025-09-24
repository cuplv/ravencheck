// When using this macro within this crate, call it as:
//
// #[crate::check_module(crate)]
//
// When using it in another crate that has ravencheck as a dependency,
// call it as:
//
// #[ravencheck::check_module]
//
// If you rename the ravencheck dependency, for example as "my_dep",
// then call this macro as:
//
// #[my_dep::check_module(my_dep)]
#[crate::check_module(crate)]
pub mod my_mod {
    use std::collections::HashSet;

    #[declare]
    #[derive(PartialEq, Eq, Clone)]
    pub struct Set(pub HashSet<u32>);

    #[declare]
    pub fn empty_set() -> Set {
        Set(HashSet::new())
    }

    #[declare]
    #[derive(PartialEq, Eq, Clone, Copy)]
    pub struct Elem(u32);

    #[declare]
    pub fn member(e: Elem, s: Set) -> bool {
        s.0.contains(&e.0)
    }

    #[assume]
    fn equal_or_distinguisher() -> bool {
        forall(|a:Set,b:Set| {
            a == b || exists(|e:Elem| member(e,a) !=  member(e,b))
        })
    }

    #[assume]
    fn empty_set_no_member() -> bool {
        forall(|e: Elem| {
            !member(e, empty_set())
        })
    }

    #[declare]
    pub fn union(a: Set, b: Set) -> Set {
        let Set(s1) = a;
        let Set(s2) = b;
        let s3 = s1.union(&s2).cloned().collect();
        Set(s3)
    }

    #[assume(union(a,b) => c)]
    fn union_def() -> bool {
        forall(|e: Elem| {
            member(e,c) == (member(e,a) || member(e,b))
        })
    }

    #[verify]
    fn union_preserves_member() -> bool {
        forall(|e:Elem,s:Set| {
            !member(e,s) || member(e, union(s,s))
        })
    }

    #[verify]
    fn union_self_is_self() -> bool {
        forall(|s:Set| union(s,s) == s)
    }

    #[verify]
    fn union_empty_set() -> bool {
        union(empty_set(), empty_set()) == empty_set()
    }

    #[cfg(test)]
    mod runtime_properties {
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
                !member(Elem(1), empty_set())
            )
        }
    }
}
