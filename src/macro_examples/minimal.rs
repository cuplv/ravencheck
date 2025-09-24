#[crate::check_module(crate)]
#[allow(dead_code)]
pub mod my_mod {
    use std::collections::HashSet;

    #[declare]
    #[derive(PartialEq, Eq, Clone)]
    pub struct Set(pub HashSet<u32>);

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

    #[falsify]
    fn prop1() -> bool {
        forall(|a: Set, b: Set| a == b)
    }

    #[verify]
    fn prop2() -> bool {
        forall(|e: Elem, s: Set| member(e,s) == member(e,s))
    }
}
