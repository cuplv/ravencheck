// This is the main macro call that tells ravencheck to use
// verification in this module.
//
// Because this example file is inside the ravencheck library, we call
// it using 'crate'.
//
// When using it in your own library, you would call it as:
//
//     #[ravencheck::check_module]
//     mod my_mod { .. }
//
#[crate::check_module(crate)]
// This command declares the uninterpreted type 'u32' to the solver.
#[declare_types(u32)]
#[allow(dead_code)]
mod my_mod {
    use std::collections::HashSet;

    // The 'declare' attribute tells the solver that we have an
    // uninterpreted type called 'MySet'.
    #[declare]
    type MySet = HashSet<u32>;

    // The 'define' attribute informs the solver of a a type
    // alias. The right-hand side of this definition must be a type
    // that has already been declared (or defined) to the solver.
    #[define]
    type MySetAlias = MySet;

    // Declare an uninterpreted relation (boolean-output function) on
    // 'u32' and 'MySet'.
    #[declare]
    fn member(e: u32, s: MySet) -> bool {
        s.contains(&e)
    }

    // The 'assume' attribute gives the body of the following function
    // to the solver as an axiom.
    //
    // This function body is erased before the Rust compiler is
    // called, so we can use the special functions forall(..)  and
    // exists(..).
    #[assume]
    fn equal_or_distinguisher() -> bool {
        forall(|a:MySet,b:MySet| {
            a == b || exists(|e:u32| member(e,a) !=  member(e,b))
        })
    }

    // Here, 'declare' tells the solver that we have an uninterpreted
    // constant called 'empty_set' with type 'MySet'.
    #[declare]
    fn empty_set() -> MySet {
        HashSet::new()
    }

    #[assume]
    fn empty_set_no_member() -> bool {
        forall(|e: u32| {
            !member(e, empty_set())
        })
    }

    // Declare an uninterpreted function on 'MySet'.
    #[declare]
    fn union(a: MySet, b: MySetAlias) -> MySetAlias {
        a.union(&b).cloned().collect()
    }

    // This is a special form of 'assume' that uses the function body
    // as an axiom on (a,b,c) that must be true when union(a,b) = c.
    #[assume_for(union)]
    fn union_def() -> bool {
        // Function input arguments
        |a: MySet, b: MySet|
        // Function output
        |c: MySet|
        // Condition that relates the inputs and output
        forall(|e: u32| {
            member(e,c) == (member(e,a) || member(e,b))
        })
    }

    // The 'verify' attribute gives the following function body to the
    // solver as a verification goal, which it checks based on the
    // axioms it has received so far.
    //
    // The #[verify] attribute is analogous to the #[test] attribute
    // in an ordinary Rust testing module.
    #[verify]
    fn union_idempotent() -> bool {
        forall(|a: MySetAlias, b: MySet| {
            union(union(a,b), b) == union(a,b)
        })
    }

    #[declare]
    fn insert(e: u32, mut s: MySet) -> MySet {
        s.insert(e);
        s
    }

    #[assume_for(insert)]
    fn insert_def() -> bool {
        |e: u32, s1: MySet|
        |s2: MySet|
        forall(|x:u32| member(x,s2) == (member(x,s1) || x == e))
    }

    #[verify]
    fn insert_monotonic() -> bool {
        forall(|e1: u32, e2: u32, s: MySet| {
            implies(
                member(e1,s),
                member(e1, insert(e2,s)),
            )
        })
    }

    // The 'define' attribute allows the solver to use the definition
    // of the function, rather than treating it as uninterpreted.
    //
    // When using 'define', the function body must follow some rules:
    //
    // * All functions/constants used must already be declared/defined
    // * No mutation or method calls
    // * No recursion
    #[define]
    fn singleton(e: u32) -> MySet {
        insert(e, empty_set())
    }

    #[verify]
    fn singleton_membership() -> bool {
        forall(|e1: u32, e2: u32| {
            member(e1, singleton(e2)) == (e1 == e2)
        })
    }

    // Here are ordinary Rust tests, which are checked by compiling
    // them using the Rust compiler and then executing the results.
    //
    // Calling 'cargo test' will run these tests alongside the
    // verification process for the #[verify] properties above.
    #[cfg(test)]
    mod normal_tests {
        use super::*;

        // Since this is real Rust code that will be executed, we
        // can't use logical quantifiers like forall(..) and
        // exists(..).
        //
        // Compare this test to the 'union_self_is_self' verification
        // property above.
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
