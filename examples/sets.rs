// This small example shows how to call the macro in your own code
// when you have 'ravencheck' as a dependency.
//
// See src/macro_examples/* for more examples.

// The 'check_module' macro generates a test module that verifies the
// specified goal properties using an SMT solver. To run the
// verification, simply use 'cargo test'. Just like normal Rust tests,
// the verification-specific code is erased when compiling for
// release.
#[ravencheck::check_module]
// This command declares the uninterpreted type 'u32' to the solver.
#[declare_types(u32)]
pub mod my_mod {
    use std::collections::HashSet;

    // The 'declare' attribute tells the solver that we have an
    // uninterpreted type called 'MySet'.
    #[declare]
    pub type MySet = HashSet<u32>;

    // Here, 'declare' tells the solver that we have an uninterpreted
    // constant called 'empty_set' with type 'MySet'.
    #[declare]
    pub fn empty_set() -> MySet {
        HashSet::new()
    }

    // Declare an uninterpreted relation (boolean-output function) on
    // 'u32' and 'MySet'.
    #[declare]
    pub fn member(e: u32, s: MySet) -> bool {
        s.contains(&e)
    }

    // The 'assume' attribute gives the body of the following function
    // to the solver as an axiom.
    //
    // This function body is erased before the Rust compiler is
    // called, so we can use special logical syntax like forall(..)
    // and exists(..).
    #[assume]
    fn equal_or_distinguisher() -> bool {
        forall(|a:MySet,b:MySet| {
            a == b || exists(|e:u32| member(e,a) !=  member(e,b))
        })
    }

    #[assume]
    fn empty_set_no_member() -> bool {
        forall(|e: u32| {
            !member(e, empty_set())
        })
    }

    // Declare an uninterpreted function on 'MySet'.
    #[declare]
    pub fn union(a: MySet, b: MySet) -> MySet {
        a.union(&b).cloned().collect()
    }

    // This is a special form of 'assume' that uses the function body
    // as an axiom on (a,b,c) that must be true when union(a,b) = c.
    #[annotate(union)]
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
        forall(|a: MySet, b: MySet| {
            union(union(a,b), b) != union(a,b)
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

// Now we can use the definitions from above the module in normal Rust
// code.
fn main() {
    let s = my_mod::empty_set();
    let result = my_mod::union(s.clone(), s.clone()) == s;
    println!("Result is {}", result);
}
