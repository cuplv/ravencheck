// You can set and configure the SMT solver using the module
// attributes.

// In this example, my_favorite_solver is called with two arguments.
// This will (presumably) panic, because (presumably) the program
// "my_favorite_solver" cannot be found in the PATH.
#[ravencheck::check_module]
#[set_solver("my_favorite_solver", "--go-fast", "--try-hard")]
#[rvn_should_panic("No such file or directory")]
mod mod1 {
    #[verify]
    fn yes() -> bool {
        true
    }
}

// In this example, two arguments are added to the default solver
// configuration.  This should succeed, because they are valid
// arguments for the default solver (CVC5).
//
// These two arguments are added after the default arguments,
// currently:
//
//   cvc5
//     --lang smt2
//     --force-logic ALL
//     --full-saturate-quant
//     --finite-model-find
//
#[ravencheck::check_module]
#[add_solver_args("-v", "--mbqi")]
mod mod2 {
    #[verify]
    fn yes() -> bool {
        true
    }
}

// In this example, CVC5 is invoked without any of the default
// arguments, but with the -v argument.
#[ravencheck::check_module]
#[set_solver("cvc5")]
#[add_solver_args("-v")]
mod mod3 {
    #[verify]
    fn yes() -> bool {
        true
    }
}
