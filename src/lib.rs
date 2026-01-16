/*!
# Example

```
#[ravencheck::check_module]
#[declare_types(u32)]
mod rvn {
    #[declare]
    const ZERO: u32 = 0;

    #[declare]
    fn le(a: u32, b: u32) -> bool {
        a <= b
    }

    #[assume]
    fn le_anti_symmetric() -> bool {
        forall(|x: u32, y: u32| {
            implies(
                le(x,y) && le(y,x),
                x == y
            )
        })
    }

    #[assume]
    fn zero_is_least() -> bool {
        forall(|x: u32| le(ZERO, x))
    }

    #[verify]
    fn prop1(x: u32) -> bool {
        implies(
            le(x, ZERO),
            x == ZERO
        )
    }
}
```

# Viewing Solver Input/Output

You can view the complete input/output trace with the solver
using the [`env_logger`](https://crates.io/crates/env_logger) system.

First, add `env_logger`
to your `Cargo.toml`.

```toml
[dependencies]
env_logger = "0.11.5"
```

Next, add the `#[log_solver]` attribute
to a Ravencheck module.

```ignore
#[ravencheck::check_module]
#[log_solver]
...
mod rvn {
    ...
}
```

Finally, set the `RUST_LOG` variable
to `easy_smt=trace` in your environment
when you `cargo test`.
You can do this on the command line as follows:

```ignore
$ RUST_LOG="easy_smt=trace" cargo test
````
*/

pub use ravencheck_macros::{
    check_module,
    export_module,
};
pub use ravenlang::CheckedSig;
mod rcc;
pub use rcc::Rcc;

#[cfg(test)]
mod tests;
