/*!
Ravencheck is a verification framework for your Rust code.
With it, you can add quantified verification goals to your code
using the `#[verify]` attribute,
just like how you add tests to your code using `#[test]`.

# Getting Started

You use Ravencheck by adding macro attributes to you code.
This example introduces the most important attributes.

First, to use Ravencheck within a module,
you add `#[ravencheck::module]`
to the top.
Note that the module must be entirely within a single file,
as in the example below.

```
#[ravencheck::module]
// Make the `u32` type visible to Ravencheck
// as an uninterpreted sort.
#[declare_types(u32)]
pub mod rvn_u32 {
    // Make a constant `ZERO` visible to Ravencheck.
    // Ravencheck doesn't see the right-hand side
    // of the `=`.
    #[declare]
    pub const ZERO: u32 = 0;

    // Ravencheck only sees the signature of this function,
    // so the body can contain arbitrary code.
    #[declare]
    pub fn less_or_eq(a: u32, b: u32) -> bool {
        a <= b
    }

    // Because we use #[define] here,
    // Ravencheck sees both the signature and the body.
    // This means that the body cannot include mutable assignments,
    // method calls, or any functions/constants/types
    // that have not already been made visible to Ravencheck.
    // Operators are restricted to `!`, `==`, `!=`, `&&`, and `||`.
    #[define]
    pub fn less_than(a: u32, b: u32) -> bool {
        less_or_eq(a,b) && a != b
    }

    // Assume the anti-symmetric property for `less_or_eq`.
    // This definition only exists at verification time,
    // so we can use Ravencheck-only operators like `forall`.
    //
    // Because we used #[define] to introduce `less_or_eq`,
    // Ravencheck knows nothing about its behavior
    // except what we tell it with #[assume].
    #[assume]
    fn le_anti_symmetric() -> bool {
        forall(|x: u32, y: u32| {
            implies(
                less_or_eq(x,y) && less_or_eq(y,x),
                x == y
            )
        })
    }

    // Assume that `ZERO` is less than or equal to every `u32`.
    #[assume]
    fn zero_is_least() -> bool {
        forall(|x: u32| less_or_eq(ZERO, x))
    }

    // Check that no `u32` is less than `ZERO`.
    // The `x` argument to the function is universally quantified.
    // We could also explicitly quantify it using `forall`,
    // like in the #[assume] conditions.
    #[verify]
    fn zero_is_smallest(x: u32) -> bool {
        !(less_than(x, ZERO))
    }

    // Check that it *cannot* be proven
    // that all `u32`s are equal to `ZERO`.
    // This can be useful as a sanity-check
    // for your trusted axioms.
    #[falsify]
    fn zero_is_only(x: u32) -> bool {
        x == ZERO
    }
}
```

To perform verification,
you will need the [CVC5 SMT solver](https://cvc5.github.io/) installed,
and in your PATH.
Then, just run `cargo test`.

# Importing from Other Modules

To use Ravencheck declarations, definitions, and assumptions
from one module to verify goals in another module,
use the `#[import]` attribute.

```ignore
#[ravencheck::module]
pub mod import_example {
    // Here, `#[import]` makes all the #[declare], #[define] and
    // #[assume] items from the `rvn_u32` module visible to Ravencheck
    // in this module as well.
    #[import]
    use crate::doc_examples::rvn_u32::*;

    /// `in_range(a,b,c)` is true when `c` is greater than or equal to
    /// `a` and less than `b`.
    #[define]
    pub fn in_range(lower: u32, upper: u32, x: u32) -> bool {
        less_or_eq(lower, x)
            && less_than(x, upper)
    }

    // Check that if the lower bound is smaller than the upper bound,
    // then at least one `u32` is in the range.
    #[verify]
    pub fn range_not_empty(lower: u32, upper: u32) -> bool {
        implies(
            less_than(lower, upper),
            exists(|x: u32| in_range(lower, upper, x))
        )
    }
}
```

# Sort Cycles

Ravencheck provides *decidable* verification.
This means that every SMT query can be verified or falsified
in a finite amount of time.
That said, as your verification goals grow in size,
you should expect solving time to also grow.

Ravencheck creates a directed graph of the sorts (types)
in your `#[assume]` and `#[verify]` properties.
If this graph contains a cycle,
then the condition is undecidable
and Ravencheck cannot verify or falsify it
(and will give you an error).

Edges between sorts in the graph
are created by two things in `#[verify]` conditions:

1. `exists(|x: A| ... forall(|y: B| ...))` creates an `A -> B` edge.
2. `exists(|x: A| ... foo(...) ...)` creates an `A -> T` edge if `foo`'s return type contains `T`.

In contrast, an `#[assume]` condition only creates an `A -> B` edge
if it contains `forall(|x: A| ... exists(|y: B| ...))`.

Finally, the `#[total]` attribute on a declared function
creates edges from all input types to all output types.

# Fixing Incompleteness with Instantiations

To maintain decidability,
Ravencheck assumes that all declared, non-`#[total]`,
non-bool-output functions are partial,
and it only applies an `#[assume]` rule
when the rule does not contain any function applications inside
that could be undefined.

For example, the following `add_right` condition
on inductive natural number type `Nat`
is falsifiable, even though it seems deducible
from the two `#[assume]` conditions.

```ignore
#[assume]
fn add_left(a: Nat, b: Nat) -> bool {
    less_or_eq(a, add(a,b))
}

#[assume]
fn add_commute(a: Nat, b: Nat) -> bool {
    add(a,b) == add(b,a)
}

#[falsify]
fn add_right(x: Nat, y: Nat) -> bool {
    less_or_eq(y, add(x,y))
}
```

Because `add(y,x)` is not called in the `add_right`,
Ravencheck cannot assume it is defined,
and cannot apply the `add_commute` rule for `x` and `y`,
which would contain the possibly undefined `add(y,x)`.
We can fix this by adding an *instantiation* of `add(y,x)`
to `add_right`.

```ignore
#[verify]
fn add_right(x: Nat, y: Nat) -> bool {
    let _ = add(y,x);
    less_or_eq(y, add(x,y))
}
```

You don't need to provide instantiations for a declared function
if you give it the `#[total]` attribute.
We can't give `add` the `#[total]` attribute
because that would create a `Nat -> Nat` edge in the sort graph,
which immediately creates a cycle (a self-loop on `Nat`).

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
    module,
};
pub use ravenlang::CheckedSig;
mod rcc;
pub use rcc::Rcc;

#[cfg(test)]
mod tests;
