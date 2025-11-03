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
    fn prop1() -> bool {
        forall(|x: u32| {
            implies(
                le(x, ZERO),
                x == ZERO
            )
        })
    }
}
```
*/

#[cfg(test)]
mod macro_examples;

pub use ravencheck_macros::{
    check_module,
    export_module,
};
pub use ravenlang::CheckedSig;
mod rcc;
pub use rcc::Rcc;
