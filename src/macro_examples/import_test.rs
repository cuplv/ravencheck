#[crate::check_module(crate)]
#[declare_types(u32)]
#[allow(dead_code)]
mod my_mod {
    #[import]
    use crate::macro_examples::nat::my_nat_mod::{Nat, le};

    #[define]
    fn in_range(min: Nat<u32>, max: Nat<u32>, x: Nat<u32>) -> bool {
        le::<u32>(min, x) && le::<u32>(x, max)
    }

    #[verify]
    fn in_range_refl() -> bool {
        forall(|x: Nat<u32>| in_range(x,x,x))
    }

    #[falsify]
    fn in_range_any() -> bool {
        forall(|x: Nat<u32>, y: Nat<u32>, z: Nat<u32>| in_range(x,y,z))
    }
}
