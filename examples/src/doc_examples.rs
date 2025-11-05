#[ravencheck::check_module]
#[declare_types(u32)]
pub mod rvn {
    #[declare]
    pub const ZERO: u32 = 0;

    #[declare]
    pub fn le(a: u32, b: u32) -> bool {
        a <= b
    }

    #[assume]
    fn le_anti_symmetric(x: u32, y: u32) -> bool {
        implies(
            le(x,y) && le(y,x),
            x == y
        )
    }

    #[assume]
    fn zero_is_least(x: u32) -> bool {
        le(ZERO, x)
    }

    #[define]
    pub fn ge(a: u32, b: u32) -> bool {
        le(b,a)
    }

    #[verify]
    fn greater_or_eq_to_zero(x: u32) -> bool {
        ge(x, ZERO)
    }

    #[falsify]
    fn less_or_eq_to_zero(x: u32) -> bool {
        le(x, ZERO)
    }

    #[verify]
    fn always_a_less_or_eq(x: u32) -> bool {
        exists(|y: u32| le(y,x))
    }
}
