#[ravencheck::check_module]
#[declare_types(u32)]
pub mod rvn_u32 {
    #[declare]
    pub fn le(x: u32, y: u32) -> bool {
        x <= y
    }

    #[assume]
    fn le_reflexive(x: u32) -> bool {
        le(x,x)
    }

    #[verify]
    fn exists_less_or_eq(x: u32) -> bool {
        exists(|y: u32| le(y,x))
    }

    #[declare]
    pub const ZERO: u32 = 0;

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
}
