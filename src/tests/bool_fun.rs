#[crate::check_module(crate)]
#[declare_types(u32)]
#[allow(dead_code)]
mod bool_fun {
    #[declare]
    fn foo(b: bool) -> u32 {
        0
    }

    #[falsify]
    fn prop1(n: u32) -> bool {
        n == foo(n == n)
    }
}
