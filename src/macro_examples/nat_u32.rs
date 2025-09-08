#[crate::check_module(crate)]
#[declare_types(u32)]
#[allow(dead_code)]
mod my_mod {
    #[declare]
    const ZERO: u32 = 0;

    #[declare]
    fn le(a: u32, b: u32) -> bool {
        a <= b
    }

    #[define]
    fn lt(a: u32, b: u32) -> bool
    {
        le(a,b) && a != b
    }

    #[define]
    fn ge(a: u32, b: u32) -> bool
    {
        le(b,a)
    }

    #[define]
    fn gt(a: u32, b: u32) -> bool
    {
        ge(a,b) && a != b
    }

    #[declare]
    fn dec(a: u32) -> u32 {
        if a == 0 {
            0
        } else {
            a - 1
        }
    }

    #[declare]
    fn inc(a: u32) -> u32 {
        a + 1
    }

    #[assume]
    fn inc_dec() -> bool {
        forall(|a: u32| {
            implies(
                a != ZERO,
                inc(dec(a)) == a
            )
        })
    }

    #[define_rec]
    fn add(a: u32, b: u32) -> u32
    {
        if a == ZERO {
            b
        } else {
            inc(
                add(dec(a), b)
            )
        }
    }

    #[annotate(add)]
    fn add_trivial() -> bool {
        |a: u32, b: u32|
        |c: u32|
        true
    }

    // #[annotate(add)]
    // fn add_monotonic() -> bool {
    //     |a: u32, b: u32|
    //     |c: u32|
    //     le(a,c) && le(a,b)
    // }

    #[annotate(add)]
    fn add_zeros() -> bool {
        |a: u32, b: u32|
        |c: u32|
        implies(a == ZERO, b == c)
        && implies(b == ZERO, a == c)
    }

    #[verify]
    fn simple_zeros() -> bool {
        add(ZERO, ZERO) == ZERO
    }
}
