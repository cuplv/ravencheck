#[ravencheck::check_module]
#[declare_types(u32)]
#[allow(dead_code)]
mod my_mod {
    #[define]
    pub fn foo(u1: u32, u2: u32) -> u32 {
        let (a, b, _c) = (u1, u1, u1);
        if a == b {
            let (_x, y, _z) = (u2, u2, u2);
            y
        } else {
            a
        }
    }

    #[verify]
    fn foo() -> bool {
        forall(|x: u32, y: u32| {
            foo(x,y) == y
        })
    }
}
