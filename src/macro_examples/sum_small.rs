#[crate::check_module(crate)]
#[declare_types(usize)]
#[allow(dead_code)]
mod rvn {

    #[define]
    enum Test {
        ConA,
        ConB,
    }

    #[verify]
    fn test_test() -> bool {
        forall(|v: Test| match v {
            Test::ConA => true,
            Test::ConB => true,
        })
    }
}
