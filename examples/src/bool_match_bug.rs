#[ravencheck::check_module]
#[allow(dead_code)]
mod rvn {

    #[falsify]
    fn quant_bool1() -> bool {
        forall(|b: bool| b)
    }

    #[falsify]
    fn quant_bool2() -> bool {
        forall(|b: bool| !b)
    }

    #[verify]
    fn quant_bool3() -> bool {
        forall(|b: bool| b || !b)
    }

    #[falsify]
    fn quant_bool4() -> bool {
        forall(|b1: bool, b2: bool| b1 || b2)
    }

    #[falsify]
    fn quant_bool5() -> bool {
        forall(|b1: bool, b2: bool, b3: bool| b1 || b2 || b3)
    }

    #[define]
    enum TestEnum {
        ConA(bool),
    }

    #[falsify]
    fn test_bug1() -> bool {
        forall(|t: TestEnum| {
            match t {
                TestEnum::ConA(b) => b,
            }
        })
    }

    #[verify]
    fn test_bug2() -> bool {
        forall(|t: TestEnum| {
            match t {
                TestEnum::ConA(b) => b || !b,
            }
        })
    }
}
