#[ravencheck::check_module]
#[declare_types(usize)]
#[allow(dead_code)]
mod rvn {

    #[define]
    #[phantom]
    enum Test {
        ConA,
        ConB,
    }

    #[verify]
    fn test1() -> bool {
        let t = Test::ConA;
        match t {
            Test::ConA => true,
            Test::ConB => false,
        }
    }

    #[verify]
    fn test1_simple() -> bool {
        forall(|v: Test| match v {
            Test::ConA => true,
            Test::ConB => true,
        })
    }

    #[define]
    enum Test2 {
        ConA(bool),
    }

    #[verify]
    fn test2_1() -> bool {
        let t = Test2::ConA(true);
        match t {
            Test2::ConA(b) => b,
        }
    }

    #[falsify]
    fn test2_2() -> bool {
        forall(|t: Test2| {
            match t {
                Test2::ConA(b) => b,
            }
        })
    }

    #[define]
    enum Test3 {
        ConA(usize),
    }

    #[verify]
    fn test3_1() -> bool {
        forall(|n: usize| {
            let t = Test3::ConA(n);
            match t {
                Test3::ConA(b) => b == n,
            }
        })
    }

    #[falsify]
    fn test3_2() -> bool {
        forall(|n: usize, t: Test3| {
            match t {
                Test3::ConA(b) => b == n
            }
        })
    }

    #[verify]
    fn test3_3() -> bool {
        forall(|n: usize, t: Test3| {
            let x = match t {
                Test3::ConA(b) => b
            };
            let y = match t {
                Test3::ConA(b) => b
            };
            x == y
        })
    }

    #[verify]
    fn test3_4() -> bool {
        forall(|n: usize, m: usize| {
            let x = if n == m { n } else { m };
            let y = if n == m { n } else { m };
            x == y
        })
    }
}
