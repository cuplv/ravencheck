#[crate::check_module(crate)]
#[declare_types(usize)]
#[allow(dead_code)]
mod rvn {

    enum Test<T> {
        Yes(T),
        No,
    }

    fn testy_test1<X: Clone + PartialEq>(x1: X, x2: X) -> X {
        let maybe = Test::<X>::Yes(x1);
        match maybe {
            Test::<X>::Yes(x) => x,
            Test::<X>::No => x2,
        }
    }

    fn testy_test2<X: Clone + PartialEq>(x1: X, x2: X) -> X {
        let maybe = Test::<X>::Yes(x1);
        match maybe {
            Test::Yes(x) => x,
            Test::No => x2,
        }
    }

    #[define]
    enum OptUsize {
        Some(usize),
        None,
    }

    #[define]
    enum Opt<T> {
        Some(T),
        None,
    }

    #[define]
    #[recursive]
    enum List<T> {
        Cons(T, Box<List<T>>),
        Nil,
    }

    #[falsify]
    fn oops() -> bool { false }

    #[verify]
    fn no_quantify_true() -> bool {
        let maybe_x = Opt::<(bool,bool)>::Some((true, false));
        match maybe_x {
            Opt::<(bool,bool)>::Some(x) => {
                let (t,f) = x;
                t && !f
            }
            Opt::<(bool,bool)>::None => false,
        }
    }

    // #[falsify]
    // fn no_quantify_false() -> bool {
    //     let maybe_x = Opt::<(bool,bool)>::Some((true, false));
    //     match maybe_x {
    //         Opt::<(bool,bool)>::Some(x) => {
    //             let (t,f) = x;
    //             !(t && !f)
    //         }
    //         Opt::<(bool,bool)>::None => true,
    //     }
    // }

    #[verify]
    fn construct_deconstruct_v<X: Clone + PartialEq>() -> bool {
        forall(|x: X| {
            let maybe_x = Opt::<X>::Some(x.clone());
            match maybe_x {
                Opt::<X>::Some(y) => y == x,
                Opt::<X>::None => false,
            }
        })
    }

    #[falsify]
    fn construct_deconstruct_f1<X: PartialEq>() -> bool {
        forall(|x: X| {
            let maybe_x = Opt::<X>::Some(x);
            match maybe_x {
                Opt::<X>::Some(y) => y != x,
                Opt::<X>::None => false,
            }
        })
    }

    #[falsify]
    fn construct_deconstruct_f2<X: PartialEq>() -> bool {
        forall(|x: X| {
            let maybe_x = Opt::<X>::Some(x);
            match maybe_x {
                Opt::<X>::Some(y) => false,
                Opt::<X>::None => true,
            }
        })
    }

    #[verify]
    fn symbolic1() -> bool {
        forall(|l1: List<usize>| {
            match l1 {
                List::<usize>::Cons(n, tail) => n == n,
                List::<usize>::Nil => true,
            }
        })
    }

    #[falsify]
    fn symbolic2() -> bool {
        forall(|l1: List<usize>, l2: List<usize>| {
            match l1 {
                List::<usize>::Cons(n, tail) => n == n && tail == l2,
                List::<usize>::Nil => true,
            }
        })
    }

    #[falsify]
    fn symbolic3() -> bool {
        forall(|l1: List<usize>| {
            match l1 {
                List::<usize>::Cons(n, tail) => {
                    match l1 {
                        List::<usize>::Cons(n, tail) => true,
                        List::<usize>::Nil => true,
                    }
                }
                List::<usize>::Nil => false,
            }
        })
    }

    // #[verify]
    // fn unique1() -> bool {
    //     let l1 = List::<usize>::Nil();
    //     let l2 = List::<usize>::Nil();
    //     l1 == l2
    // }
    // #[verify]
    // fn unique2() -> bool {
    //     forall(|n: usize| {
    //         List::<usize>::Cons(n, List::<usize>::Nil)
    //             == List::<usize>::Cons(n, List::<usize>::Nil)
    //     })
    // }
    // #[verify]
    // fn unique3() -> bool {
    //     forall(|n: usize, l: List<usize>| {
    //         List::<usize>::Cons(n, l)
    //             == List::<usize>::Cons(n, l)
    //     })
    // }
}
