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
                Opt::<X>::Some(y) => true,
                Opt::<X>::None => false,
            }
        })
    }

    #[falsify]
    fn construct_deconstruct_f2<X: PartialEq>() -> bool {
        forall(|x: X| {
            let maybe_x = Opt::<X>::Some(x);
            match maybe_x {
                Opt::<X>::Some(y) => y == x,
                Opt::<X>::None => true,
            }
        })
    }
}
