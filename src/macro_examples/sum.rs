#[crate::check_module(crate)]
#[declare_types(usize)]
#[allow(dead_code)]
mod rvn {

    #[define]
    enum OptionUsize {
        Some(usize),
        None,
    }

    #[define]
    enum Option<T> {
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
}
