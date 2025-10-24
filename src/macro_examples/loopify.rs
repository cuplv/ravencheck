#[crate::check_module(crate)]
#[declare_types(String)]
#[allow(dead_code)]
mod rvn {
    #[define]
    #[phantom]
    pub enum Option<T> {
        Some(T),
        None,
    }

    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum List { Nil, Cons(String, Box<List>) }

    fn make_list<S: ToString, const N: usize>(elems: [S; N]) -> List {
        let n = elems.len();
        let mut l = List::Nil;
        for i in (0..n).rev() {
            l = List::Cons(elems[i].to_string(), Box::new(l));
        }
        l
    }

    #[define]
    // (old list, new reversed list)
    type RState = (List, List);

    #[define]
    type More = (String, List);

    #[define]
    fn init(l: List) -> RState {
        (l, List::Nil)
    }

    #[define]
    fn cond(s: &RState) -> Option<More> {
        let (l, _) = s;
        match l {
            List::Nil => Option::<More>::None,
            List::Cons(e, l2) => Option::<More>::Some((e.clone(), *l2.clone())),
        }
    }

    #[define]
    fn step(c: More, s: RState) -> RState {
        let (e, l_in) = c;
        let (_, l_out) = s;
        (l_in, List::Cons(e, Box::new(l_out)))
    }

    #[define]
    fn finish(s: RState) -> List {
        let (_, l_out) = s;
        l_out
    }

    #[loopify(RState, More, init, cond, step, finish)]
    pub fn reverse(l: List) -> List {}
}
