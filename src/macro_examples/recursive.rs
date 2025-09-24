#[crate::check_module(crate)]
#[declare_types(usize)]
#[allow(dead_code)]
mod rvn {
    #[declare]
    type List<E> = Vec<E>;

    #[declare]
    fn empty_list<E>() -> List<E> { Vec::new() }

    #[declare]
    fn cons<E>(e: E, mut l: List<E>) -> List<E> {
        l.push(e);
        l
    }

    #[declare]
    fn uncons<E>(e: E, mut l: List<E>) -> (E, List<E>) {
        match l.pop() {
            Some(e1) => (e1, l),
            None => (e, l),
        }
    }

    #[define]
    #[recursive]
    fn concat<E>(e_def: E, l1: List<E>, l2: List<E>) -> List<E>
    where E: Clone + PartialEq
    {
        if l1 == empty_list::<E>() {
            l2
        } else {
            let (e, l1_tail) = uncons::<E>(e_def.clone(), l1);
            cons(e, concat::<E>(e_def, l1_tail, l2))
        }
    }

    #[annotate(concat::<T>(e, l1, l2) => l3)]
    fn left_empty() -> bool {
        implies(
            l1 == empty_list::<E>(),
            l3 == l2,
        )
    }

    #[annotate(concat::<T>(e, l1, l2) => l3)]
    fn right_empty() -> bool {
        implies(
            l2 == empty_list::<E>(),
            l3 == l1,
        )
    }
}
