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

    #[define]
    fn cons_twice<E: Clone>(e: E, l: List<E>) -> List<E> {
        cons::<E>(e.clone(), cons::<E>(e, l))
    }

    #[verify]
    fn cons_twice_def<E>() -> bool {
        forall(|e: E, l: List<E>| {
            cons_twice::<E>(e, l)
                == cons::<E>(e, cons::<E>(e, l))
        })
    }

    #[falsify]
    fn cons_twice_fal<E>() -> bool {
        forall(|e: E, l: List<E>| {
            cons_twice::<E>(e, l)
                != cons::<E>(e, cons::<E>(e, l))
        })
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
            cons::<E>(e, concat::<E>(e_def, l1_tail, l2))
        }
    }

    #[annotate(concat::<T>(e, l1, l2) => l3)]
    fn left_empty() -> bool {
        implies(
            l1 == empty_list::<T>(),
            l3 == l2,
        )
    }

    #[verify]
    fn from_left_empty<E>() -> bool {
        forall(|e_def: E, l2: List<E>| {
            concat::<E>(e_def, empty_list::<E>(), l2) == l2
        })
    }

    #[annotate(concat::<T>(e, l1, l2) => l3)]
    fn right_empty() -> bool {
        implies(
            l2 == empty_list::<T>(),
            l3 == l1,
        )
    }
}
