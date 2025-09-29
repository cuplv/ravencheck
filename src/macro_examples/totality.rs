#[crate::check_module(crate)]
#[declare_types(usize)]
#[allow(dead_code)]
mod rvn {
    #[declare]
    type List = Vec<usize>;

    #[declare]
    fn has_length(l: &List, n: usize) -> bool {
        l.len() == n
    }

    // If you remove the #[total] option here, then the
    // 'always_a_length' property fails to verify.
    #[declare]
    #[total]
    fn length(l: &List) -> usize {
        l.len()
    }

    #[assume]
    fn lengths_agree() -> bool {
        forall(|l: List| has_length(l, length(l)))
    }

    #[verify]
    fn always_a_length() -> bool {
        forall(|l: List| exists(|n: usize| has_length(l,n)))
    }

    // We can also use #[total] on a recursive-defined function.

    #[define]
    enum Nat {
        Z,
        S(Box<Nat>),
    }

    #[define]
    enum ListR {
        Nil,
        Cons(usize, Box<ListR>),
    }

    #[declare]
    fn has_length_r(l: &ListR, n: &Nat) -> bool {
        todo!()
    }

    // If you remove the #[total] option here, then the
    // 'always_a_length_r' property fails to verify.
    #[define]
    #[recursive]
    #[total]
    fn length_r(l: &ListR) -> Nat {
        match l {
            ListR::Nil => Nat::Z,
            ListR::Cons(n, l2) => Nat::S(Box::new(length_r(l2)))
        }
    }

    #[assume]
    fn lengths_agree() -> bool {
        forall(|l: ListR| has_length_r(l, length_r(l)))
    }

    #[verify]
    fn always_a_length_r() -> bool {
        forall(|l: ListR| exists(|n: Nat| has_length_r(l,n)))
    }

}
