#[crate::check_module(crate)]
#[allow(dead_code)]
mod induction {
    #[annotate]
    fn true_is_true() -> bool {
        true == true
    }

    #[annotate]
    #[should_fail]
    fn true_is_false() -> bool {
        true == false
    }

    #[define]
    enum Nat { Z, S(Box<Nat>) }

    #[annotate]
    fn z_is_z() -> bool {
        Nat::Z == Nat::Z
    }

    #[annotate]
    #[should_fail]
    fn z_is_s() -> bool {
        Nat::Z == Nat::S(Nat::Z)
    }

    #[annotate]
    #[inductive(x: Nat)]
    fn z_is_zi() -> bool {
        Nat::Z == Nat::Z
    }

    #[annotate]
    #[inductive(x: Nat)]
    #[should_fail]
    fn z_is_si() -> bool {
        Nat::Z == Nat::S(x)
    }
    
    #[define]
    #[recursive]
    fn add(x: Nat, y: Nat) -> Nat {
        match x {
            Nat::Z => y,
            Nat::S(x_sub) => Nat::S(Box::new(add(*x_sub, y))),
        }
    }

    #[annotate]
    #[inductive(x: Nat, y: Nat)]
    fn factor_s_right_good() -> Bool {
        add(x,Nat::S(y)) == Nat::S(add(x,y))
    }

    // This makes use of the previous #[annotate] property, which has
    // now been assumed.
    #[verify]
    fn check_factor_s_right(x: Nat, y: Nat) -> bool {
        add(x,Nat::S(y)) == Nat::S(add(x,y))
    }

    #[annotate]
    #[inductive(x: Nat, y: Nat)]
    #[should_fail]
    fn factor_s_right_oops() -> Bool {
        // This line uses != in place of ==
        add(x,Nat::S(y)) != Nat::S(add(x,y))
    }

    #[annotate]
    #[inductive(x: Nat, y: Nat, z: Nat)]
    #[should_fail]
    fn prop_0() -> bool {
        // Should obviously fail.
        add(y,y) == add(z,z)
    }

    #[annotate]
    #[inductive(x: Nat)]
    #[should_fail]
    fn prop_1() -> bool {
        // Here is a second version that should fail, which quantifies
        // y and z in a different way.
        forall(|y: Nat, z: Nat| {
            add(y,y) == add(z,z)
        })
    }
}

#[crate::check_module(crate)]
#[allow(dead_code)]
#[declare_types(u32)]
mod polymorphic_annotate {
    #[define]
    enum List<T> {
        Nil,
        Cons(T, Box<List<T>>),
    }

    #[verify]
    fn nil_is_nil<T>() -> bool {
        List::<T>::Nil == List::<T>::Nil
    }

    #[annotate]
    #[inductive(l: List<T>)]
    #[for_type(List<E> => <E>)]
    fn cons_ne_base<T>(t: T) -> bool {
        List::<T>::Cons(t, l) != l
    }
}

#[crate::check_module(crate)]
#[allow(dead_code)]
#[declare_types(u32)]
#[rvn_should_panic("only enum types should be used in #[inductive(..)], but you used u32 for property cons_ne_base")]
mod induct_non_enum {
    #[define]
    enum List<T> {
        Nil,
        Cons(T, Box<List<T>>),
    }

    #[annotate]
    #[inductive(l: List<T>, x: u32)]
    #[for_type(List<E> => <E>)]
    fn cons_ne_base<T>(t: T) -> bool {
        List::<T>::Cons(t, l) != l
    }
}

#[crate::check_module(crate)]
#[allow(dead_code)]
mod induct_instantiations {
    #[define]
    enum Nat { Z, S(Box<Nat>) }

    #[declare]
    fn inside_1(n: Nat) -> Nat {
        n
    }

    #[declare]
    fn inside_2(n: Nat) -> Nat {
        n
    }

    #[define]
    #[recursive]
    fn outside_1(n: Nat) -> Nat {
        inside_1(n)
    }

    #[define]
    #[recursive]
    fn outside_2(n: Nat) -> Nat {
        inside_2(n)
    }

    #[annotate]
    #[inductive(n: Nat)]
    #[should_fail]
    fn prop1() -> bool {
        let _ = outside_1(n);

        outside_2(n) == n
    }
}
