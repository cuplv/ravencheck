#[crate::check_module(crate)]
#[declare_types(u32)]
#[rvn_should_panic("sort cycle self-loop ⤷ u32 ⤴")]
mod cycle1 {
    #[verify]
    fn exists_forall() -> bool {
        exists(|a: u32| forall(|b: u32| a == b))
    }
}

#[crate::check_module(crate)]
#[declare_types(u16, u32, u64)]
#[rvn_should_panic("sort cycle ⤷ u16 → u32 → u64 ⤴")]
mod cycle2 {
    #[verify]
    fn exists_forall_chain() -> bool {
        exists(|a: u16| forall(|b: u32| true))
            && exists(|a: u32| forall(|b: u64| true))
            && exists(|a: u64| forall(|b: u16| true))
    }
}

#[crate::check_module(crate)]
#[declare_types(u16, u32, u64)]
mod non_cycle3 {
    #[verify]
    fn exists_forall_chain() -> bool {
        exists(|a: u16| forall(|b: u32| true))
            && exists(|a: u32| forall(|b: u64| true))
            && exists(|a: u16| forall(|b: u64| true))
    }
}

#[crate::check_module(crate)]
#[declare_types(u16, u32)]
#[rvn_should_panic("sort cycle ⤷ u16 → u32 ⤴")]
mod eq_cycle4 {
    #[verify]
    fn uses_eq() -> bool {
        let x = exists(|a: u16| {
            true == exists(|b: u32| false)
        });
        let y = exists(|a: u32| {
            true == forall(|b: u16| false)
        });
        x && y
    }
}

#[crate::check_module(crate)]
#[declare_types(u16, u32)]
#[rvn_should_panic("sort cycle ⤷ u16 → u32 ⤴")]
mod eq_cycle5 {
    #[verify]
    fn uses_eq_nested() -> bool {
        let x = exists(|a: u16| {
            true == exists(|b: u32| false)
        });
        let y = exists(|a: u32| {
            true == forall(|b: u16| false)
        });
        x == y
    }
}

#[crate::check_module(crate)]
#[declare_types(u16, u32)]
mod non_eq_cycle5 {
    #[falsify]
    fn uses_eq_but_no_cycle() -> bool {
        let x = exists(|a: u16| {
            true == exists(|b: u32| false)
        });
        let y = exists(|a: u16| {
            true == forall(|b: u32| false)
        });
        x && !y
    }
}

#[crate::check_module(crate)]
#[declare_types(u16, u32)]
mod non_ite_cycle6 {
    #[falsify]
    fn uses_eq_but_no_cycle() -> bool {
        let x = exists(|b: u32| false);
        forall(|y: u32| if x { true } else { false})
    }
}

#[crate::check_module(crate)]
#[declare_types(u16, u32)]
#[rvn_should_panic("sort cycle self-loop ⤷ u32 ⤴")]
mod ite_cycle7 {
    #[falsify]
    fn uses_eq_but_no_cycle() -> bool {
        let x = exists(|b: u32| false);
        exists(|y: u32| if x { true } else { false})
    }
}
