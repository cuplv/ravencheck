#[crate::check_module(crate)]
#[allow(dead_code)]
mod match_exclusion {
    #[define]
    enum Opt<T> {
        Some(T),
        None,
    }

    #[verify]
    fn not_some_and_none<T>(v: Opt<T>) -> bool {
        let some = exists(|t: T| v == Opt::<T>::Some(t));
        let none = v == Opt::<T>::None;
        !(some && none)
    }

    // This is not currently enforced by the constructor axioms.
    #[falsify]
    fn some_or_none<T>(v: Opt<T>) -> bool {
        let some = exists(|t: T| v == Opt::<T>::Some(t));
        let none = v == Opt::<T>::None;
        (some || none)
    }
}
