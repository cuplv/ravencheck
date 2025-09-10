#[crate::export_module(crate)]
#[declare_types(u32)]
#[allow(dead_code)]
pub mod my_nat_mod {
    use std::marker::PhantomData;

    #[declare]
    #[derive(Copy,Clone,PartialEq,Eq,Hash)]
    pub struct Nat<T>{
        value: usize,
        tag: PhantomData<T>,
    }

    impl<T> Nat<T> {
        pub fn new(n: usize) -> Nat<T> {
            Nat { value: n, tag: PhantomData }
        }
    }

    #[declare]
    pub fn zero<T>() -> Nat<T> { Nat::new(0) }

    #[declare]
    pub fn le<T>(a: Nat<T>, b: Nat<T>) -> bool {
        a.value <= b.value
    }

    #[assume((Nat<T>, T))]
    fn le_refl<T>() -> bool {
        forall(|x: Nat<T>| le::<T>(x,x))
    }

    #[define]
    pub fn lt<T>(a: Nat<T>, b: Nat<T>) -> bool
    where T: std::cmp::Eq + Copy
    {
        le::<T>(a,b) && a != b
    }

    #[define]
    pub fn ge<T>(a: Nat<T>, b: Nat<T>) -> bool
    {
        le::<T>(b,a)
    }

    #[define]
    pub fn gt<T>(a: Nat<T>, b: Nat<T>) -> bool
    where T: std::cmp::Eq + Copy
    {
        ge::<T>(a,b) && a != b
    }

    #[declare]
    pub fn dec<T>(a: Nat<T>) -> Nat<T> {
        if a.value == 0 {
            Nat::new(0)
        } else {
            Nat::new(a.value - 1)
        }
    }

    #[declare]
    pub fn inc<T>(a: Nat<T>) -> Nat<T> {
        Nat::new(a.value + 1)
    }

    #[assume((Nat<T>, T))]
    fn inc_dec<T>() -> bool {
        forall(|a: Nat<T>| {
            implies(
                a != zero::<T>(),
                inc::<T>(dec::<T>(a)) == a
            )
        })
    }

    #[define_rec]
    pub fn add<T>(a: Nat<T>, b: Nat<T>) -> Nat<T>
    where T: std::cmp::Eq + Copy
    {
        if a == zero::<T>() {
            b
        } else {
            inc::<T>(
                add::<T>(dec::<T>(a), b)
            )
        }
    }

    #[annotate(add)]
    fn add_trivial<T>() -> bool {
        |a: Nat<T>, b: Nat<T>|
        |c: Nat<T>|
        true
    }

    // #[annotate(add)]
    // fn add_monotonic<T>() -> bool {
    //     |a: Nat<T>, b: Nat<T>|
    //     |c: Nat<T>|
    //     le::<T>(a,c) && le::<T>(a,b)
    // }

    #[annotate(add)]
    fn add_zeros<T>() -> bool {
        |a: Nat<T>, b: Nat<T>|
        |c: Nat<T>|
        implies(a == zero::<T>(), b == c)
        && implies(b == zero::<T>(), a == c)
    }

    #[verify]
    fn simple_zeros() -> bool {
        add::<u32>(zero::<u32>(), zero::<u32>()) == zero::<u32>()
    }
}
