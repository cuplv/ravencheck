#[ravencheck::export_module]
#[allow(dead_code)]
mod heap {
    pub const PTR_MAX: usize = 1024;

    #[declare]
    #[derive(Copy, Clone, Eq, PartialEq, Hash)]
    pub struct Ptr(usize);

    #[declare]
    pub type Val = u8;

    impl Ptr {
        pub fn new(n: usize) -> Option<Self> {
            if n < PTR_MAX { Some(Self(n)) } else { None }
        }
    }

    #[declare]
    pub struct Heap(Box<[u8; PTR_MAX]>);

    #[declare]
    #[total]
    pub fn get(h: &Heap, n: Ptr) -> Val {
        h.0[n.0]
    }

    #[declare]
    pub fn set(mut h: Heap, p: Ptr, v: Val) -> Heap {
        h.0[p.0] = v;
        h
    }

    #[assume]
    pub fn set_get(h: Heap, a: Ptr, b: Ptr, v: Val, w: Val) -> bool {
        get(set(h, b, w), a) == if a == b { w } else { get(h, a) }
    }
}

#[ravencheck::check_module]
#[allow(dead_code, unused_imports)]
mod swap {
    #[import]
    use crate::heap::heap::*;

    #[define]
    pub fn swap(h: Heap, a: Ptr, b: Ptr) -> Heap {
        let a_v = get(&h, a);
        let b_v = get(&h, b);
        let h2 = set(h, a, b_v);
        set(h2, b, a_v)
    }
    
    #[define]
    #[phantom]
    pub fn contains_l(h: Heap, v: Val) -> bool {
        exists(|a: Ptr| get(h, a) == v)
    }

    #[verify]
    pub fn prop1(h1: Heap, a: Ptr, b: Ptr) -> bool {
        let h2 = swap(h1, a, b);
        forall(|v: Val| {
            contains_l(h1, v) == contains_l(h2, v)
        })
    }
}
