/// This module defines a finite-sized array type `Heap`, an
/// associated in-bounds pointer type `Ptr`, and `get` and `set`
/// operations that use them.
///
/// `get` and `set` are axiomatized by [`get_set`].
///
/// In the `swap` module below, we will define and verify a new
/// function on heaps using this interface.
///
/// The `ravencheck::export_module` attribute makes declared functions
/// and axioms in this module visible to other modules that import it.
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
        /// Construct a new in-bounds pointer.  Returns `None` if
        /// given `usize` is not in-bounds.
        pub fn new(n: usize) -> Option<Self> {
            if n < PTR_MAX { Some(Self(n)) } else { None }
        }
    }

    #[declare]
    pub struct Heap(pub Box<[u8; PTR_MAX]>);

    impl Heap {
        pub fn new(v_init: Val) -> Self {
            Self(Box::new([v_init; PTR_MAX]))
        }
    }

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

    /// This is assumed as a trusted axiom.  Ravencheck cannot see the
    /// bodies of functions `get` or `set`, since they use #[declare].
    #[assume]
    pub fn set_get(h: Heap, a: Ptr, b: Ptr, v: Val, w: Val) -> bool {
        get(set(h, b, w), a) == if a == b { w } else { get(h, a) }
    }
}

/// In this module, we define a `swap` function on heaps and verify a
/// safety property for it.
///
/// Our goal is to show that `swap` preserves all values: if a value
/// is somewhere in the heap before a swap, then it is still somewhere
/// in the heap after the swap.  We can try to establish this property
/// using normal unit tests, but it's difficult to make them cover
/// enough cases to be useful.  So, we'll add Ravencheck verification.
#[ravencheck::check_module]
#[allow(dead_code, unused_imports)]
mod swap {
    #[import]
    use crate::heap::heap::*;

    /// Swaps the values at two given positions in the given heap.
    ///
    /// The body of `swap` is visible to Ravencheck, since we used
    /// `#[define]`.
    #[define]
    pub fn swap(h: Heap, a: Ptr, b: Ptr) -> Heap {
        let a_v = get(&h, a);
        let b_v = get(&h, b);
        let h2 = set(h, a, b_v);
        set(h2, b, a_v)
    }

    /// This function checks that a value is present at some index in
    /// the heap.  We'll just use it in tests.
    #[cfg(test)]
    fn contains_t(h: &Heap, v: Val) -> bool {
        h.0.iter().any(|v1| *v1 == v)
    }

    /// This tests one example of swapping two values in an array.
    #[test]
    fn swap_preserves_t1() {
        let h = set(Heap::new(0), Ptr::new(5).unwrap(), 1);
        let h2 = swap(h, Ptr::new(5).unwrap(), Ptr::new(7).unwrap());
        assert!(
            contains_t(&h2, 1)
        );
    }

    /// This tests one more example.
    #[test]
    fn swap_preserves_t2() {
        let h = set(Heap::new(0), Ptr::new(99).unwrap(), 3);
        let h2 = swap(h, Ptr::new(5).unwrap(), Ptr::new(7).unwrap());
        assert!(
            contains_t(&h2, 3)
        );
    }

    /// For Ravencheck verification, we'll define a logical/symbolic
    /// version of `contains_t`.  Here, `contains(h, v)` is true when
    /// `v` is present at some index in `h`.
    #[define]
    // We use `phantom` to make this function only exist at
    // verification time.  It can't be compiled into a runnable
    // binary, since it contains a quantifier.
    #[phantom]
    fn contains(h: Heap, v: Val) -> bool {
        exists(|a: Ptr| get(h, a) == v)
    }

    /// This goal verifies that `swap` does not remove any value from
    /// the heap.  If the old heap `contains` the value, then the new,
    /// post-swap heap also `contains` the value.
    ///
    /// Unlike the tests above, this #[verify] goal checks the
    /// property for *all* heaps, pointers, and values.
    ///
    /// #[verify] items only exist at verification time: they are not
    /// passed to the Rust toolchain.
    #[verify]
    fn swap_preserves(h1: Heap, a: Ptr, b: Ptr) -> bool {
        let h2 = swap(h1, a, b);
        // Arguments to a #[verify] function are all universally
        // quantified (`h1`, `a`, and `b`).  We use the `forall`
        // operator to explicitly quantify `v` below, but we could
        // also move `v` to the function arguments above.
        forall(|v: Val| {
            contains(h1, v) == contains(h2, v)
        })
    }
}
