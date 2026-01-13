// Here is a module that wraps HashMap<u32, u32> for use in Ravencheck
// code.  We'll add axioms below.
#[ravencheck::export_module]
#[declare_types(u32, HashMap<_>)]
#[allow(dead_code)]
mod map_with_null_check {
    use std::collections::HashMap;

    #[declare]
    type MyMap = HashMap<u32, u32>;

    #[declare]
    pub fn empty_map() -> MyMap {
        HashMap::new()
    }

    // key_val checks whether the given key has the given val.
    #[declare]
    pub fn key_val(m: &MyMap, key: u32, val: u32) -> bool {
        match m.get(&key) {
            Some(v) => v == &val,
            None => false,
        }
    }

    // key_null checks whether the given key has no val.
    #[declare]
    pub fn key_null(m: &MyMap, key: u32) -> bool {
        match m.get(&key) {
            None => true,
            Some(_v) => false,
        }
    }

    #[declare]
    pub fn insert(mut m: MyMap, key: u32, val: u32) -> MyMap {
        m.insert(key, val);
        m
    }

    #[declare]
    pub fn remove(mut m: MyMap, key: u32) -> MyMap {
        m.remove(&key);
        m
    }
}

// Based on its implementation, we know that key_null is true if and
// only if key_val is false for all keys.
//
// Ideally, we would give Ravencheck a *complete* axiom that fully
// captures this.  Unfortunately, this axiom creates a sort cycle, and
// so we will need to replace it with the *incomplete* axioms below.
#[ravencheck::check_module]
// Verification for this module will fail with the following error
// message.
#[rvn_should_panic("Cannot check 'prop1': sort cycle self-loop ⤷ u32 ⤴")]
#[allow(unused_imports)]
mod complete_null_check_axiom {
    #[import]
    use crate::incomplete_map::map_with_null_check::*;

    #[assume]
    pub fn key_null_complete(m: MyMap, key: u32) -> bool {
        // Because 'forall' is used in an equation, it counts as both
        // a 'forall' and an 'exists' quantifier when considering sort
        // edges.  Using this 'exists(u32)' quantifier within a
        // condition that forall-quantifies a u32 (key) creates a sort
        // cycle.
        //
        // If the key and val were different types, this would create
        // a sort edge Key->Val, but would not create a cycle on its
        // own.
        key_null(m, key) ==
            forall(|val: u32| !key_val(m, key, val))
    }

    // Due to the sort cycle, we can't verify a property like this.
    #[verify]
    pub fn prop1(m: MyMap, key: u32) -> bool {
        key_null(m, key) || exists(|val: u32| key_val(m, key, val))
    }
}

#[ravencheck::check_module]
#[allow(unused_imports)]
mod incomplete_axioms {
    #[import]
    use crate::incomplete_map::map_with_null_check::*;

    // We can't have the 'key_null_complete' axiom, but this one is
    // fine.  This means that, when 'key_val' is true for some key, we
    // can verify that 'key_null' will be false.  But when 'key_val'
    // is not true for any key, it is unknown whether 'key_null' will
    // be true or false (for an arbitrary map).
    #[assume]
    pub fn key_null_incomplete(m: MyMap, key: u32, val: u32) -> bool {
        !(key_val(m, key, val) && key_null(m, key))
    }

    // As a result, we can't verify properties like this.
    #[falsify]
    pub fn no_middle(m: MyMap, key: u32) -> bool {
        key_null(m, key) ||
            exists(|val: u32| key_val(m, key, val))
    }

    // But we can verify things like this.
    #[verify]
    pub fn val_means_not_null(m: MyMap, key: u32, val: u32) -> bool {
        implies(
            key_null(m, key),
            !key_val(m, key, val),
        )
    }

    // Note that, for a specific map like the 'empty_map', we can
    // still speak with certainly about 'key_null' without using
    // quantifiers, and thus without creating sort cycles.
    #[assume]
    pub fn key_null_empty(key: u32) -> bool {
        key_null(empty_map(), key)
    }

    // Likewise, we can still write axioms that say 'insert' preserves
    // 'key_null' for other keys, and 'remove' introduces 'key_null'
    // for the given key.
}
