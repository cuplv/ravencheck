#[ravencheck::check_module]
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

    #[declare]
    pub fn key_val(m: &MyMap, key: u32, val: u32) -> bool {
        match m.get(&key) {
            Some(v) => v == &val,
            None => false,
        }
    }

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

    // // Ideally we would write this axiom, but it would create a
    // // sort cycle.
    //
    // #[assume]
    // pub fn key_null_complete(m: MyMap, key: u32) -> bool {
    //     key_null(m, key) ==
    //         forall(|val: u32| !key_val(m, key, val))
    // }

    // So we define this half-measure axiom instead.
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
}
