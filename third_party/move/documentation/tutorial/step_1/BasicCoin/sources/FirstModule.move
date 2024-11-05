module 0xCAFE::BasicCoin {
    struct S {
        x: u64,
        y: u64,
    }

    struct T has key {
        x: u64,
    }

    struct R has key {
        x: u64,
    }

    struct V<T: store> has key {
        x: u64,
        y: T,
    }

    public fun diff_resource_generic<A: store, B: store>(cond: bool, a: address) acquires V {
        let x = if (cond) {
            let t1 = borrow_global_mut<V<A>>(a);
            &mut t1.x
        } else {
            let t2 = borrow_global_mut<V<B>>(a);
            &mut t2.x
        };
        *x = 0;
    }

    spec diff_resource_generic {
        aborts_if cond && !exists<V<A>>(a);
        aborts_if !cond && !exists<V<B>>(a);
        ensures if (cond) global<V<A>>(a).x == 0 else global<V<B>>(a).x == 0;
    }
}
