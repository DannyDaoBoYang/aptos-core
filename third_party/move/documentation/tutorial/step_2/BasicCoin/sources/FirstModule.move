module 0x82::Test {
    struct R has key {
        x: u64,
    }
    struct Y has key {
        x: u64,
    }

    spec module {
        invariant update forall a: address where exists<R>(a):
                global<R>(a).x == old(global<R>(a).x) + 1;
    }

    public fun incr(a: address) acquires R{
        let r = borrow_global_mut<R>(a);
        r.x = r.x + 1;
    }
}
