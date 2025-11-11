module 0x82::Test {
    struct R has key {
        x: u64,
        y: u64,
    }
    struct S has key {
        x: u64,
        y: u64,
    }
    struct Y has key {
        x: u64,
    }

    spec module {
        invariant update forall a: address where old(exists<R>(a)):
                global<R>(a).x >= old(global<R>(a).x);
        invariant update forall a: address where old(exists<S>(a)):
                global<S>(a).y > old(global<S>(a).y);
    }

    public fun incr(a: address, b: address, c: bool) acquires R, S{
        let r = borrow_global_mut<R>(a);
        let r2 = borrow_global_mut<S>(b);
        r.x = r.x + 1;
        r2.y = r2.y+1;
    }
}
