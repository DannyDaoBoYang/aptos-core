module 0x82::Test {
    struct R has key {
        x: u64,
    }
    struct Y has key {
        x: u64,
    }

    spec module {
        invariant forall a: address where exists<R>(a):
            a == @0x0;
        invariant forall b: address where exists<Y>(b):
            b == @0x30;
        invariant forall a: address where exists<R>(a):
            forall b: address where exists<Y>(b):
                global<R>(a).x >= global<Y>(b).x;
    }

    public fun incr(a: address, b:address) acquires R, Y{
        let r = borrow_global_mut<R>(a);
        r.x = r.x + 1;
        //write back to R happense here
        //Invariant Checks injected here

        let r2 = borrow_global_mut<Y>(b);
        r2.x = r2.x + 1;
        //write back to Y happense here
        //Invariant Checks injected here
    }
    public fun incr2(a: address, b:address) acquires R, Y{
        let r = borrow_global_mut<R>(a);
        let r2 = borrow_global_mut<Y>(b);
        r.x = r.x + 1;
        //write back to R happense here
        //Invariant injected here
        r2.x = r2.x + 1;
    }
    public fun incr2(a: address, b:address) acquires R, Y{
        let r2 = borrow_global_mut<Y>(b);
        let r = borrow_global_mut<R>(a);
        r.x = r.x + 1;
        r2.x = r2.x + 1;
    }
}
