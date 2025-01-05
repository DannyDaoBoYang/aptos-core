module 0xCAFE::BasicCoin {

    struct R has key {
        x: u64,
    }

    public fun f(addr: address) acquires R {
        let x_ref = borrow_global_mut<R>(addr);
        x_ref.x = x_ref.x + 1;
    }
    spec f {
        ensures global<R>(addr).x == old(global<R>(addr).x) + 1;
    }

}
