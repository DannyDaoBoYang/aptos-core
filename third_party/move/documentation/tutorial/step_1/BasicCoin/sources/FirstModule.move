module 0x42::Test {
    struct R has key{
        v1: u64,
        v2: u64
    }
    spec module {
        invariant update forall addr: address where old(exists<R>(addr)): exists<R>(addr);
    }
    fun bor(a: address, b: address, p1: bool, p2: bool) acquires R {
        let c = if (p2) borrow_global_mut<R>(a) else borrow_global_mut<R>(a);
        c.v1 = c.v1+1;
    }
}
