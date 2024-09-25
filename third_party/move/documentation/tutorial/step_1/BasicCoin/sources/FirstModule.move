module 0xCAFE::BasicCoin {
    struct Coin has key {
        value: u64,
    }
    struct R{
        f1: u64,
        f2: u64
    }
    spec mint(a:&mut R){
        aborts_if a.f1>=5;
    }
    public fun mint( a:&mut R) {
        a.f1 = 6;
        if (a.f1 >= 5) {
            abort 0;  // Aborts with custom error code
        };
    }
}
