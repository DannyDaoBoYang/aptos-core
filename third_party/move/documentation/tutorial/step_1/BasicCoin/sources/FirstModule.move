module 0xCAFE::BasicCoin {
    struct Coin has key {
        value: u64
    }
    struct R{
        f1: u64,
        f2: R2
    }
    struct R2{
        f1: u64,
        f2: u64
    }
    public fun mint( a:&mut R) {
        a.f2.f1 = 1;
    }
}
