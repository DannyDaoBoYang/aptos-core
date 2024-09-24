module 0xCAFE::BasicCoin {
    struct Coin has key {
        value: u64,
    }
    struct R{
        f1: u64,
        f2: u64
    }

    public fun mint( a:&mut R) {
        a.f1 = 1;
    }
}
