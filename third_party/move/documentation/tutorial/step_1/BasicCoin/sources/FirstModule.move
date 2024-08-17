module 0xCAFE::BasicCoin {
    struct Coin has key {
        value: u64,
    }
    struct R{
        s1: S,
        s2: S,
    }
    struct S{
        f1: u64,
        f2: u64,
    }

    public fun mint(account: signer, value: u64, a:&mut R) {
        move_to(&account, Coin { value });
        a.s2.f1 = 1;
        a.s1.f2 = 2;
    }
}
