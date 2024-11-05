module 0xCAFE::BasicCoin {
    struct S has drop{
        x: u64,
        y: u64,
    }
    public fun ib (a: &mut S): &mut u64{
        return &mut a.x
    }
    public fun mint(value1: S, value2: S, cond: bool) {
        let x = if (cond) {
            ib(&mut value1)
        } else {
            &mut value2.y
        };
        *x = 0;
    }
}
