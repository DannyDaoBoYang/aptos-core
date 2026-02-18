module BasicCoin::ProphecyBenchmark3Levels {
    /// Struct A with field x
    public struct A has key {
        x: u64,
    }

    /// Struct B with field y
    public struct B has key {
        y: u64,
    }

    /// Global invariant ensuring A.x >= B.y
    spec module {
        invariant [global] forall a: address where exists<A>(a) && exists<B>(a): global<A>(a).x >= global<B>(a).y;
    }

    /// Main function demonstrating global invariant checking
    public fun main(addr: address) acquires A, B {
        let mut_a = borrow_global_mut<A>(addr);
        let mut_b = borrow_global_mut<B>(addr); // B gets borrowed here.
        mut_b.y = 0;
        mut_a.x = 10;
        // <--- mut_a usage ends here. Implicit Writeback of A.
        // This triggers the Invariant Check for A while B is still borrowed.
        mut_b.y = 9;
        // <--- mut_b usage ends here. Implicit Writeback of B.
    }
}
