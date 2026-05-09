module BasicCoin::ProphecyBenchmark2Levels {

    // ==========================================
    // 1. DATA STRUCTURES (Levels 1-2)
    // ==========================================

    // Level 1: Leaf Node (8 integers)
    struct Node1 has copy, drop, store {
        v0: u64, v1: u64, v2: u64, v3: u64, 
        v4: u64, v5: u64, v6: u64, v7: u64,
    }

    // Level 2: Root Node (8 Node1s)
    struct Node2 has copy, drop, store {
        v0: Node1, v1: Node1, v2: Node1, v3: Node1, 
        v4: Node1, v5: Node1, v6: Node1, v7: Node1,
    }

    // ==========================================
    // 2. CONSTRUCTORS
    // ==========================================

    public fun new_node1(): Node1 {
        Node1 { v0: 0, v1: 0, v2: 0, v3: 0, v4: 0, v5: 0, v6: 0, v7: 0 }
    }

    public fun new_node2(): Node2 {
        Node2 { 
            v0: new_node1(), v1: new_node1(), v2: new_node1(), v3: new_node1(), 
            v4: new_node1(), v5: new_node1(), v6: new_node1(), v7: new_node1() 
        }
    }

    // ==========================================
    // 3. SELECTION HELPERS (With Inline Specs)
    // ==========================================

    // Step 1: Root (Node2) -> Child (Node1)
    fun select_n1(n: &mut Node2, idx: u64): &mut Node1 {
        if (idx == 0) { &mut n.v0 } else if (idx == 1) { &mut n.v1 }
        else if (idx == 2) { &mut n.v2 } else if (idx == 3) { &mut n.v3 }
        else if (idx == 4) { &mut n.v4 } else if (idx == 5) { &mut n.v5 }
        else if (idx == 6) { &mut n.v6 } else { &mut n.v7 }
    }
    spec select_n1 { 
        pragma opaque = false; // Force inline
        pragma verify = false; // Skip isolated verification
    }

    // Step 2: Child (Node1) -> Leaf (u64)
    fun select_leaf(n: &mut Node1, idx: u64): &mut u64 {
        if (idx == 0) { &mut n.v0 } else if (idx == 1) { &mut n.v1 }
        else if (idx == 2) { &mut n.v2 } else if (idx == 3) { &mut n.v3 }
        else if (idx == 4) { &mut n.v4 } else if (idx == 5) { &mut n.v5 }
        else if (idx == 6) { &mut n.v6 } else { &mut n.v7 }
    }
    spec select_leaf { 
        pragma opaque = false; 
        pragma verify = false; 
    }

    // ==========================================
    // 4. MAIN BENCHMARK FUNCTION
    // ==========================================

    public fun benchmark_from_scratch(
        c2: u64, c1: u64
    ): Node2 {
        let root = new_node2();
        
        let idx2 = c2 % 8;
        let idx1 = c1 % 8;

        let n2_ref = &mut root;
        
        // Borrow Chain: Node2 -> Node1 -> u64
        let n1_ref = select_n1(n2_ref, idx2);
        let leaf_ref = select_leaf(n1_ref, idx1);

        *leaf_ref = *leaf_ref + 1;

        root
    }
    spec new_node1 {
        pragma opaque = false;
    }
    spec new_node2 {
        pragma opaque = false;
    }
    spec benchmark_from_scratch {
        pragma opaque = false;

        // Path: root.v0.v0
        
        // 1. Exact path match
        ensures (c2==0 && c1==0) 
            ==> result.v0.v0 == 1;
        ensures (c2==1 && c1==1) 
            ==> result.v1.v1 == 1;
        // 3. Bound check
        ensures result.v0.v0 <= 1;
    }
}
