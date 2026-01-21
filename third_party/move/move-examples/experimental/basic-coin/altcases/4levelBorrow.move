module BasicCoin::ProphecyBenchmark4Levels {

    // ==========================================
    // 1. DATA STRUCTURES (Levels 1-4)
    // ==========================================

    struct Node1 has copy, drop, store {
        v0: u64, v1: u64, v2: u64, v3: u64, 
        v4: u64, v5: u64, v6: u64, v7: u64,
    }

    struct Node2 has copy, drop, store {
        v0: Node1, v1: Node1, v2: Node1, v3: Node1, 
        v4: Node1, v5: Node1, v6: Node1, v7: Node1,
    }

    struct Node3 has copy, drop, store {
        v0: Node2, v1: Node2, v2: Node2, v3: Node2, 
        v4: Node2, v5: Node2, v6: Node2, v7: Node2,
    }

    // New Root
    struct Node4 has copy, drop, store {
        v0: Node3, v1: Node3, v2: Node3, v3: Node3, 
        v4: Node3, v5: Node3, v6: Node3, v7: Node3,
    }

    // ==========================================
    // 2. CONSTRUCTORS
    // ==========================================

    public fun new_node1(): Node1 {
        Node1 { v0: 0, v1: 0, v2: 0, v3: 0, v4: 0, v5: 0, v6: 0, v7: 0 }
    }
    public fun new_node2(): Node2 {
        Node2 { v0: new_node1(), v1: new_node1(), v2: new_node1(), v3: new_node1(), v4: new_node1(), v5: new_node1(), v6: new_node1(), v7: new_node1() }
    }
    public fun new_node3(): Node3 {
        Node3 { v0: new_node2(), v1: new_node2(), v2: new_node2(), v3: new_node2(), v4: new_node2(), v5: new_node2(), v6: new_node2(), v7: new_node2() }
    }
    public fun new_node4(): Node4 {
        Node4 { v0: new_node3(), v1: new_node3(), v2: new_node3(), v3: new_node3(), v4: new_node3(), v5: new_node3(), v6: new_node3(), v7: new_node3() }
    }

    // ==========================================
    // 3. SELECTION HELPERS (With Inline Specs)
    // ==========================================

    // Start borrowing from Node4 -> Node3
    fun select_n3(n: &mut Node4, idx: u64): &mut Node3 {
        if (idx == 0) { &mut n.v0 } else if (idx == 1) { &mut n.v1 }
        else if (idx == 2) { &mut n.v2 } else if (idx == 3) { &mut n.v3 }
        else if (idx == 4) { &mut n.v4 } else if (idx == 5) { &mut n.v5 }
        else if (idx == 6) { &mut n.v6 } else { &mut n.v7 }
    }
    spec select_n3 { 
        pragma opaque = false; 
        pragma verify = false; 
    }

    // Node3 -> Node2
    fun select_n2(n: &mut Node3, idx: u64): &mut Node2 {
        if (idx == 0) { &mut n.v0 } else if (idx == 1) { &mut n.v1 }
        else if (idx == 2) { &mut n.v2 } else if (idx == 3) { &mut n.v3 }
        else if (idx == 4) { &mut n.v4 } else if (idx == 5) { &mut n.v5 }
        else if (idx == 6) { &mut n.v6 } else { &mut n.v7 }
    }
    spec select_n2 { 
        pragma opaque = false; 
        pragma verify = false; 
    }

    // Node2 -> Node1
    fun select_n1(n: &mut Node2, idx: u64): &mut Node1 {
        if (idx == 0) { &mut n.v0 } else if (idx == 1) { &mut n.v1 }
        else if (idx == 2) { &mut n.v2 } else if (idx == 3) { &mut n.v3 }
        else if (idx == 4) { &mut n.v4 } else if (idx == 5) { &mut n.v5 }
        else if (idx == 6) { &mut n.v6 } else { &mut n.v7 }
    }
    spec select_n1 { 
        pragma opaque = false; 
        pragma verify = false; 
    }

    // Node1 -> u64 (Leaf)
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
        c4: u64, c3: u64, c2: u64, c1: u64
    ): Node4 {
        let root = new_node4();
        
        let idx4 = c4 % 8;
        let idx3 = c3 % 8;
        let idx2 = c2 % 8;
        let idx1 = c1 % 8;

        let n4_ref = &mut root;
        // The chain now starts at n4
        let n3_ref = select_n3(n4_ref, idx4);
        let n2_ref = select_n2(n3_ref, idx3);
        let n1_ref = select_n1(n2_ref, idx2);
        let leaf_ref = select_leaf(n1_ref, idx1);

        *leaf_ref = *leaf_ref + 1;

        root
    }

    spec benchmark_from_scratch {
        pragma opaque = false;
        
        // Assertions adjusted for 4 levels depth
        ensures (c4==0 && c3==0 && c2==0 && c1==0) 
            ==> result.v0.v0.v0.v0 == 1;

        ensures (c4!=0 || c3!=0 || c2!=0 || c1!=0) 
            ==> result.v0.v0.v0.v0 == 0;
            
        ensures result.v0.v0.v0.v0 <= 1;
    }
}
