module BasicCoin::ProphecyBenchmarkInitialized {

    // ==========================================
    // 1. DATA STRUCTURES
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

    struct Node4 has copy, drop, store {
        v0: Node3, v1: Node3, v2: Node3, v3: Node3, 
        v4: Node3, v5: Node3, v6: Node3, v7: Node3,
    }

    struct Node5 has copy, drop, store {
        v0: Node4, v1: Node4, v2: Node4, v3: Node4, 
        v4: Node4, v5: Node4, v6: Node4, v7: Node4,
    }

    // ==========================================
    // 2. INITIALIZATION LOGIC (Constructors)
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

    public fun new_node3(): Node3 {
        Node3 { 
            v0: new_node2(), v1: new_node2(), v2: new_node2(), v3: new_node2(), 
            v4: new_node2(), v5: new_node2(), v6: new_node2(), v7: new_node2() 
        }
    }

    public fun new_node4(): Node4 {
        Node4 { 
            v0: new_node3(), v1: new_node3(), v2: new_node3(), v3: new_node3(), 
            v4: new_node3(), v5: new_node3(), v6: new_node3(), v7: new_node3() 
        }
    }

    public fun new_node5(): Node5 {
        Node5 { 
            v0: new_node4(), v1: new_node4(), v2: new_node4(), v3: new_node4(), 
            v4: new_node4(), v5: new_node4(), v6: new_node4(), v7: new_node4() 
        }
    }

    // ==========================================
    // 3. THE GIANT BORROW FUNCTION (Mutation)
    // ==========================================

    public fun deep_update_root(
        root: Node5, 
        c5: u64, c4: u64, c3: u64, c2: u64, c1: u64
    ): Node5 {
        
        // 1. Borrow from Root (Node5) -> Node4
        let n5_ref = &mut root;
        let n4_ref = if (c5 % 8 == 0) { &mut n5_ref.v0 }
        else if (c5 % 8 == 1) { &mut n5_ref.v1 }
        else if (c5 % 8 == 2) { &mut n5_ref.v2 }
        else if (c5 % 8 == 3) { &mut n5_ref.v3 }
        else if (c5 % 8 == 4) { &mut n5_ref.v4 }
        else if (c5 % 8 == 5) { &mut n5_ref.v5 }
        else if (c5 % 8 == 6) { &mut n5_ref.v6 }
        else { &mut n5_ref.v7 };

        // 2. Borrow from Node4 -> Node3
        let n3_ref = if (c4 % 8 == 0) { &mut n4_ref.v0 }
        else if (c4 % 8 == 1) { &mut n4_ref.v1 }
        else if (c4 % 8 == 2) { &mut n4_ref.v2 }
        else if (c4 % 8 == 3) { &mut n4_ref.v3 }
        else if (c4 % 8 == 4) { &mut n4_ref.v4 }
        else if (c4 % 8 == 5) { &mut n4_ref.v5 }
        else if (c4 % 8 == 6) { &mut n4_ref.v6 }
        else { &mut n4_ref.v7 };

        // 3. Borrow from Node3 -> Node2
        let n2_ref = if (c3 % 8 == 0) { &mut n3_ref.v0 }
        else if (c3 % 8 == 1) { &mut n3_ref.v1 }
        else if (c3 % 8 == 2) { &mut n3_ref.v2 }
        else if (c3 % 8 == 3) { &mut n3_ref.v3 }
        else if (c3 % 8 == 4) { &mut n3_ref.v4 }
        else if (c3 % 8 == 5) { &mut n3_ref.v5 }
        else if (c3 % 8 == 6) { &mut n3_ref.v6 }
        else { &mut n3_ref.v7 };

        // 4. Borrow from Node2 -> Node1
        let n1_ref = if (c2 % 8 == 0) { &mut n2_ref.v0 }
        else if (c2 % 8 == 1) { &mut n2_ref.v1 }
        else if (c2 % 8 == 2) { &mut n2_ref.v2 }
        else if (c2 % 8 == 3) { &mut n2_ref.v3 }
        else if (c2 % 8 == 4) { &mut n2_ref.v4 }
        else if (c2 % 8 == 5) { &mut n2_ref.v5 }
        else if (c2 % 8 == 6) { &mut n2_ref.v6 }
        else { &mut n2_ref.v7 };

        // 5. Borrow from Node1 -> Leaf Integer (u64)
        let leaf_ref = if (c1 % 8 == 0) { &mut n1_ref.v0 }
        else if (c1 % 8 == 1) { &mut n1_ref.v1 }
        else if (c1 % 8 == 2) { &mut n1_ref.v2 }
        else if (c1 % 8 == 3) { &mut n1_ref.v3 }
        else if (c1 % 8 == 4) { &mut n1_ref.v4 }
        else if (c1 % 8 == 5) { &mut n1_ref.v5 }
        else if (c1 % 8 == 6) { &mut n1_ref.v6 }
        else { &mut n1_ref.v7 };

        // 6. The Mutation
        *leaf_ref = *leaf_ref + 1;

        root
    }

    // ==========================================
    // 4. MAIN ENTRY POINT & SPECS
    // ==========================================

    // Constructs a clean zero-tree, then attempts to update it.
    public fun benchmark_from_scratch(
        c5: u64, c4: u64, c3: u64, c2: u64, c1: u64
    ): Node5 {
        let root = new_node5(); 
        deep_update_root(root, c5, c4, c3, c2, c1)
    }

    spec benchmark_from_scratch {
        // We do NOT need 'requires' here because new_node5() ensures
        // the state is 0. The prover must derive this fact itself.

        // Assertion 1: If we target the specific path (0,0,0,0,0), it becomes 1.
        ensures (c5==0 && c4==0 && c3==0 && c2==0 && c1==0) 
            ==> result.v0.v0.v0.v0.v0 == 1;

        // Assertion 2: If we deviate even slightly, that specific path stays 0.
        ensures (c5!=0 || c4!=0 || c3!=0 || c2!=0 || c1!=0) 
            ==> result.v0.v0.v0.v0.v0 == 0;

        // Assertion 3: The leaf is bounded.
        ensures result.v0.v0.v0.v0.v0 <= 1;
    }
}
