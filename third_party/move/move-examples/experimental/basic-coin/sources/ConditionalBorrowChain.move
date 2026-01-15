module BasicCoin::ProphecyBenchmark {
    
    // The "Parent Node" containing 8 distinct integer fields
    struct Node has copy, drop {
        v0: u64, v1: u64, v2: u64, v3: u64,
        v4: u64, v5: u64, v6: u64, v7: u64,
    }

    // Helper to create a clean node
    public fun new_node(): Node {
        Node { v0: 0, v1: 0, v2: 0, v3: 0, v4: 0, v5: 0, v6: 0, v7: 0 }
    }

    // The Logic: Borrow one specific field based on 'choice' and mutate it
    public fun update_one(node: Node, choice: u64): Node {
        // We must take a mutable borrow of the 'node' struct first
        let n_ref = &mut node;
        // This is the "Disjunction" that kills performance.
        // The solver has to fork 8 times here.
        let target = if (choice%8 == 0) { &mut n_ref.v0 }
        else if (choice%8 == 1) { &mut n_ref.v1 }
        else if (choice%8 == 2) { &mut n_ref.v2 }
        else if (choice%8 == 3) { &mut n_ref.v3 }
        else if (choice%8 == 4) { &mut n_ref.v4 }
        else if (choice%8 == 5) { &mut n_ref.v5 }
        else if (choice%8 == 6) { &mut n_ref.v6 }
        else { &mut n_ref.v7 };
        // The Mutation
        *target = *target + 1;
        // Return the modified parent
        node
    }

    // The Verification
    spec update_one {
        pragma opaque = false; //force inline
        requires node.v0 == 0 && node.v1 == 0 && node.v2 == 0 && node.v3 == 0;
        requires node.v4 == 0 && node.v5 == 0 && node.v6 == 0 && node.v7 == 0;
        // Assumption for valid input (to avoid choice > 7 going to v7 default)
        //requires choice < 8;
        // POSTCONDITION 1: The chosen field must be 1
        ensures choice == 0 ==> result.v0 == 1;
        ensures choice == 1 ==> result.v1 == 1;
        ensures choice == 2 ==> result.v2 == 1;
        ensures choice == 3 ==> result.v3 == 1;
        ensures choice == 4 ==> result.v4 == 1;
        ensures choice == 5 ==> result.v5 == 1;
        ensures choice == 6 ==> result.v6 == 1;
        ensures choice == 7 ==> result.v7 == 1;
        ensures choice == 0 ==> result.v0 == node.v0 + 1;
        ensures choice == 0 ==> result.v1 == node.v1; 
        // This implies checks for every combination (8 * 8 = 64 checks internally)
        ensures choice == 1 ==> result.v1 == node.v1 + 1;
        ensures choice == 1 ==> result.v0 == node.v0;
        // General Safety
        aborts_if false; 
    }

    // The Stress Test: Update the node 10 times in a row
    public fun stress_test_10(
        n: Node, 
        c0: u64, c1: u64, c2: u64, c3: u64, c4: u64, 
        c5: u64, c6: u64, c7: u64, c8: u64, c9: u64
    ): Node {
        let n = update_one(n, c0);
        let n = update_one(n, c1);
        let n = update_one(n, c2);
        let n = update_one(n, c3);
        let n = update_one(n, c4);
        let n = update_one(n, c5);
        let n = update_one(n, c6);
        let n = update_one(n, c7);
        let n = update_one(n, c8);
        let n = update_one(n, c9);
        n
    }

    spec stress_test_10 {
        // 1. Preconditions (Assume clean slate for simplicity)
        requires n.v0 == 0 && n.v1 == 0 && n.v2 == 0 && n.v3 == 0; 
        requires n.v4 == 0 && n.v5 == 0 && n.v6 == 0 && n.v7 == 0;
        // 2. The Verification for v0
        // We sum up the contribution of every single call (c0...c9)
        ensures result.v0 == 
            (if (c0==0) {1} else {0}) + 
            (if (c1==0) {1} else {0}) + 
            (if (c2==0) {1} else {0}) + 
            (if (c3==0) {1} else {0}) + 
            (if (c4==0) {1} else {0}) + 
            (if (c5==0) {1} else {0}) + 
            (if (c6==0) {1} else {0}) + 
            (if (c7==0) {1} else {0}) + 
            (if (c8==0) {1} else {0}) + 
            (if (c9==0) {1} else {0});
        // Note: For a true stress test, you would technically need to write 
        // this huge block for v1, v2, v3... v7 as well. 
        // But verifying just v0 is usually enough to slow down the solver 
        // because it still has to track the aliasing for all variables.
    }
}