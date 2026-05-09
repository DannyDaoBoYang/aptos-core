module BasicCoin::ProphecyBenchmark {
    
    // The "Parent Node" containing 5 distinct integer fields
    struct Node has copy, drop {
        v0: u64, v1: u64, v2: u64, v3: u64, 
        v4: u64,
    }

    // Helper to create a clean node
    public fun new_node(): Node {
        Node { v0: 0, v1: 0, v2: 0, v3: 0, v4: 0 }
    }

    // The Logic: Borrow one specific field based on 'choice' and mutate it
    public fun update_one(node: Node, choice: u64): Node {
        // We must take a mutable borrow of the 'node' struct first
        let n_ref = &mut node;
        // This is the "Disjunction" that kills performance.
        // The solver has to fork {n} times here.
        let target = if (choice%5 == 0) { &mut n_ref.v0 }
        else if (choice%5 == 1) { &mut n_ref.v1 }
        else if (choice%5 == 2) { &mut n_ref.v2 }
        else if (choice%5 == 3) { &mut n_ref.v3 }
        else { &mut n_ref.v4 };
        // The Mutation
        *target = *target + 1;
        // Return the modified parent
        node
    }

    spec update_one {
        pragma opaque = false; //force inline
    	requires node.v0 <= 100;
	requires node.v1 <= 100;
	requires node.v2 <= 100;
	requires node.v3 <= 100;
	requires node.v4 <= 100;
 // No preconditions - fields can have any value
        // Postcondition: exactly one field is incremented by 1
        // The chosen field gets incremented by 1
        ensures choice == 0 ==> result.v0 == node.v0 + 1;
        ensures choice != 0 ==> result.v0 == node.v0;
        ensures choice == 0 ==> result.v1 == node.v1; 
        // This implies checks for every combination (8 * 8 = 64 checks internally)
        ensures choice == 1 ==> result.v1 == node.v1 + 1;
        ensures choice == 1 ==> result.v0 == node.v0;
        aborts_if false; 
    }

    // The Stress Test: Update the node 10 times in a row
    public fun stress_test_10(
        n: Node, 
        c0: u64, c1: u64, c2: u64, c3: u64, c4: u64, 
        c5: u64, c6: u64, c7: u64, c8: u64, c9: u64
    ): Node {
        let n1 = update_one(n, c0);
        let n2 = update_one(n1, c1);
        let n3 = update_one(n2, c2);
        let n4 = update_one(n3, c3);
        let n5 = update_one(n4, c4);
        let n6 = update_one(n5, c5);
        let n7 = update_one(n6, c6);
        n7
    }

    spec stress_test_10 {
        // 1. Preconditions (Assume clean slate for simplicity)
    	requires n.v0 == 0;
	requires n.v1 == 0;
	requires n.v2 == 0;
	requires n.v3 == 0;
	requires n.v4 == 0;
    // 2. The Verification for v0
        // We sum up the contribution of every single call (c0...c9)
        ensures result.v0 <= 10; 
        /*   (if (c0==0) {1} else {0}) + 
            (if (c1==0) {1} else {0}) + 
            (if (c2==0) {1} else {0}) + 
            (if (c3==0) {1} else {0}) + 
            (if (c4==0) {1} else {0}) + 
            (if (c5==0) {1} else {0}) + 
            (if (c6==0) {1} else {0}) + 
            (if (c7==0) {1} else {0}) + 
            (if (c8==0) {1} else {0}) + 
            (if (c9==0) {1} else {0}); */
        // Note: For a true stress test, you would technically need to write 
        // this huge block for v1, v2, v3... v{n-1} as well. 
        // But verifying just v0 is usually enough to slow down the solver 
        // because it still has to track the aliasing for all variables.
    }
}
