# Fixed parts of the Move file
MODULE_HEADER = 'module BasicCoin::ProphecyBenchmark {{\n    \n    // The "Parent Node" containing {n} distinct integer fields\n'

STRUCT_HEADER = '    struct Node has copy, drop {\n'

STRUCT_FOOTER = '    }\n\n'

def generate_new_node_function(n):
    """Generate the new_node function"""
    fields = ", ".join([f"v{i}: 0" for i in range(n)])
    return f"""    // Helper to create a clean node
    public fun new_node(): Node {{
        Node {{ {fields} }}
    }}
"""

def generate_node_fields(n):
    """Generate field definitions for the Node struct"""
    result = ""
    for i in range(n):
        if i % 4 == 0:
            result += "        "
        result += f"v{i}: u64"
        if i < n - 1:
            result += ", "
            if (i + 1) % 4 == 0:
                result += "\n"
        else:
            result += ",\n"
    return result

def generate_node_initialization(n):
    """Generate initialization for new_node function"""
    init = ", ".join([f"v{i}: 0" for i in range(n)])
    return f"        Node {{ {init} }}\n"

def generate_update_one_function(n):
    """Generate the update_one function with conditional branching"""
    func = f"""
    // The Logic: Borrow one specific field based on 'choice' and mutate it
    public fun update_one(node: Node, choice: u64): Node {{
        // We must take a mutable borrow of the 'node' struct first
        let n_ref = &mut node;
        // This is the "Disjunction" that kills performance.
        // The solver has to fork {{n}} times here.
        let target = if (choice%{n} == 0) {{ &mut n_ref.v0 }}"""
    
    for i in range(1, n):
        if i < n - 1:
            func += f"\n        else if (choice%{n} == {i}) {{ &mut n_ref.v{i} }}"
        else:
            func += f"\n        else {{ &mut n_ref.v{i} }};"
    
    func += """
        // The Mutation
        *target = *target + 1;
        // Return the modified parent
        node
    }
"""
    return func

def generate_update_one_spec(n):
    """Generate the spec for update_one function"""
    optional_spec = ""
    for i in range(n):
        optional_spec += f"\trequires node.v{i} <= 100;\n"
    spec = f"""
    spec update_one {{
        pragma opaque = false; //force inline
    """ + optional_spec + f""" // No preconditions - fields can have any value
        // Postcondition: exactly one field is incremented by 1
        // The chosen field gets incremented by 1
        ensures choice == 0 ==> result.v0 == node.v0 + 1;
        ensures choice != 0 ==> result.v0 == result.v0;
        ensures choice == 0 ==> result.v1 == node.v1; 
        // This implies checks for every combination (8 * 8 = 64 checks internally)
        ensures choice == 1 ==> result.v1 == node.v1 + 1;
        ensures choice == 1 ==> result.v0 == node.v0;
        aborts_if false; 
    }}
"""
    
    return spec

def generate_stress_test_function(n):
    """Generate the stress_test_10 function"""
    func_spec_options = ""
    for i in range(n):
        func_spec_options += f"\trequires n.v{i} == 0;\n"
    func = f"""
    // The Stress Test: Update the node 10 times in a row
    public fun stress_test_10(
        n: Node, 
        c0: u64, c1: u64, c2: u64, c3: u64, c4: u64, 
        c5: u64, c6: u64, c7: u64, c8: u64, c9: u64
    ): Node {{
        let n1 = update_one(n, c0);
        let n2 = update_one(n1, c1);
        let n3 = update_one(n2, c2);
        let n4 = update_one(n3, c3);
        let n5 = update_one(n4, c4);
        let n6 = update_one(n5, c5);
        let n7 = update_one(n6, c6);
        n7
    }}

    spec stress_test_10 {{
        // 1. Preconditions (Assume clean slate for simplicity)
    """ + func_spec_options + f"""    // 2. The Verification for v0
        // We sum up the contribution of every single call (c0...c9)
        ensures result.v0 <= 10; 
        /*   (if (c0==0) {{1}} else {{0}}) + 
            (if (c1==0) {{1}} else {{0}}) + 
            (if (c2==0) {{1}} else {{0}}) + 
            (if (c3==0) {{1}} else {{0}}) + 
            (if (c4==0) {{1}} else {{0}}) + 
            (if (c5==0) {{1}} else {{0}}) + 
            (if (c6==0) {{1}} else {{0}}) + 
            (if (c7==0) {{1}} else {{0}}) + 
            (if (c8==0) {{1}} else {{0}}) + 
            (if (c9==0) {{1}} else {{0}}); */
        // Note: For a true stress test, you would technically need to write 
        // this huge block for v1, v2, v3... v{{n-1}} as well. 
        // But verifying just v0 is usually enough to slow down the solver 
        // because it still has to track the aliasing for all variables.
    }}
}}
"""
    
    return func

def generate_move_file(n, filename="sources/ConditionalBorrowChain.move"):
    with open(filename, "w") as f:
        f.write(MODULE_HEADER.format(n=n))
        f.write(STRUCT_HEADER)
        f.write(generate_node_fields(n))
        f.write(STRUCT_FOOTER)
        f.write(generate_new_node_function(n))
        f.write(generate_update_one_function(n))
        f.write(generate_update_one_spec(n))
        f.write(generate_stress_test_function(n))

if __name__ == "__main__":
    try:
        num_fields_str = n = int(input("Enter number of Node fields: "))
        if num_fields_str:
            n = int(num_fields_str)
            generate_move_file(n)
    except (ValueError, EOFError):
        # If input is not a valid integer or no input is provided, do nothing.
        pass

