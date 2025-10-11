// Copyright © Aptos Foundation
// SPDX-License-Identifier: Apache-2.0

//! Tool to generate Move bytecode semantics documentation
//! 
//! This tool extracts the semantics specifications from the Move bytecode
//! and generates human-readable documentation.

use move_binary_format::file_format::Bytecode;

fn main() {
    let specs = Bytecode::spec();
    
    println!("# Move Bytecode Semantics");
    println!();
    println!("This document describes the semantics of Move bytecode instructions.");
    println!("The semantics are derived from the interpreter implementation.");
    println!();
    
    // Group instructions by their group
    let mut groups = std::collections::BTreeMap::new();
    for spec in &specs {
        let group = spec.get("group").unwrap();
        groups.entry(group.clone()).or_insert_with(Vec::new).push(spec);
    }
    
    for (group, instructions) in groups {
        println!("## {}", group.replace('_', " ").to_uppercase());
        println!();
        
        for instr in instructions {
            let name = instr.get("name").unwrap();
            let description = instr.get("description").unwrap();
            let semantics = instr.get("semantics").unwrap();
            
            println!("### {}", name);
            println!();
            
            if !description.is_empty() {
                println!("{}", description);
                println!();
            }
            
            println!("**Semantics:**");
            println!();
            println!("```");
            println!("{}", semantics);
            println!("```");
            println!();
            
            if let Some(static_operands) = instr.get("static_operands") {
                if !static_operands.is_empty() {
                    println!("**Static Operands:** {}", static_operands);
                    println!();
                }
            }
            
            if let Some(runtime_check_prologue) = instr.get("runtime_check_prologue") {
                if !runtime_check_prologue.is_empty() {
                    println!("**Runtime Check (Prologue):**");
                    println!();
                    println!("```");
                    println!("{}", runtime_check_prologue);
                    println!("```");
                    println!();
                }
            }
            
            if let Some(runtime_check_epilogue) = instr.get("runtime_check_epilogue") {
                if !runtime_check_epilogue.is_empty() {
                    println!("**Runtime Check (Epilogue):**");
                    println!();
                    println!("```");
                    println!("{}", runtime_check_epilogue);
                    println!("```");
                    println!();
                }
            }
        }
    }
}
