# Move Semantics Documentation Tool

This tool generates comprehensive documentation for Move bytecode semantics based on the interpreter implementation.

## Overview

The Move VM interpreter executes bytecode instructions according to formal semantics defined in the `Bytecode` enum. This tool extracts those semantics annotations and generates human-readable documentation.

## Generated Documentation

The tool generates `MOVE_BYTECODE_SEMANTICS.md` in the repository root, which contains:

- Complete semantics for all 87 bytecode instructions
- Descriptions of each instruction's behavior
- Static operands (if any)
- Runtime type checks (prologue and epilogue)
- Instructions organized by functional group (control flow, arithmetic, etc.)

## Building

```bash
cargo build -p move-semantics-doc
```

## Running

To regenerate the documentation:

```bash
cargo run -p move-semantics-doc > MOVE_BYTECODE_SEMANTICS.md
```

Or use the Python extraction script:

```bash
python3 tools/move-semantics-doc/extract_semantics.py \
    third_party/move/move-binary-format/src/file_format.rs \
    > MOVE_BYTECODE_SEMANTICS.md
```

## Semantics Format

Each bytecode instruction includes:

- **Name**: The bytecode variant name
- **Group**: Functional category (e.g., "control_flow", "arithmetic", "vector")
- **Description**: Human-readable explanation
- **Semantics**: Pseudocode describing the instruction's behavior
- **Static Operands**: Parameters encoded in the bytecode (if any)
- **Runtime Checks**: Type safety checks performed before/after execution

## Maintenance

When new bytecode instructions are added to `move-binary-format/src/file_format.rs`, run this tool to update the documentation.

The semantics are defined using the `#[bytecode_spec]` procedural macro attributes in the source code.
