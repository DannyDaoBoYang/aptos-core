# Move Bytecode Quick Reference

This is a quick reference guide for Move bytecode instructions. For detailed semantics, see [MOVE_BYTECODE_SEMANTICS.md](MOVE_BYTECODE_SEMANTICS.md).

## Control Flow Instructions
- `Ret` - Return from current function
- `BrTrue` - Conditional branch if true
- `BrFalse` - Conditional branch if false  
- `Branch` - Unconditional branch
- `Call` - Call a function
- `CallGeneric` - Call a generic function
- `Abort` - Abort transaction with error code
- `Nop` - No operation

## Stack and Local Variable Instructions
- `Pop` - Pop and discard value from stack
- `LdU8`, `LdU16`, `LdU32`, `LdU64`, `LdU128`, `LdU256` - Load integer constant
- `LdTrue`, `LdFalse` - Load boolean constant
- `LdConst` - Load constant from constant pool
- `CopyLoc` - Copy local variable to stack
- `MoveLoc` - Move local variable to stack
- `StLoc` - Store value to local variable
- `MutBorrowLoc` - Borrow local variable mutably
- `ImmBorrowLoc` - Borrow local variable immutably

## Reference Instructions
- `ReadRef` - Read value from reference
- `WriteRef` - Write value to reference
- `FreezeRef` - Convert mutable reference to immutable
- `CastU16`, `CastU32`, `CastU64`, `CastU128`, `CastU256` - Cast reference

## Arithmetic Instructions
- `Add` - Integer addition
- `Sub` - Integer subtraction
- `Mul` - Integer multiplication
- `Div` - Integer division
- `Mod` - Modulo operation

## Bitwise Instructions
- `BitOr` - Bitwise OR
- `BitAnd` - Bitwise AND
- `Xor` - Bitwise XOR
- `Shl` - Shift left
- `Shr` - Shift right

## Comparison Instructions
- `Lt` - Less than
- `Le` - Less than or equal
- `Gt` - Greater than
- `Ge` - Greater than or equal
- `Eq` - Equal
- `Neq` - Not equal

## Boolean Instructions
- `And` - Logical AND
- `Or` - Logical OR
- `Not` - Logical NOT

## Struct Instructions
- `Pack` - Create struct instance
- `PackGeneric` - Create generic struct instance
- `Unpack` - Destroy struct and extract fields
- `UnpackGeneric` - Destroy generic struct
- `MutBorrowField` - Borrow struct field mutably
- `MutBorrowFieldGeneric` - Borrow generic struct field mutably
- `ImmBorrowField` - Borrow struct field immutably
- `ImmBorrowFieldGeneric` - Borrow generic struct field immutably

## Variant (Enum) Instructions
- `PackVariant` - Create enum variant
- `PackVariantGeneric` - Create generic enum variant
- `UnpackVariant` - Destroy variant and extract fields
- `UnpackVariantGeneric` - Destroy generic variant
- `MutBorrowVariantField` - Borrow variant field mutably
- `MutBorrowVariantFieldGeneric` - Borrow generic variant field mutably
- `ImmBorrowVariantField` - Borrow variant field immutably
- `ImmBorrowVariantFieldGeneric` - Borrow generic variant field immutably
- `VariantSwitch` - Switch on enum variant

## Global Storage Instructions
- `MoveTo` - Move value to global storage
- `MoveToGeneric` - Move generic value to storage
- `MoveFrom` - Move value from global storage
- `MoveFromGeneric` - Move generic value from storage
- `MutBorrowGlobal` - Borrow global resource mutably
- `MutBorrowGlobalGeneric` - Borrow generic global resource mutably
- `ImmBorrowGlobal` - Borrow global resource immutably
- `ImmBorrowGlobalGeneric` - Borrow generic global resource immutably
- `Exists` - Check if resource exists
- `ExistsGeneric` - Check if generic resource exists

## Vector Instructions
- `VecPack` - Create vector from stack values
- `VecLen` - Get vector length
- `VecImmBorrow` - Borrow vector element immutably
- `VecMutBorrow` - Borrow vector element mutably
- `VecPushBack` - Append element to vector
- `VecPopBack` - Remove element from vector end
- `VecUnpack` - Destroy vector and extract elements
- `VecSwap` - Swap two vector elements

---

For complete semantics including:
- Detailed descriptions
- Pseudocode semantics
- Static operands
- Runtime type checks

See the full documentation at [MOVE_BYTECODE_SEMANTICS.md](MOVE_BYTECODE_SEMANTICS.md).

## Regenerating Documentation

To regenerate the bytecode semantics documentation:

```bash
./tools/move-semantics-doc/generate_docs.sh
```

Or manually:

```bash
python3 tools/move-semantics-doc/extract_semantics.py \
    third_party/move/move-binary-format/src/file_format.rs \
    > MOVE_BYTECODE_SEMANTICS.md
```
