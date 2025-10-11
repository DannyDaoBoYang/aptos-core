# Move Bytecode Semantics

This document describes the semantics of Move bytecode instructions based on the interpreter implementation.

---

## Control Flow

### `Ret`

Return from current function call, possibly with values according to the return types in the function signature.

        The returned values need to be pushed on the stack prior to the return instruction.

**Semantics:**

```
call_stack >> current_frame
        // The frame of the function being returned from is dropped.

        current_frame.pc += 1
```

---

### `BrTrue`

Branch to the instruction at position `code_offset` if the value at the top of the stack is true.
        Code offsets are relative to the start of the function body.

**Static Operands:** `[code_offset]`

**Semantics:**

```
stack >> flag
        if flag is true
            current_frame.pc = code_offset
        else
            current_frame.pc += 1
```

**Runtime Check (Prologue):**

```
ty_stack >> _
```

---

### `BrFalse`

Branch to the instruction at position `code_offset` if the value at the top of the stack is false.
        Code offsets are relative to the start of the function body.

**Static Operands:** `[code_offset]`

**Semantics:**

```
stack >> flag
        if flag is false
            current_frame.pc = code_offset
        else
            current_frame.pc += 1
```

**Runtime Check (Prologue):**

```
ty_stack >> _
```

---

### `Branch`

Branch unconditionally to the instruction at position `code_offset`.
        Code offsets are relative to the start of a function body.

**Static Operands:** `[code_offset]`

**Semantics:**

```
current_frame.pc = code_offset
```

---

### `Call`

Call a function. The stack has the arguments pushed first to last.
        The arguments are consumed and pushed to the locals of the function.

        Return values are pushed onto the stack from the first to the last and
        available to the caller after returning from the callee.

**Static Operands:** `[func_handle_idx]`

**Semantics:**

```
func = <func from handle or instantiation>
        // Here `func` is loaded from the file format, containing information like the
        // the function signature, the locals, and the body.

        ty_args = if func.is_generic then func.ty_args else []

        n = func.num_params
        stack >> arg_n-1
        ..
        stack >> arg_0

        if func.is_native()
            call_native(func.name, ty_args, args = [arg_0, .., arg_n-1])
            current_frame.pc += 1
        else
            call_stack << current_frame

            current_frame = new_frame_from_func(
                func,
                ty_args,
                locals = [arg_0, .., arg_n-1, invalid, ..]
                                           // ^ other locals
            )
```

**Runtime Check (Epilogue):**

```
assert func visibility rules
        for i in 0..#args:
            ty_stack >> ty
            assert ty == locals[#args -  i - 1]
```

---

### `CallGeneric`

Generic version of `Call`.

**Static Operands:** `[func_inst_idx]`

**Semantics:**

```
See `Call`.
```

**Runtime Check (Epilogue):**

```
See `Call`.
```

---

### `Abort`

Abort the transaction with an error code.

**Semantics:**

```
stack >> (error_code: u64)
        abort transaction with error_code
```

**Runtime Check (Prologue):**

```
ty_stack >> _
```

---

### `Nop`

A "no operation" -- an instruction that does not perform any meaningful operation.
        It can be however, useful as a placeholder in certain cases.

**Semantics:**

```
current_frame.pc += 1
```

---

## Stack And Local

### `Pop`

Pop and discard the value at the top of the stack. The value on the stack must be an copyable type.

**Semantics:**

```
stack >> _
```

**Runtime Check (Epilogue):**

```
ty_stack >> ty
        assert ty has drop
```

---

### `LdU8`

Push a u8 constant onto the stack.

**Static Operands:** `[u8_value]`

**Semantics:**

```
stack << u8_value
```

**Runtime Check (Epilogue):**

```
ty_stack << u8
```

---

### `LdU64`

Push a u64 constant onto the stack.

**Static Operands:** `[u64_value]`

**Semantics:**

```
stack << u64_value
```

**Runtime Check (Epilogue):**

```
ty_stack << u64
```

---

### `LdU128`

Push a u128 constant onto the stack.

**Static Operands:** `[u128_value]`

**Semantics:**

```
stack << u128_value
```

**Runtime Check (Epilogue):**

```
ty_stack << u128
```

---

### `LdConst`

Push a constant value onto the stack.
        The value is loaded and deserialized (according to its type) from the the file format.

**Static Operands:** `[const_idx]`

**Semantics:**

```
stack << constants[const_idx]
```

**Runtime Check (Epilogue):**

```
ty_stack << const_ty
```

---

### `LdTrue`

Push a true value onto the stack.

**Semantics:**

```
stack << true
```

**Runtime Check (Epilogue):**

```
ty_stack << bool
```

---

### `LdFalse`

Push a false value onto the stack.

**Semantics:**

```
stack << false
```

**Runtime Check (Epilogue):**

```
ty_stack << bool
```

---

### `CopyLoc`

Push the local identified by the local index onto the stack.
        The value must be copyable and the local remains safe to use.

**Semantics:**

```
stack << locals[local_idx]
```

**Runtime Check (Epilogue):**

```
ty = clone local_ty
        assert ty has copy
        ty_stack << ty
```

---

### `MoveLoc`

Move the local identified by the local index onto the stack.

        Once moved, the local becomes invalid to use, unless a store operation writes
        to the local before any read to that local.

**Static Operands:** `[local_idx]`

**Semantics:**

```
stack << locals[local_idx]
        locals[local_idx] = invalid
```

**Runtime Check (Epilogue):**

```
ty = clone local_ty
        ty_stack << ty
```

---

### `StLoc`

Pop value from the top of the stack and store it into the local identified by the local index.

        If the local contains an old value, then that value is dropped.

**Static Operands:** `[local_idx]`

**Semantics:**

```
stack >> locals[local_idx]
```

**Runtime Check (Prologue):**

```
ty = clone local_ty
        ty_stack >> val_ty
        assert ty == val_ty
        if locals[local_idx] != invalid
            assert ty has drop
```

---

### `MutBorrowLoc`

Load a mutable reference to a local identified by the local index.

**Static Operands:** `[local_idx]`

**Semantics:**

```
stack << &mut locals[local_idx]
```

**Runtime Check (Epilogue):**

```
ty = clone local_ty
        ty_stack << &mut ty
```

---

### `ImmBorrowLoc`

Load an immutable reference to a local identified by the local index.

**Static Operands:** `[local_idx]`

**Semantics:**

```
stack << &locals[local_idx]
```

**Runtime Check (Epilogue):**

```
ty << clone local_ty
        ty_stack << &ty
```

---

### `LdU16`

Push a u16 constant onto the stack.

**Static Operands:** `[u16_value]`

**Semantics:**

```
stack << u16_value
```

**Runtime Check (Epilogue):**

```
ty_stack << u16
```

---

### `LdU32`

Push a u32 constant onto the stack.

**Static Operands:** `[u32_value]`

**Semantics:**

```
stack << u32_value
```

**Runtime Check (Epilogue):**

```
ty_stack << u32
```

---

### `LdU256`

Push a u256 constant onto the stack.

**Static Operands:** `[u256_value]`

**Semantics:**

```
stack << u256_value
```

**Runtime Check (Epilogue):**

```
ty_stack << u256
```

---

## Reference

### `ReadRef`

Consume the reference at the top of the stack, read the value referenced, and push the value onto the stack.

        Reading a reference performs a copy of the value referenced.
        As such, ReadRef requires that the type of the value has the `copy` ability.

**Semantics:**

```
stack >> ref
        stack << copy *ref
```

**Runtime Check (Epilogue):**

```
ty_stack >> ref_ty
        assert ty has copy
```

---

### `WriteRef`

Pop a reference and a value off the stack, and write the value to the reference.

        It is required that the type of the value has the `drop` ability, as the previous value is dropped.

**Semantics:**

```
stack >> ref
        stack >> val
        *ref = val
```

**Runtime Check (Epilogue):**

```
ty_stack >> ref_ty
        ty_stack >> val_ty
        assert ref_ty == &val_ty
        assert val_ty has drop
```

---

### `FreezeRef`

Convert a mutable reference into an immutable reference.

**Semantics:**

```
stack >> mutable_ref
        stack << mutable_ref.into_immutable()
```

**Runtime Check (Epilogue):**

```
ty_stack >> &mut ty
        ty_stack << &ty
```

---

## Arithmetic

### `Add`

Add the two integer values at the top of the stack and push the result on the stack.

        This operation aborts the transaction in case of overflow.

**Semantics:**

```
stack >> rhs
        stack >> lhs
        if lhs + rhs > int_ty::max
            arithmetic error
        else
            stack << (lhs + rhs)
```

**Runtime Check (Epilogue):**

```
ty_stack >> right_ty
        ty_stack >> left_ty
        assert left_ty == right_ty
        ty_stack << right_ty
```

---

### `Sub`

Subtract the two integer values at the top of the stack and push the result on the stack.

        This operation aborts the transaction in case of underflow.

**Semantics:**

```
stack >> rhs
        stack >> lhs
        if lhs < rhs
            arithmetic error
        else
            stack << (lhs - rhs)
```

**Runtime Check (Epilogue):**

```
ty_stack >> right_ty
        ty_stack >> left_ty
        assert left_ty == right_ty
        ty_stack << right_ty
```

---

### `Mul`

Multiply the two integer values at the top of the stack and push the result on the stack.

        This operation aborts the transaction in case of overflow.

**Semantics:**

```
stack >> rhs
        stack >> lhs
        if lhs * rhs > int_ty::max
            arithmetic error
        else
            stack << (lhs * rhs)
```

**Runtime Check (Epilogue):**

```
ty_stack >> right_ty
        ty_stack >> left_ty
        assert left_ty == right_ty
        ty_stack << right_ty
```

---

### `Mod`

Perform a modulo operation on the two integer values at the top of the stack and push the result on the stack.

        This operation aborts the transaction in case the right hand side is zero.

**Semantics:**

```
stack >> rhs
        stack >> lhs
        if rhs == 0
            arithmetic error
        else
            stack << (lhs % rhs)
```

**Runtime Check (Epilogue):**

```
ty_stack >> right_ty
        ty_stack >> left_ty
        assert left_ty == right_ty
        ty_stack << right_ty
```

---

### `Div`

Divide the two integer values at the top of the stack and push the result on the stack.

        This operation aborts the transaction in case the right hand side is zero.

**Semantics:**

```
stack >> rhs
        stack >> lhs
        if rhs == 0
            arithmetic error
        else
            stack << (lhs / rhs)
```

**Runtime Check (Epilogue):**

```
ty_stack >> right_ty
        ty_stack >> left_ty
        assert left_ty == right_ty
        ty_stack << right_ty
```

---

## Casting

### `CastU8`

Convert the integer value at the top of the stack into a u8.
        An arithmetic error will be raised if the value cannot be represented as a u8.

**Semantics:**

```
stack >> int_val
        if int_val > u8::MAX:
            arithmetic error
        else:
            stack << int_val as u8
```

**Runtime Check (Epilogue):**

```
ty_stack >> _
        ty_stack << u8
```

---

### `CastU64`

Convert the integer value at the top of the stack into a u64.
        An arithmetic error will be raised if the value cannot be represented as a u64.

**Semantics:**

```
stack >> int_val
        if int_val > u64::MAX:
            arithmetic error
        else:
            stack << int_val as u64
```

**Runtime Check (Epilogue):**

```
ty_stack >> _
        ty_stack << u64
```

---

### `CastU128`

Convert the integer value at the top of the stack into a u128.
        An arithmetic error will be raised if the value cannot be represented as a u128.

**Semantics:**

```
stack >> int_val
        if int_val > u128::MAX:
            arithmetic error
        else:
            stack << int_val as u128
```

**Runtime Check (Epilogue):**

```
ty_stack >> _
        ty_stack << u128
```

---

### `CastU16`

Convert the integer value at the top of the stack into a u16.
        An arithmetic error will be raised if the value cannot be represented as a u16.

**Semantics:**

```
stack >> int_val
        if int_val > u16::MAX:
            arithmetic error
        else:
            stack << int_val as u16
```

**Runtime Check (Epilogue):**

```
ty_stack >> _
        ty_stack << u16
```

---

### `CastU32`

Convert the integer value at the top of the stack into a u32.
        An arithmetic error will be raised if the value cannot be represented as a u32.

**Semantics:**

```
stack >> int_val
        if int_val > u32::MAX:
            arithmetic error
        else:
            stack << int_val as u32
```

**Runtime Check (Epilogue):**

```
ty_stack >> _
        ty_stack << u32
```

---

### `CastU256`

Convert the integer value at the top of the stack into a u256.

**Semantics:**

```
stack >> int_val
        stack << int_val as u256
```

**Runtime Check (Epilogue):**

```
ty_stack >> _
        ty_stack << u256
```

---

## Bitwise

### `BitOr`

Perform a bitwise OR operation on the two integer values at the top of the stack
        and push the result on the stack.

        The operands can be of any (but the same) primitive integer type.

**Semantics:**

```
stack >> rhs
        stack >> lhs
        stack << lhs | rhs
```

**Runtime Check (Epilogue):**

```
ty_stack >> right_ty
        ty_stack >> left_ty
        assert left_ty == right_ty
        ty_stack << right_ty
```

---

### `BitAnd`

Perform a bitwise AND operation on the two integer values at the top of the stack
        and push the result on the stack.

        The operands can be of any (but the same) primitive integer type.

**Semantics:**

```
stack >> rhs
        stack >> lhs
        stack << lhs & rhs
```

**Runtime Check (Epilogue):**

```
ty_stack >> right_ty
        ty_stack >> left_ty
        assert left_ty == right_ty
        ty_stack << right_ty
```

---

### `Xor`

Perform a bitwise XOR operation on the two integer values at the top of the stack
        and push the result on the stack.

        The operands can be of any (but the same) primitive integer type.

**Semantics:**

```
stack >> rhs
        stack >> lhs
        stack << lhs ^ rhs
```

**Runtime Check (Epilogue):**

```
ty_stack >> right_ty
        ty_stack >> left_ty
        assert left_ty == right_ty
        ty_stack << right_ty
```

---

### `Shl`

Shift the (second top value) right (top value) bits and pushes the result on the stack.

        The number of bits shifted must be less than the number of bits in the integer value being shifted,
        or the transaction will be aborted with an arithmetic error.

        The number being shifted can be of any primitive integer type, but the number of bits
        shifted must be u64.

**Semantics:**

```
stack >> (rhs: u8)
        stack >> (lhs: int_ty)
        if rhs >= num_bits_in(int_ty)
            arithmetic error
        else
            stack << (lhs __shift_left__ rhs)
```

**Runtime Check (Epilogue):**

```
ty_stack >> right_ty
        ty_stack >> left_ty
        ty_stack << left_ty
```

---

### `Shr`

Shift the (second top value) left (top value) bits and pushes the result on the stack.

        The number of bits shifted must be less than the number of bits in the integer value being shifted,
        or the transaction will be aborted with an arithmetic error.

        The number being shifted can be of any primitive integer type, but the number of bits
        shifted must be u64.

**Semantics:**

```
stack >> (rhs: u8)
        stack >> (lhs: int_ty)
        if rhs >= num_bits_in(int_ty)
            arithmetic error
        else
            stack << (lhs __shift_right__ rhs)
```

**Runtime Check (Epilogue):**

```
ty_stack >> right_ty
        ty_stack >> left_ty
        ty_stack << left_ty
```

---

## Comparison

### `Eq`

Compare for equality the two values at the top of the stack and push the result on the stack.

        The values must have the `drop` ability as they will be consumed and destroyed.

**Semantics:**

```
stack >> rhs
        stack >> lhs
        stack << (lhs == rhs)

        Note that equality is only defined for
            - Simple primitive types: u8, u16, u32, u64, u128, u256, bool, address
            - vector<T> where equality is defined for T
            - &T (or &mut T) where equality is defined for T
```

**Runtime Check (Epilogue):**

```
ty_stack >> right_ty
        ty_stack >> left_ty
        assert right_ty == left_ty
        assert right_ty has drop
        ty_stack << bool
```

---

### `Neq`

Similar to `eq`, but with the result being inverted.

**Semantics:**

```
stack >> rhs
        stack >> lhs
        stack << (lhs != rhs)
```

**Runtime Check (Epilogue):**

```
ty_stack >> right_ty
        ty_stack >> left_ty
        assert right_ty == left_ty
        assert right_ty has drop
        ty_stack << bool
```

---

### `Lt`

Perform a "less than" operation of the two integer values at the top of the stack
        and push the boolean result on the stack.

        The operands can be of any (but the same) primitive integer type.

**Semantics:**

```
stack >> (rhs: int_ty)
        stack >> (lhs: int_ty)
        stack << (lhs < rhs)
```

**Runtime Check (Epilogue):**

```
ty_stack >> right_ty
        ty_stack >> left_ty
        assert right_ty == left_ty
        assert right_ty has drop
        ty_stack << bool
```

---

### `Gt`

Perform a "greater than" operation of the two integer values at the top of the stack
        and push the boolean result on the stack.

        The operands can be of any (but the same) primitive integer type.

**Semantics:**

```
stack >> (rhs: int_ty)
        stack >> (lhs: int_ty)
        stack << (lhs > rhs)
```

**Runtime Check (Epilogue):**

```
ty_stack >> right_ty
        ty_stack >> left_ty
        assert right_ty == left_ty
        assert right_ty has drop
        ty_stack << bool
```

---

### `Le`

Perform a "less than or equal to" operation of the two integer values at the top of the stack
        and push the boolean result on the stack.

        The operands can be of any (but the same) primitive integer type.

**Semantics:**

```
stack >> (rhs: int_ty)
        stack >> (lhs: int_ty)
        stack << (lhs <= rhs)
```

**Runtime Check (Epilogue):**

```
ty_stack >> right_ty
        ty_stack >> left_ty
        assert right_ty == left_ty
        assert right_ty has drop
        ty_stack << bool
```

---

### `Ge`

Perform a "greater than or equal to" operation of the two integer values at the top of the stack
        and push the boolean result on the stack.

        The operands can be of any (but the same) primitive integer type.

**Semantics:**

```
stack >> (rhs: int_ty)
        stack >> (lhs: int_ty)
        stack << (lhs >= rhs)
```

**Runtime Check (Epilogue):**

```
ty_stack >> right_ty
        ty_stack >> left_ty
        assert right_ty == left_ty
        assert right_ty has drop
        ty_stack << bool
```

---

## Boolean

### `Or`

Perform a boolean OR operation on the two bool values at the top of the stack
        and push the result on the stack.

**Semantics:**

```
stack >> rhs
        stack >> lhs
        stack << lhs || rhs
```

**Runtime Check (Epilogue):**

```
ty_stack >> right_ty
        ty_stack >> left_ty
        assert left_ty == right_ty
        ty_stack << right_ty
```

---

### `And`

Perform a boolean AND operation on the two bool values at the top of the stack
        and push the result on the stack.

**Semantics:**

```
stack >> rhs
        stack >> lhs
        stack << lhs && rhs
```

**Runtime Check (Epilogue):**

```
ty_stack >> right_ty
        ty_stack >> left_ty
        assert left_ty == right_ty
        ty_stack << right_ty
```

---

### `Not`

Invert the bool value at the top of the stack and push the result on the stack.

**Semantics:**

```
stack >> bool_val
        stack << (not bool_val)
```

**Runtime Check (Epilogue):**

```
ty_stack >> ty
        assert ty == bool
        ty_stack << bool
```

---

## Struct

### `Pack`

Create an instance of the struct specified by the struct def index and push it on the stack.
        The values of the fields of the struct, in the order they appear in the struct declaration,
        must be pushed on the stack. All fields must be provided.

**Static Operands:** `[struct_def_idx]`

**Semantics:**

```
stack >> field_n-1
        ...
        stack >> field_0
        stack << struct { field_0, ..., field_n-1 }
```

**Runtime Check (Epilogue):**

```
ty_stack >> tys
        assert tys == field_tys
        check field abilities
        ty_stack << struct_ty
```

---

### `PackGeneric`

Generic version of `Pack`.

**Static Operands:** `[struct_inst_idx]`

**Semantics:**

```
See `Pack`.
```

**Runtime Check (Epilogue):**

```
See `Pack`.
```

---

### `Unpack`

Destroy an instance of a struct and push the values bound to each field onto the stack.

**Static Operands:** `[struct_def_idx]`

**Semantics:**

```
stack >> struct { field_0, .., field_n-1 }
        stack << field_0
        ...
        stack << field_n-1
```

**Runtime Check (Epilogue):**

```
ty_stack >> ty
        assert ty == struct_ty
        ty_stack << field_tys
```

---

### `UnpackGeneric`

Generic version of `Unpack`.

**Static Operands:** `[struct_inst_idx]`

**Semantics:**

```
See `Unpack`.
```

**Runtime Check (Epilogue):**

```
See `Unpack`.
```

---

### `UnpackVariantGeneric`

Generic version of `UnpackVariant`.

**Static Operands:** `[struct_variant_inst_idx]`

**Semantics:**

```
See `UnpackVariant`.
```

**Runtime Check (Epilogue):**

```
See `UnpackVariant`.
```

---

### `MutBorrowField`

Consume the reference to a struct at the top of the stack,
        and load a mutable reference to the field identified by the field handle index.

**Static Operands:** `[field_handle_idx]`

**Semantics:**

```
stack >> struct_ref
        stack << &mut (*struct_ref).field(field_index)
```

**Runtime Check (Epilogue):**

```
ty_stack >> ty
        assert ty == &mut struct_ty
        ty_stack << &mut field_ty
```

---

### `MutBorrowFieldGeneric`

Consume the reference to a generic struct at the top of the stack,
        and load a mutable reference to the field identified by the field handle index.

**Static Operands:** `[field_inst_idx]`

**Semantics:**

```
stack >> struct_ref
        stack << &mut (*struct_ref).field(field_index)
```

**Runtime Check (Epilogue):**

```
ty_stack >> ty
        assert ty == &struct_ty
        ty_stack << &mut field_ty
```

---

### `ImmBorrowField`

Consume the reference to a struct at the top of the stack,
        and load an immutable reference to the field identified by the field handle index.

**Static Operands:** `[field_handle_idx]`

**Semantics:**

```
stack >> struct_ref
        stack << &(*struct_ref).field(field_index)
```

**Runtime Check (Epilogue):**

```
ty_stack >> ty
        assert ty == &struct_ty
        ty_stack << &field_ty
```

---

### `ImmBorrowFieldGeneric`

Consume the reference to a generic struct at the top of the stack,
        and load an immutable reference to the field identified by the
        field handle index.

**Static Operands:** `[field_inst_idx]`

**Semantics:**

```
stack >> struct_ref
        stack << &(*struct_ref).field(field_index)
```

**Runtime Check (Epilogue):**

```
ty_stack >> ty
        assert ty == &struct_ty
        ty_stack << &field_ty
```

---

## Variant

### `PackVariant`

Create an instance of the struct variant specified by the handle and push it on the stack.
        The values of the fields of the variant, in the order they are determined by the
        declaration, must be pushed on the stack. All fields must be provided.

**Static Operands:** `[struct_variant_handle_idx]`

**Semantics:**

```
stack >> field_n-1
        ...
        stack >> field_0
        stack << struct/variant { field_0, ..., field_n-1 }
```

**Runtime Check (Epilogue):**

```
ty_stack >> tys
        assert tys == field_tys
        check field abilities
        ty_stack << struct_ty
```

---

### `PackVariantGeneric`

Generic version of `PackVariant`.

**Static Operands:** `[struct_variant_inst_idx]`

**Semantics:**

```
See `PackVariant`.
```

**Runtime Check (Epilogue):**

```
See `PackVariant`.
```

---

### `UnpackVariant`

If the value on the stack is of the specified variant, destroy it and push the
        values bound to each field onto the stack.

        Aborts if the value is not of the specified variant.

**Static Operands:** `[struct_variant_handle_idx]`

**Semantics:**

```
if struct_ref is variant_field.variant
            stack >> struct/variant { field_0, .., field_n-1 }
            stack << field_0
            ...
            stack << field_n-1
        else
            error
```

**Runtime Check (Epilogue):**

```
ty_stack >> ty
        assert ty == struct_ty
        ty_stack << field_tys
```

---

### `TestVariant`

Tests whether the reference value on the stack is of the specified variant.

**Static Operands:** `[struct_variant_handle_idx]`

**Semantics:**

```
stack >> struct_ref
        stack << struct_if is variant
```

**Runtime Check (Epilogue):**

```
ty_stack >> ty
        assert ty == &struct_ty
        ty_stack << bool
```

---

### `TestVariantGeneric`

Generic version of `TestVariant`.

**Semantics:**

```
See `TestVariant`.
```

**Runtime Check (Epilogue):**

```
See `TestVariant`.
```

---

### `MutBorrowVariantField`

Consume the reference to a struct at the top of the stack,
        and provided that the struct is of the given variant, load a mutable reference to
        the field of the variant.

        Aborts execution if the operand is not of the given variant.

**Static Operands:** `[variant_field_handle_idx]`

**Semantics:**

```
stack >> struct_ref
        if struct_ref is variant
            stack << &mut (*struct_ref).field(variant_field.field_index)
        else
            error
```

**Runtime Check (Epilogue):**

```
ty_stack >> ty
        assert ty == &mut struct_ty
        ty_stack << &mut field_ty
```

---

### `MutBorrowVariantFieldGeneric`

Consume the reference to a generic struct at the top of the stack,
        and provided that the struct is of the given variant, load a mutable reference to
        the field of the variant.

        Aborts execution if the operand is not of the given variant.

**Static Operands:** `[variant_field_inst_idx]`

**Semantics:**

```
stack >> struct_ref
        if struct_ref is variant_field
            stack << &mut (*struct_ref).field(field_index)
        else
            error
```

**Runtime Check (Epilogue):**

```
ty_stack >> ty
        assert ty == &mut struct_ty
        ty_stack << &mut field_ty
```

---

### `ImmBorrowVariantField`

Consume the reference to a struct at the top of the stack,
        and provided that the struct is of the given variant, load an
        immutable reference to the field of the variant.

        Aborts execution if the operand is not of the given variant.

**Static Operands:** `[variant_field_inst_idx]`

**Semantics:**

```
stack >> struct_ref
        if struct_ref is variant
            stack << &(*struct_ref).field(field_index)
        else
            error
```

**Runtime Check (Epilogue):**

```
ty_stack >> ty
        assert ty == &mut struct_ty
        ty_stack << &mut field_ty
```

---

### `ImmBorrowVariantFieldGeneric`

Consume the reference to a generic struct at the top of the stack,
        and provided that the struct is of the given variant, load an immutable
        reference to the field of the variant.

        Aborts execution if the operand is not of the given variant.

**Static Operands:** `[variant_field_inst_idx]`

**Semantics:**

```
stack >> struct_ref
        if struct_ref is variant_field.variant
            stack << &(*struct_ref).field(variant_field.field_index)
        else
            error
```

**Runtime Check (Epilogue):**

```
ty_stack >> ty
        assert ty == &mut struct_ty
        ty_stack << &mut field_ty
```

---

## Global

### `MutBorrowGlobal`

Return a mutable reference to an instance of the specified type under the address passed as argument.

        Abort execution if such an object does not exist.

**Static Operands:** `[struct_def_idx]`

**Semantics:**

```
stack >> addr

        if global_state[addr] contains struct_type
            stack << &mut global_state[addr][struct_type]
        else
            error
```

**Runtime Check (Epilogue):**

```
ty_stack >> ty
        assert ty == address
        assert struct_ty has key
        ty_stack << &mut struct_ty
```

---

### `MutBorrowGlobalGeneric`

Generic version of `mut_borrow_global`.

**Static Operands:** `[struct_inst_idx]`

**Semantics:**

```
See `mut_borrow_global`.
```

**Runtime Check (Epilogue):**

```
See `mut_borrow_global`.
```

---

### `ImmBorrowGlobal`

Return an immutable reference to an instance of the specified type under the address passed as argument.

        Abort execution if such an object does not exist.

**Static Operands:** `[struct_def_idx]`

**Semantics:**

```
stack >> addr

        if global_state[addr] contains struct_type
            stack << &global_state[addr][struct_type]
        else
            error
```

**Runtime Check (Epilogue):**

```
ty_stack >> ty
        assert ty == address
        assert struct_ty has key
        ty_stack << &struct_ty
```

---

### `ImmBorrowGlobalGeneric`

Generic version of `imm_borrow_global`.

**Static Operands:** `[struct_inst_idx]`

**Semantics:**

```
See `imm_borrow_global`.
```

**Runtime Check (Epilogue):**

```
See `imm_borrow_global`.
```

---

### `Exists`

Check whether or not a given address in the global storage has an object of the specified type already.

**Static Operands:** `[struct_def_idx]`

**Semantics:**

```
stack >> addr
        stack << (global_state[addr] contains struct_type)
```

**Runtime Check (Epilogue):**

```
ty_stack >> ty
        assert ty == address
        ty_stack << bool
```

---

### `ExistsGeneric`

Generic version of `Exists`

**Static Operands:** `[struct_inst_idx]`

**Semantics:**

```
See `Exists`.
```

**Runtime Check (Epilogue):**

```
See `Exists`.
```

---

### `MoveFrom`

Move the value of the specified type under the address in the global storage onto the top of the stack.

        Abort execution if such an value does not exist.

**Static Operands:** `[struct_def_idx]`

**Semantics:**

```
stack >> addr

        if global_state[addr] contains struct_type
            stack << global_state[addr][struct_type]
            delete global_state[addr][struct_type]
        else
            error
```

**Runtime Check (Epilogue):**

```
ty_stack >> ty
        assert ty == address
        assert struct_ty has key
        ty_stack << struct_ty
```

---

### `MoveFromGeneric`

Generic version of `MoveFrom`

**Static Operands:** `[struct_inst_idx]`

**Semantics:**

```
See `MoveFrom`.
```

**Runtime Check (Epilogue):**

```
See `MoveFrom`.
```

---

### `MoveTo`

Move the value at the top of the stack into the global storage,
        under the address of the `signer` on the stack below it.

        Abort execution if an object of the same type already exists under that address.

**Static Operands:** `[struct_def_idx]`

**Semantics:**

```
stack >> struct_val
        stack >> &signer

        if global_state[signer.addr] contains struct_type
            error
        else
            global_state[signer.addr][struct_type] = struct_val
```

**Runtime Check (Epilogue):**

```
ty_stack >> ty1
        ty_stack >> ty2
        assert ty2 == signer
        assert ty1 == struct_ty
        assert struct_ty has key
```

---

### `MoveToGeneric`

Generic version of `MoveTo`

**Static Operands:** `[struct_inst_idx]`

**Semantics:**

```
See `MoveTo`.
```

**Runtime Check (Epilogue):**

```
See `MoveTo`.
```

---

## Vector

### `VecPack`

Create a vector by packing a statically known number of elements from the stack.

        Abort the execution if there are not enough number of elements on the stack
        to pack from or they do not have the same type identified by the `elem_ty_idx`.

**Static Operands:** `[elem_ty_idx] [num_elements]`

**Semantics:**

```
stack >> elem_n-1
        ..
        stack >> elem_0
        stack << vector[elem_0, .., elem_n-1]
```

**Runtime Check (Epilogue):**

```
elem_ty = instantiate elem_ty
        for i in 1..=n:
            ty_stack >> ty
            assert ty == elem_ty
        ty_stack << vector<elem_ty>
```

---

### `VecLen`

Get the length of a vector.

**Static Operands:** `[elem_ty_idx]`

**Semantics:**

```
stack >> vec_ref
        stack << (*vec_ref).len
```

**Runtime Check (Epilogue):**

```
elem_ty = instantiate elem_ty
        ty_stack >> ty
        assert ty == &elem_ty
        ty_stack << u64
```

---

### `VecImmBorrow`

Acquire an immutable reference to the element at a given index of the vector.
        Abort the execution if the index is out of bounds.

**Static Operands:** `[elem_ty_idx]`

**Semantics:**

```
stack >> i
        stack >> vec_ref
        stack << &((*vec_ref)[i])
```

**Runtime Check (Epilogue):**

```
ty_stack >> idx_ty
        assert idx_ty == u64
        ty_stack >> ref_ty
        assert ref_ty == &vector<elem_ty>
        ty_stack << &elem_ty
```

---

### `VecMutBorrow`

Acquire a mutable reference to the element at a given index of the vector.
        Abort the execution if the index is out of bounds.

**Static Operands:** `[elem_ty_idx]`

**Semantics:**

```
stack >> i
        stack >> vec_ref
        stack << &mut ((*vec_ref)[i])
```

**Runtime Check (Epilogue):**

```
ty_stack >> idx_ty
        assert idx_ty == u64
        ty_stack >> ref_ty
        assert ref_ty == &mut vector<elem_ty>
        ty_stack << &mut elem_ty
```

---

### `VecPushBack`

Add an element to the end of the vector.

**Static Operands:** `[elem_ty_idx]`

**Semantics:**

```
stack >> val
        stack >> vec_ref
        (*vec_ref) << val
```

**Runtime Check (Epilogue):**

```
ty_stack >> val_ty
        assert val_ty == elem_ty
        ty_stack >> ref_ty
        assert ref_ty == &mut vector<elem_ty>
```

---

### `VecPopBack`

Pop an element from the end of vector.
        Aborts if the vector is empty.

**Static Operands:** `[elem_ty_idx]`

**Semantics:**

```
stack >> vec_ref
        (*vec_ref) >> val
        stack << val
```

**Runtime Check (Epilogue):**

```
ty_stack >> ref_ty
        assert ref_ty == &mut vector<elem_ty>
        ty_stack << val_ty
```

---

### `VecUnpack`

Destroy the vector and unpack a statically known number of elements onto the stack.
        Abort if the vector does not have a length `n`.

**Static Operands:** `[elem_ty_idx] [num_elements]`

**Semantics:**

```
stack >> vector[elem_0, ..., elem_n-1]
        stack << elem_0
        ...
        stack << elem_n
```

**Runtime Check (Epilogue):**

```
ty_stack >> ty
        assert ty == vector<elem_ty>
        ty_stack << [elem_ty]*n
```

---

### `VecSwap`

Swaps the elements at two indices in the vector.
        Abort the execution if any of the indices are out of bounds.

**Static Operands:** `[elem_ty_idx]`

**Semantics:**

```
stack >> j
        stack >> i
        stack >> vec_ref
        (*vec_ref)[i], (*vec_ref)[j] = (*vec_ref)[j], (*vec_ref)[i]
```

**Runtime Check (Epilogue):**

```
ty_stack >> ty1
        ty_stack >> ty2
        ty_stack >> ty3
        assert ty1 == u64
        assert ty2 == u64
        assert ty3 == &vector<elem_ty>
```

---

