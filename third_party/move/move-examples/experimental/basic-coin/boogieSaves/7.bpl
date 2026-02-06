
// ** Expanded prelude

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Basic theory for vectors using arrays. This version of vectors is not extensional.

datatype Vec<T> {
    Vec(v: [int]T, l: int)
}

function {:builtin "MapConst"} MapConstVec<T>(T): [int]T;
function DefaultVecElem<T>(): T;
function {:inline} DefaultVecMap<T>(): [int]T { MapConstVec(DefaultVecElem()) }

function {:inline} EmptyVec<T>(): Vec T {
    Vec(DefaultVecMap(), 0)
}

function {:inline} MakeVec1<T>(v: T): Vec T {
    Vec(DefaultVecMap()[0 := v], 1)
}

function {:inline} MakeVec2<T>(v1: T, v2: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2], 2)
}

function {:inline} MakeVec3<T>(v1: T, v2: T, v3: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2][2 := v3], 3)
}

function {:inline} MakeVec4<T>(v1: T, v2: T, v3: T, v4: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2][2 := v3][3 := v4], 4)
}

function {:inline} ExtendVec<T>(v: Vec T, elem: T): Vec T {
    (var l := v->l;
    Vec(v->v[l := elem], l + 1))
}

function {:inline} ReadVec<T>(v: Vec T, i: int): T {
    v->v[i]
}

function {:inline} LenVec<T>(v: Vec T): int {
    v->l
}

function {:inline} IsEmptyVec<T>(v: Vec T): bool {
    v->l == 0
}

function {:inline} RemoveVec<T>(v: Vec T): Vec T {
    (var l := v->l - 1;
    Vec(v->v[l := DefaultVecElem()], l))
}

function {:inline} RemoveAtVec<T>(v: Vec T, i: int): Vec T {
    (var l := v->l - 1;
    Vec(
        (lambda j: int ::
           if j >= 0 && j < l then
               if j < i then v->v[j] else v->v[j+1]
           else DefaultVecElem()),
        l))
}

function {:inline} ConcatVec<T>(v1: Vec T, v2: Vec T): Vec T {
    (var l1, m1, l2, m2 := v1->l, v1->v, v2->l, v2->v;
    Vec(
        (lambda i: int ::
          if i >= 0 && i < l1 + l2 then
            if i < l1 then m1[i] else m2[i - l1]
          else DefaultVecElem()),
        l1 + l2))
}

function {:inline} ReverseVec<T>(v: Vec T): Vec T {
    (var l := v->l;
    Vec(
        (lambda i: int :: if 0 <= i && i < l then v->v[l - i - 1] else DefaultVecElem()),
        l))
}

function {:inline} SliceVec<T>(v: Vec T, i: int, j: int): Vec T {
    (var m := v->v;
    Vec(
        (lambda k:int ::
          if 0 <= k && k < j - i then
            m[i + k]
          else
            DefaultVecElem()),
        (if j - i < 0 then 0 else j - i)))
}


function {:inline} UpdateVec<T>(v: Vec T, i: int, elem: T): Vec T {
    Vec(v->v[i := elem], v->l)
}

function {:inline} SwapVec<T>(v: Vec T, i: int, j: int): Vec T {
    (var m := v->v;
    Vec(m[i := m[j]][j := m[i]], v->l))
}

function {:inline} ContainsVec<T>(v: Vec T, e: T): bool {
    (var l := v->l;
    (exists i: int :: InRangeVec(v, i) && v->v[i] == e))
}

function IndexOfVec<T>(v: Vec T, e: T): int;
axiom {:ctor "Vec"} (forall<T> v: Vec T, e: T :: {IndexOfVec(v, e)}
    (var i := IndexOfVec(v,e);
     if (!ContainsVec(v, e)) then i == -1
     else InRangeVec(v, i) && ReadVec(v, i) == e &&
        (forall j: int :: j >= 0 && j < i ==> ReadVec(v, j) != e)));

// This function should stay non-inlined as it guards many quantifiers
// over vectors. It appears important to have this uninterpreted for
// quantifier triggering.
function InRangeVec<T>(v: Vec T, i: int): bool {
    i >= 0 && i < LenVec(v)
}

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Boogie model for multisets, based on Boogie arrays. This theory assumes extensional equality for element types.

datatype Multiset<T> {
    Multiset(v: [T]int, l: int)
}

function {:builtin "MapConst"} MapConstMultiset<T>(l: int): [T]int;

function {:inline} EmptyMultiset<T>(): Multiset T {
    Multiset(MapConstMultiset(0), 0)
}

function {:inline} LenMultiset<T>(s: Multiset T): int {
    s->l
}

function {:inline} ExtendMultiset<T>(s: Multiset T, v: T): Multiset T {
    (var len := s->l;
    (var cnt := s->v[v];
    Multiset(s->v[v := (cnt + 1)], len + 1)))
}

// This function returns (s1 - s2). This function assumes that s2 is a subset of s1.
function {:inline} SubtractMultiset<T>(s1: Multiset T, s2: Multiset T): Multiset T {
    (var len1 := s1->l;
    (var len2 := s2->l;
    Multiset((lambda v:T :: s1->v[v]-s2->v[v]), len1-len2)))
}

function {:inline} IsEmptyMultiset<T>(s: Multiset T): bool {
    (s->l == 0) &&
    (forall v: T :: s->v[v] == 0)
}

function {:inline} IsSubsetMultiset<T>(s1: Multiset T, s2: Multiset T): bool {
    (s1->l <= s2->l) &&
    (forall v: T :: s1->v[v] <= s2->v[v])
}

function {:inline} ContainsMultiset<T>(s: Multiset T, v: T): bool {
    s->v[v] > 0
}

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Theory for tables.

// v is the SMT array holding the key-value assignment. e is an array which
// independently determines whether a key is valid or not. l is the length.
//
// Note that even though the program cannot reflect over existence of a key,
// we want the specification to be able to do this, so it can express
// verification conditions like "key has been inserted".
datatype Table <K, V> {
    Table(v: [K]V, e: [K]bool, l: int)
}

// Functions for default SMT arrays. For the table values, we don't care and
// use an uninterpreted function.
function DefaultTableArray<K, V>(): [K]V;
function DefaultTableKeyExistsArray<K>(): [K]bool;
axiom DefaultTableKeyExistsArray() == (lambda i: int :: false);

function {:inline} EmptyTable<K, V>(): Table K V {
    Table(DefaultTableArray(), DefaultTableKeyExistsArray(), 0)
}

function {:inline} GetTable<K,V>(t: Table K V, k: K): V {
    // Notice we do not check whether key is in the table. The result is undetermined if it is not.
    t->v[k]
}

function {:inline} LenTable<K,V>(t: Table K V): int {
    t->l
}


function {:inline} ContainsTable<K,V>(t: Table K V, k: K): bool {
    t->e[k]
}

function {:inline} UpdateTable<K,V>(t: Table K V, k: K, v: V): Table K V {
    Table(t->v[k := v], t->e, t->l)
}

function {:inline} AddTable<K,V>(t: Table K V, k: K, v: V): Table K V {
    // This function has an undetermined result if the key is already in the table
    // (all specification functions have this "partial definiteness" behavior). Thus we can
    // just increment the length.
    Table(t->v[k := v], t->e[k := true], t->l + 1)
}

function {:inline} RemoveTable<K,V>(t: Table K V, k: K): Table K V {
    // Similar as above, we only need to consider the case where the key is in the table.
    Table(t->v, t->e[k := false], t->l - 1)
}

axiom {:ctor "Table"} (forall<K,V> t: Table K V :: {LenTable(t)}
    (exists k: K :: {ContainsTable(t, k)} ContainsTable(t, k)) ==> LenTable(t) >= 1
);
// TODO: we might want to encoder a stronger property that the length of table
// must be more than N given a set of N items. Currently we don't see a need here
// and the above axiom seems to be sufficient.



// Uninterpreted function for all types


function $Arbitrary_value_of'$bc_ProphecyBenchmark3Levels_Node1'(): $bc_ProphecyBenchmark3Levels_Node1;



function $Arbitrary_value_of'$bc_ProphecyBenchmark3Levels_Node2'(): $bc_ProphecyBenchmark3Levels_Node2;



function $Arbitrary_value_of'$bc_ProphecyBenchmark3Levels_Node3'(): $bc_ProphecyBenchmark3Levels_Node3;



function $Arbitrary_value_of'bool'(): bool;



function $Arbitrary_value_of'u256'(): int;



function $Arbitrary_value_of'u64'(): int;



function $Arbitrary_value_of'bv256'(): bv256;



function $Arbitrary_value_of'bv64'(): bv64;




// ============================================================================================
// Integer Types

// Constants, Instructions, and Procedures needed by both unsigned and signed integers, but defined separately.



const $MIN_U8: int;
const $MAX_U8: int;
axiom $MIN_U8 == 0;
axiom $MAX_U8 == 255;

function $IsValid'u8'(v: int): bool {
  v >= $MIN_U8 && v <= $MAX_U8
}

function {:inline} $IsEqual'u8'(x: int, y: int): bool {
    x == y
}

procedure {:inline 1} $CastU8(src: int) returns (dst: int)
{
    if (src < $MIN_U8 || src > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $AddU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U8 || src1 + src2 < $MIN_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU8_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $SubU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 - src2 > $MAX_U8 || src1 - src2 < $MIN_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 - src2;
}

procedure {:inline 1} $MulU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U8 || src1 * src2 < $MIN_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}


const $MIN_U16: int;
const $MAX_U16: int;
axiom $MIN_U16 == 0;
axiom $MAX_U16 == 65535;

function $IsValid'u16'(v: int): bool {
  v >= $MIN_U16 && v <= $MAX_U16
}

function {:inline} $IsEqual'u16'(x: int, y: int): bool {
    x == y
}

procedure {:inline 1} $CastU16(src: int) returns (dst: int)
{
    if (src < $MIN_U16 || src > $MAX_U16) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $AddU16(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U16 || src1 + src2 < $MIN_U16) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU16_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $SubU16(src1: int, src2: int) returns (dst: int)
{
    if (src1 - src2 > $MAX_U16 || src1 - src2 < $MIN_U16) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 - src2;
}

procedure {:inline 1} $MulU16(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U16 || src1 * src2 < $MIN_U16) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}


const $MIN_U32: int;
const $MAX_U32: int;
axiom $MIN_U32 == 0;
axiom $MAX_U32 == 4294967295;

function $IsValid'u32'(v: int): bool {
  v >= $MIN_U32 && v <= $MAX_U32
}

function {:inline} $IsEqual'u32'(x: int, y: int): bool {
    x == y
}

procedure {:inline 1} $CastU32(src: int) returns (dst: int)
{
    if (src < $MIN_U32 || src > $MAX_U32) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $AddU32(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U32 || src1 + src2 < $MIN_U32) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU32_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $SubU32(src1: int, src2: int) returns (dst: int)
{
    if (src1 - src2 > $MAX_U32 || src1 - src2 < $MIN_U32) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 - src2;
}

procedure {:inline 1} $MulU32(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U32 || src1 * src2 < $MIN_U32) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}


const $MIN_U64: int;
const $MAX_U64: int;
axiom $MIN_U64 == 0;
axiom $MAX_U64 == 18446744073709551615;

function $IsValid'u64'(v: int): bool {
  v >= $MIN_U64 && v <= $MAX_U64
}

function {:inline} $IsEqual'u64'(x: int, y: int): bool {
    x == y
}

procedure {:inline 1} $CastU64(src: int) returns (dst: int)
{
    if (src < $MIN_U64 || src > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $AddU64(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U64 || src1 + src2 < $MIN_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU64_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $SubU64(src1: int, src2: int) returns (dst: int)
{
    if (src1 - src2 > $MAX_U64 || src1 - src2 < $MIN_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 - src2;
}

procedure {:inline 1} $MulU64(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U64 || src1 * src2 < $MIN_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}


const $MIN_U128: int;
const $MAX_U128: int;
axiom $MIN_U128 == 0;
axiom $MAX_U128 == 340282366920938463463374607431768211455;

function $IsValid'u128'(v: int): bool {
  v >= $MIN_U128 && v <= $MAX_U128
}

function {:inline} $IsEqual'u128'(x: int, y: int): bool {
    x == y
}

procedure {:inline 1} $CastU128(src: int) returns (dst: int)
{
    if (src < $MIN_U128 || src > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $AddU128(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U128 || src1 + src2 < $MIN_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU128_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $SubU128(src1: int, src2: int) returns (dst: int)
{
    if (src1 - src2 > $MAX_U128 || src1 - src2 < $MIN_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 - src2;
}

procedure {:inline 1} $MulU128(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U128 || src1 * src2 < $MIN_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}


const $MIN_U256: int;
const $MAX_U256: int;
axiom $MIN_U256 == 0;
axiom $MAX_U256 == 115792089237316195423570985008687907853269984665640564039457584007913129639935;

function $IsValid'u256'(v: int): bool {
  v >= $MIN_U256 && v <= $MAX_U256
}

function {:inline} $IsEqual'u256'(x: int, y: int): bool {
    x == y
}

procedure {:inline 1} $CastU256(src: int) returns (dst: int)
{
    if (src < $MIN_U256 || src > $MAX_U256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $AddU256(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U256 || src1 + src2 < $MIN_U256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU256_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $SubU256(src1: int, src2: int) returns (dst: int)
{
    if (src1 - src2 > $MAX_U256 || src1 - src2 < $MIN_U256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 - src2;
}

procedure {:inline 1} $MulU256(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U256 || src1 * src2 < $MIN_U256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}


const $MIN_I8: int;
const $MAX_I8: int;
axiom $MIN_I8 == -128;
axiom $MAX_I8 == 127;

function $IsValid'i8'(v: int): bool {
  v >= $MIN_I8 && v <= $MAX_I8
}

function {:inline} $IsEqual'i8'(x: int, y: int): bool {
    x == y
}

procedure {:inline 1} $CastI8(src: int) returns (dst: int)
{
    if (src < $MIN_I8 || src > $MAX_I8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $AddI8(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_I8 || src1 + src2 < $MIN_I8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddI8_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $SubI8(src1: int, src2: int) returns (dst: int)
{
    if (src1 - src2 > $MAX_I8 || src1 - src2 < $MIN_I8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 - src2;
}

procedure {:inline 1} $MulI8(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_I8 || src1 * src2 < $MIN_I8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}


const $MIN_I16: int;
const $MAX_I16: int;
axiom $MIN_I16 == -32768;
axiom $MAX_I16 == 32767;

function $IsValid'i16'(v: int): bool {
  v >= $MIN_I16 && v <= $MAX_I16
}

function {:inline} $IsEqual'i16'(x: int, y: int): bool {
    x == y
}

procedure {:inline 1} $CastI16(src: int) returns (dst: int)
{
    if (src < $MIN_I16 || src > $MAX_I16) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $AddI16(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_I16 || src1 + src2 < $MIN_I16) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddI16_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $SubI16(src1: int, src2: int) returns (dst: int)
{
    if (src1 - src2 > $MAX_I16 || src1 - src2 < $MIN_I16) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 - src2;
}

procedure {:inline 1} $MulI16(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_I16 || src1 * src2 < $MIN_I16) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}


const $MIN_I32: int;
const $MAX_I32: int;
axiom $MIN_I32 == -2147483648;
axiom $MAX_I32 == 2147483647;

function $IsValid'i32'(v: int): bool {
  v >= $MIN_I32 && v <= $MAX_I32
}

function {:inline} $IsEqual'i32'(x: int, y: int): bool {
    x == y
}

procedure {:inline 1} $CastI32(src: int) returns (dst: int)
{
    if (src < $MIN_I32 || src > $MAX_I32) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $AddI32(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_I32 || src1 + src2 < $MIN_I32) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddI32_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $SubI32(src1: int, src2: int) returns (dst: int)
{
    if (src1 - src2 > $MAX_I32 || src1 - src2 < $MIN_I32) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 - src2;
}

procedure {:inline 1} $MulI32(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_I32 || src1 * src2 < $MIN_I32) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}


const $MIN_I64: int;
const $MAX_I64: int;
axiom $MIN_I64 == -9223372036854775808;
axiom $MAX_I64 == 9223372036854775807;

function $IsValid'i64'(v: int): bool {
  v >= $MIN_I64 && v <= $MAX_I64
}

function {:inline} $IsEqual'i64'(x: int, y: int): bool {
    x == y
}

procedure {:inline 1} $CastI64(src: int) returns (dst: int)
{
    if (src < $MIN_I64 || src > $MAX_I64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $AddI64(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_I64 || src1 + src2 < $MIN_I64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddI64_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $SubI64(src1: int, src2: int) returns (dst: int)
{
    if (src1 - src2 > $MAX_I64 || src1 - src2 < $MIN_I64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 - src2;
}

procedure {:inline 1} $MulI64(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_I64 || src1 * src2 < $MIN_I64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}


const $MIN_I128: int;
const $MAX_I128: int;
axiom $MIN_I128 == -170141183460469231731687303715884105728;
axiom $MAX_I128 == 170141183460469231731687303715884105727;

function $IsValid'i128'(v: int): bool {
  v >= $MIN_I128 && v <= $MAX_I128
}

function {:inline} $IsEqual'i128'(x: int, y: int): bool {
    x == y
}

procedure {:inline 1} $CastI128(src: int) returns (dst: int)
{
    if (src < $MIN_I128 || src > $MAX_I128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $AddI128(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_I128 || src1 + src2 < $MIN_I128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddI128_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $SubI128(src1: int, src2: int) returns (dst: int)
{
    if (src1 - src2 > $MAX_I128 || src1 - src2 < $MIN_I128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 - src2;
}

procedure {:inline 1} $MulI128(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_I128 || src1 * src2 < $MIN_I128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}


const $MIN_I256: int;
const $MAX_I256: int;
axiom $MIN_I256 == -57896044618658097711785492504343953926634992332820282019728792003956564819968;
axiom $MAX_I256 == 57896044618658097711785492504343953926634992332820282019728792003956564819967;

function $IsValid'i256'(v: int): bool {
  v >= $MIN_I256 && v <= $MAX_I256
}

function {:inline} $IsEqual'i256'(x: int, y: int): bool {
    x == y
}

procedure {:inline 1} $CastI256(src: int) returns (dst: int)
{
    if (src < $MIN_I256 || src > $MAX_I256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $AddI256(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_I256 || src1 + src2 < $MIN_I256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddI256_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $SubI256(src1: int, src2: int) returns (dst: int)
{
    if (src1 - src2 > $MAX_I256 || src1 - src2 < $MIN_I256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 - src2;
}

procedure {:inline 1} $MulI256(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_I256 || src1 * src2 < $MIN_I256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}


// Instructions and Procedures shared by unsigned and signed integers

// uninterpreted function to return an undefined value.
function $undefined_int(): int;

procedure {:inline 1} $Div(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 div src2;
}

procedure {:inline 1} $Mod(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 mod src2;
}

// Unimplemented binary arithmetic operations; return the dst
procedure {:inline 1} $ArithBinaryUnimplemented(src1: int, src2: int) returns (dst: int);

// Instructions and Procedures unique to unsigned integers

// Recursive exponentiation function
// Undefined unless e >=0.  $pow(0,0) is also undefined.
function $pow(n: int, e: int): int {
    if n != 0 && e == 0 then 1
    else if e > 0 then n * $pow(n, e - 1)
    else $undefined_int()
}

function $shl(src1: int, p: int): int {
    src1 * $pow(2, p)
}

function $shr(src1: int, p: int): int {
    src1 div $pow(2, p)
}

procedure {:inline 1} $Shr(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shr(src1, src2);
}




function $shlU8(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod ($MAX_U8 + 1)
}

procedure {:inline 1} $ShlU8(src1: int, src2: int) returns (dst: int)
{
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;

    if (src2 >= 8) {
        call $ExecFailureAbort();
        return;
    }

    dst := $shlU8(src1, src2);
}

procedure {:inline 1} $ShrU8(src1: int, src2: int) returns (dst: int)
{
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;

    if (src2 >= 8) {
        call $ExecFailureAbort();
        return;
    }

    dst := $shr(src1, src2);
}


function $shlU16(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod ($MAX_U16 + 1)
}

procedure {:inline 1} $ShlU16(src1: int, src2: int) returns (dst: int)
{
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;

    if (src2 >= 16) {
        call $ExecFailureAbort();
        return;
    }

    dst := $shlU16(src1, src2);
}

procedure {:inline 1} $ShrU16(src1: int, src2: int) returns (dst: int)
{
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;

    if (src2 >= 16) {
        call $ExecFailureAbort();
        return;
    }

    dst := $shr(src1, src2);
}


function $shlU32(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod ($MAX_U32 + 1)
}

procedure {:inline 1} $ShlU32(src1: int, src2: int) returns (dst: int)
{
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;

    if (src2 >= 32) {
        call $ExecFailureAbort();
        return;
    }

    dst := $shlU32(src1, src2);
}

procedure {:inline 1} $ShrU32(src1: int, src2: int) returns (dst: int)
{
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;

    if (src2 >= 32) {
        call $ExecFailureAbort();
        return;
    }

    dst := $shr(src1, src2);
}


function $shlU64(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod ($MAX_U64 + 1)
}

procedure {:inline 1} $ShlU64(src1: int, src2: int) returns (dst: int)
{
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;

    if (src2 >= 64) {
        call $ExecFailureAbort();
        return;
    }

    dst := $shlU64(src1, src2);
}

procedure {:inline 1} $ShrU64(src1: int, src2: int) returns (dst: int)
{
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;

    if (src2 >= 64) {
        call $ExecFailureAbort();
        return;
    }

    dst := $shr(src1, src2);
}


function $shlU128(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod ($MAX_U128 + 1)
}

procedure {:inline 1} $ShlU128(src1: int, src2: int) returns (dst: int)
{
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;

    if (src2 >= 128) {
        call $ExecFailureAbort();
        return;
    }

    dst := $shlU128(src1, src2);
}

procedure {:inline 1} $ShrU128(src1: int, src2: int) returns (dst: int)
{
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;

    if (src2 >= 128) {
        call $ExecFailureAbort();
        return;
    }

    dst := $shr(src1, src2);
}


function $shlU256(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod ($MAX_U256 + 1)
}

procedure {:inline 1} $ShlU256(src1: int, src2: int) returns (dst: int)
{
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;

    dst := $shlU256(src1, src2);
}

procedure {:inline 1} $ShrU256(src1: int, src2: int) returns (dst: int)
{
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;

    dst := $shr(src1, src2);
}


// Instructions and Procedures unique to signed integers




procedure {:inline 1} $NegateI8(src: int) returns (dst: int)
{
     if (src <= $MIN_I8) {
        call $ExecFailureAbort();
        return;
    }
    dst := -src;
}


procedure {:inline 1} $NegateI16(src: int) returns (dst: int)
{
     if (src <= $MIN_I16) {
        call $ExecFailureAbort();
        return;
    }
    dst := -src;
}


procedure {:inline 1} $NegateI32(src: int) returns (dst: int)
{
     if (src <= $MIN_I32) {
        call $ExecFailureAbort();
        return;
    }
    dst := -src;
}


procedure {:inline 1} $NegateI64(src: int) returns (dst: int)
{
     if (src <= $MIN_I64) {
        call $ExecFailureAbort();
        return;
    }
    dst := -src;
}


procedure {:inline 1} $NegateI128(src: int) returns (dst: int)
{
     if (src <= $MIN_I128) {
        call $ExecFailureAbort();
        return;
    }
    dst := -src;
}


procedure {:inline 1} $NegateI256(src: int) returns (dst: int)
{
     if (src <= $MIN_I256) {
        call $ExecFailureAbort();
        return;
    }
    dst := -src;
}


// ============================================================================================
// Logical Procedures

procedure {:inline 1} $Lt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 < src2;
}

procedure {:inline 1} $Gt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 > src2;
}

procedure {:inline 1} $Le(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 <= src2;
}

procedure {:inline 1} $Ge(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 >= src2;
}

procedure {:inline 1} $And(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 && src2;
}

procedure {:inline 1} $Or(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 || src2;
}

procedure {:inline 1} $Not(src: bool) returns (dst: bool)
{
    dst := !src;
}

// ============================================================================================
// Templates for bitvector operations

function {:bvbuiltin "bvand"} $And'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvor"} $Or'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvxor"} $Xor'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvadd"} $Add'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvsub"} $Sub'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvmul"} $Mul'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvudiv"} $Div'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvurem"} $Mod'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvshl"} $Shl'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvlshr"} $Shr'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvult"} $Lt'Bv8'(bv8,bv8) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv8'(bv8,bv8) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv8'(bv8,bv8) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv8'(bv8,bv8) returns(bool);

procedure {:inline 1} $AddBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Lt'Bv8'($Add'Bv8'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv8'(src1, src2);
}

procedure {:inline 1} $AddBv8_unchecked(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $Add'Bv8'(src1, src2);
}

procedure {:inline 1} $SubBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Lt'Bv8'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv8'(src1, src2);
}

procedure {:inline 1} $MulBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Lt'Bv8'($Mul'Bv8'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv8'(src1, src2);
}

procedure {:inline 1} $DivBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if (src2 == 0bv8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv8'(src1, src2);
}

procedure {:inline 1} $ModBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if (src2 == 0bv8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv8'(src1, src2);
}

procedure {:inline 1} $AndBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $And'Bv8'(src1,src2);
}

procedure {:inline 1} $OrBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $Or'Bv8'(src1,src2);
}

procedure {:inline 1} $XorBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $Xor'Bv8'(src1,src2);
}

procedure {:inline 1} $LtBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Lt'Bv8'(src1,src2);
}

procedure {:inline 1} $LeBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Le'Bv8'(src1,src2);
}

procedure {:inline 1} $GtBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Gt'Bv8'(src1,src2);
}

procedure {:inline 1} $GeBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Ge'Bv8'(src1,src2);
}

function $IsValid'bv8'(v: bv8): bool {
  $Ge'Bv8'(v,0bv8) && $Le'Bv8'(v,255bv8)
}

function {:inline} $IsEqual'bv8'(x: bv8, y: bv8): bool {
    x == y
}

procedure {:inline 1} $int2bv8(src: int) returns (dst: bv8)
{
    if (src > 255) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.8(src);
}

procedure {:inline 1} $bv2int8(src: bv8) returns (dst: int)
{
    dst := $bv2int.8(src);
}

function {:builtin "(_ int2bv 8)"} $int2bv.8(i: int) returns (bv8);
function {:builtin "bv2nat"} $bv2int.8(i: bv8) returns (int);

function {:bvbuiltin "bvand"} $And'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvor"} $Or'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvxor"} $Xor'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvadd"} $Add'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvsub"} $Sub'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvmul"} $Mul'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvudiv"} $Div'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvurem"} $Mod'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvshl"} $Shl'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvlshr"} $Shr'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvult"} $Lt'Bv16'(bv16,bv16) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv16'(bv16,bv16) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv16'(bv16,bv16) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv16'(bv16,bv16) returns(bool);

procedure {:inline 1} $AddBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Lt'Bv16'($Add'Bv16'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv16'(src1, src2);
}

procedure {:inline 1} $AddBv16_unchecked(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $Add'Bv16'(src1, src2);
}

procedure {:inline 1} $SubBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Lt'Bv16'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv16'(src1, src2);
}

procedure {:inline 1} $MulBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Lt'Bv16'($Mul'Bv16'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv16'(src1, src2);
}

procedure {:inline 1} $DivBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if (src2 == 0bv16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv16'(src1, src2);
}

procedure {:inline 1} $ModBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if (src2 == 0bv16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv16'(src1, src2);
}

procedure {:inline 1} $AndBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $And'Bv16'(src1,src2);
}

procedure {:inline 1} $OrBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $Or'Bv16'(src1,src2);
}

procedure {:inline 1} $XorBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $Xor'Bv16'(src1,src2);
}

procedure {:inline 1} $LtBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Lt'Bv16'(src1,src2);
}

procedure {:inline 1} $LeBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Le'Bv16'(src1,src2);
}

procedure {:inline 1} $GtBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Gt'Bv16'(src1,src2);
}

procedure {:inline 1} $GeBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Ge'Bv16'(src1,src2);
}

function $IsValid'bv16'(v: bv16): bool {
  $Ge'Bv16'(v,0bv16) && $Le'Bv16'(v,65535bv16)
}

function {:inline} $IsEqual'bv16'(x: bv16, y: bv16): bool {
    x == y
}

procedure {:inline 1} $int2bv16(src: int) returns (dst: bv16)
{
    if (src > 65535) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.16(src);
}

procedure {:inline 1} $bv2int16(src: bv16) returns (dst: int)
{
    dst := $bv2int.16(src);
}

function {:builtin "(_ int2bv 16)"} $int2bv.16(i: int) returns (bv16);
function {:builtin "bv2nat"} $bv2int.16(i: bv16) returns (int);

function {:bvbuiltin "bvand"} $And'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvor"} $Or'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvxor"} $Xor'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvadd"} $Add'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvsub"} $Sub'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvmul"} $Mul'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvudiv"} $Div'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvurem"} $Mod'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvshl"} $Shl'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvlshr"} $Shr'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvult"} $Lt'Bv32'(bv32,bv32) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv32'(bv32,bv32) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv32'(bv32,bv32) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv32'(bv32,bv32) returns(bool);

procedure {:inline 1} $AddBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Lt'Bv32'($Add'Bv32'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv32'(src1, src2);
}

procedure {:inline 1} $AddBv32_unchecked(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $Add'Bv32'(src1, src2);
}

procedure {:inline 1} $SubBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Lt'Bv32'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv32'(src1, src2);
}

procedure {:inline 1} $MulBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Lt'Bv32'($Mul'Bv32'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv32'(src1, src2);
}

procedure {:inline 1} $DivBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if (src2 == 0bv32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv32'(src1, src2);
}

procedure {:inline 1} $ModBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if (src2 == 0bv32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv32'(src1, src2);
}

procedure {:inline 1} $AndBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $And'Bv32'(src1,src2);
}

procedure {:inline 1} $OrBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $Or'Bv32'(src1,src2);
}

procedure {:inline 1} $XorBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $Xor'Bv32'(src1,src2);
}

procedure {:inline 1} $LtBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Lt'Bv32'(src1,src2);
}

procedure {:inline 1} $LeBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Le'Bv32'(src1,src2);
}

procedure {:inline 1} $GtBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Gt'Bv32'(src1,src2);
}

procedure {:inline 1} $GeBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Ge'Bv32'(src1,src2);
}

function $IsValid'bv32'(v: bv32): bool {
  $Ge'Bv32'(v,0bv32) && $Le'Bv32'(v,2147483647bv32)
}

function {:inline} $IsEqual'bv32'(x: bv32, y: bv32): bool {
    x == y
}

procedure {:inline 1} $int2bv32(src: int) returns (dst: bv32)
{
    if (src > 2147483647) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.32(src);
}

procedure {:inline 1} $bv2int32(src: bv32) returns (dst: int)
{
    dst := $bv2int.32(src);
}

function {:builtin "(_ int2bv 32)"} $int2bv.32(i: int) returns (bv32);
function {:builtin "bv2nat"} $bv2int.32(i: bv32) returns (int);

function {:bvbuiltin "bvand"} $And'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvor"} $Or'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvxor"} $Xor'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvadd"} $Add'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvsub"} $Sub'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvmul"} $Mul'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvudiv"} $Div'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvurem"} $Mod'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvshl"} $Shl'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvlshr"} $Shr'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvult"} $Lt'Bv64'(bv64,bv64) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv64'(bv64,bv64) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv64'(bv64,bv64) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv64'(bv64,bv64) returns(bool);

procedure {:inline 1} $AddBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Lt'Bv64'($Add'Bv64'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv64'(src1, src2);
}

procedure {:inline 1} $AddBv64_unchecked(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $Add'Bv64'(src1, src2);
}

procedure {:inline 1} $SubBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Lt'Bv64'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv64'(src1, src2);
}

procedure {:inline 1} $MulBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Lt'Bv64'($Mul'Bv64'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv64'(src1, src2);
}

procedure {:inline 1} $DivBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if (src2 == 0bv64) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv64'(src1, src2);
}

procedure {:inline 1} $ModBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if (src2 == 0bv64) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv64'(src1, src2);
}

procedure {:inline 1} $AndBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $And'Bv64'(src1,src2);
}

procedure {:inline 1} $OrBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $Or'Bv64'(src1,src2);
}

procedure {:inline 1} $XorBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $Xor'Bv64'(src1,src2);
}

procedure {:inline 1} $LtBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Lt'Bv64'(src1,src2);
}

procedure {:inline 1} $LeBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Le'Bv64'(src1,src2);
}

procedure {:inline 1} $GtBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Gt'Bv64'(src1,src2);
}

procedure {:inline 1} $GeBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Ge'Bv64'(src1,src2);
}

function $IsValid'bv64'(v: bv64): bool {
  $Ge'Bv64'(v,0bv64) && $Le'Bv64'(v,18446744073709551615bv64)
}

function {:inline} $IsEqual'bv64'(x: bv64, y: bv64): bool {
    x == y
}

procedure {:inline 1} $int2bv64(src: int) returns (dst: bv64)
{
    if (src > 18446744073709551615) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.64(src);
}

procedure {:inline 1} $bv2int64(src: bv64) returns (dst: int)
{
    dst := $bv2int.64(src);
}

function {:builtin "(_ int2bv 64)"} $int2bv.64(i: int) returns (bv64);
function {:builtin "bv2nat"} $bv2int.64(i: bv64) returns (int);

function {:bvbuiltin "bvand"} $And'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvor"} $Or'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvxor"} $Xor'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvadd"} $Add'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvsub"} $Sub'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvmul"} $Mul'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvudiv"} $Div'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvurem"} $Mod'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvshl"} $Shl'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvlshr"} $Shr'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvult"} $Lt'Bv128'(bv128,bv128) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv128'(bv128,bv128) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv128'(bv128,bv128) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv128'(bv128,bv128) returns(bool);

procedure {:inline 1} $AddBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Lt'Bv128'($Add'Bv128'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv128'(src1, src2);
}

procedure {:inline 1} $AddBv128_unchecked(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $Add'Bv128'(src1, src2);
}

procedure {:inline 1} $SubBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Lt'Bv128'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv128'(src1, src2);
}

procedure {:inline 1} $MulBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Lt'Bv128'($Mul'Bv128'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv128'(src1, src2);
}

procedure {:inline 1} $DivBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if (src2 == 0bv128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv128'(src1, src2);
}

procedure {:inline 1} $ModBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if (src2 == 0bv128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv128'(src1, src2);
}

procedure {:inline 1} $AndBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $And'Bv128'(src1,src2);
}

procedure {:inline 1} $OrBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $Or'Bv128'(src1,src2);
}

procedure {:inline 1} $XorBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $Xor'Bv128'(src1,src2);
}

procedure {:inline 1} $LtBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Lt'Bv128'(src1,src2);
}

procedure {:inline 1} $LeBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Le'Bv128'(src1,src2);
}

procedure {:inline 1} $GtBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Gt'Bv128'(src1,src2);
}

procedure {:inline 1} $GeBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Ge'Bv128'(src1,src2);
}

function $IsValid'bv128'(v: bv128): bool {
  $Ge'Bv128'(v,0bv128) && $Le'Bv128'(v,340282366920938463463374607431768211455bv128)
}

function {:inline} $IsEqual'bv128'(x: bv128, y: bv128): bool {
    x == y
}

procedure {:inline 1} $int2bv128(src: int) returns (dst: bv128)
{
    if (src > 340282366920938463463374607431768211455) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.128(src);
}

procedure {:inline 1} $bv2int128(src: bv128) returns (dst: int)
{
    dst := $bv2int.128(src);
}

function {:builtin "(_ int2bv 128)"} $int2bv.128(i: int) returns (bv128);
function {:builtin "bv2nat"} $bv2int.128(i: bv128) returns (int);

function {:bvbuiltin "bvand"} $And'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvor"} $Or'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvxor"} $Xor'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvadd"} $Add'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvsub"} $Sub'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvmul"} $Mul'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvudiv"} $Div'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvurem"} $Mod'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvshl"} $Shl'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvlshr"} $Shr'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvult"} $Lt'Bv256'(bv256,bv256) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv256'(bv256,bv256) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv256'(bv256,bv256) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv256'(bv256,bv256) returns(bool);

procedure {:inline 1} $AddBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Lt'Bv256'($Add'Bv256'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv256'(src1, src2);
}

procedure {:inline 1} $AddBv256_unchecked(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $Add'Bv256'(src1, src2);
}

procedure {:inline 1} $SubBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Lt'Bv256'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv256'(src1, src2);
}

procedure {:inline 1} $MulBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Lt'Bv256'($Mul'Bv256'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv256'(src1, src2);
}

procedure {:inline 1} $DivBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if (src2 == 0bv256) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv256'(src1, src2);
}

procedure {:inline 1} $ModBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if (src2 == 0bv256) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv256'(src1, src2);
}

procedure {:inline 1} $AndBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $And'Bv256'(src1,src2);
}

procedure {:inline 1} $OrBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $Or'Bv256'(src1,src2);
}

procedure {:inline 1} $XorBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $Xor'Bv256'(src1,src2);
}

procedure {:inline 1} $LtBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Lt'Bv256'(src1,src2);
}

procedure {:inline 1} $LeBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Le'Bv256'(src1,src2);
}

procedure {:inline 1} $GtBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Gt'Bv256'(src1,src2);
}

procedure {:inline 1} $GeBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Ge'Bv256'(src1,src2);
}

function $IsValid'bv256'(v: bv256): bool {
  $Ge'Bv256'(v,0bv256) && $Le'Bv256'(v,115792089237316195423570985008687907853269984665640564039457584007913129639935bv256)
}

function {:inline} $IsEqual'bv256'(x: bv256, y: bv256): bool {
    x == y
}

procedure {:inline 1} $int2bv256(src: int) returns (dst: bv256)
{
    if (src > 115792089237316195423570985008687907853269984665640564039457584007913129639935) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.256(src);
}

procedure {:inline 1} $bv2int256(src: bv256) returns (dst: int)
{
    dst := $bv2int.256(src);
}

function {:builtin "(_ int2bv 256)"} $int2bv.256(i: int) returns (bv256);
function {:builtin "bv2nat"} $bv2int.256(i: bv256) returns (int);

datatype $Range {
    $Range(lb: int, ub: int)
}

function {:inline} $IsValid'bool'(v: bool): bool {
  true
}

function $IsValid'num'(v: int): bool {
  true
}

function $IsValid'address'(v: int): bool {
  // TODO: restrict max to representable addresses?
  v >= 0
}

function {:inline} $IsValidRange(r: $Range): bool {
   $IsValid'u64'(r->lb) &&  $IsValid'u64'(r->ub)
}

// Intentionally not inlined so it serves as a trigger in quantifiers.
function $InRange(r: $Range, i: int): bool {
   r->lb <= i && i < r->ub
}

function {:inline} $IsEqual'num'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'address'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'bool'(x: bool, y: bool): bool {
    x == y
}

// ============================================================================================
// Memory

datatype $Location {
    // A global resource location within the statically known resource type's memory,
    // where `a` is an address.
    $Global(a: int),
    // A local location. `i` is the unique index of the local.
    $Local(i: int),
    // The location of a reference outside of the verification scope, for example, a `&mut` parameter
    // of the function being verified. References with these locations don't need to be written back
    // when mutation ends.
    $Param(i: int),
    // The location of an uninitialized mutation. Using this to make sure that the location
    // will not be equal to any valid mutation locations, i.e., $Local, $Global, or $Param.
    $Uninitialized()
}

// A mutable reference which also carries its current value. Since mutable references
// are single threaded in Move, we can keep them together and treat them as a value
// during mutation until the point they are stored back to their original location.
datatype $Mutation<T> {
    $Mutation(l: $Location, p: Vec int, v: T)
}

// Representation of memory for a given type.
datatype $Memory<T> {
    $Memory(domain: [int]bool, contents: [int]T)
}

function {:builtin "MapConst"} $ConstMemoryDomain(v: bool): [int]bool;
function {:builtin "MapConst"} $ConstMemoryContent<T>(v: T): [int]T;
axiom $ConstMemoryDomain(false) == (lambda i: int :: false);
axiom $ConstMemoryDomain(true) == (lambda i: int :: true);


// Dereferences a mutation.
function {:inline} $Dereference<T>(ref: $Mutation T): T {
    ref->v
}

// Update the value of a mutation.
function {:inline} $UpdateMutation<T>(m: $Mutation T, v: T): $Mutation T {
    $Mutation(m->l, m->p, v)
}

// Havoc the content of the mutation, preserving location and path.
procedure {:inline 1} $HavocMutation<T>(m: $Mutation T) returns (r: $Mutation T) {
    r->l := m->l;
    r->p := m->p;
    // r->v stays uninitialized, thus havoced
}

function {:inline} $ChildMutation<T1, T2>(m: $Mutation T1, offset: int, v: T2): $Mutation T2 {
    $Mutation(m->l, ExtendVec(m->p, offset), v)
}

// Return true if two mutations share the location and path
function {:inline} $IsSameMutation<T1, T2>(parent: $Mutation T1, child: $Mutation T2 ): bool {
    parent->l == child->l && parent->p == child->p
}

// Return true if the mutation is a parent of a child which was derived with the given edge offset. This
// is used to implement write-back choices.
function {:inline} $IsParentMutation<T1, T2>(parent: $Mutation T1, edge: int, child: $Mutation T2 ): bool {
    parent->l == child->l &&
    (var pp := parent->p;
    (var cp := child->p;
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
     cl == pl + 1 &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) ==  ReadVec(cp, i)) &&
     $EdgeMatches(ReadVec(cp, pl), edge)
    ))))
}

// Return true if the mutation is a parent of a child, for hyper edge.
function {:inline} $IsParentMutationHyper<T1, T2>(parent: $Mutation T1, hyper_edge: Vec int, child: $Mutation T2 ): bool {
    parent->l == child->l &&
    (var pp := parent->p;
    (var cp := child->p;
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
    (var el := LenVec(hyper_edge);
     cl == pl + el &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) == ReadVec(cp, i)) &&
     (forall i: int:: i >= 0 && i < el ==> $EdgeMatches(ReadVec(cp, pl + i), ReadVec(hyper_edge, i)))
    )))))
}

function {:inline} $EdgeMatches(edge: int, edge_pattern: int): bool {
    edge_pattern == -1 // wildcard
    || edge_pattern == edge
}



function {:inline} $SameLocation<T1, T2>(m1: $Mutation T1, m2: $Mutation T2): bool {
    m1->l == m2->l
}

function {:inline} $HasGlobalLocation<T>(m: $Mutation T): bool {
    (m->l) is $Global
}

function {:inline} $HasLocalLocation<T>(m: $Mutation T, idx: int): bool {
    m->l == $Local(idx)
}

function {:inline} $GlobalLocationAddress<T>(m: $Mutation T): int {
    (m->l)->a
}



// Tests whether resource exists.
function {:inline} $ResourceExists<T>(m: $Memory T, addr: int): bool {
    m->domain[addr]
}

// Obtains Value of given resource.
function {:inline} $ResourceValue<T>(m: $Memory T, addr: int): T {
    m->contents[addr]
}

// Update resource.
function {:inline} $ResourceUpdate<T>(m: $Memory T, a: int, v: T): $Memory T {
    $Memory(m->domain[a := true], m->contents[a := v])
}

// Remove resource.
function {:inline} $ResourceRemove<T>(m: $Memory T, a: int): $Memory T {
    $Memory(m->domain[a := false], m->contents)
}

// Copies resource from memory s to m.
function {:inline} $ResourceCopy<T>(m: $Memory T, s: $Memory T, a: int): $Memory T {
    $Memory(m->domain[a := s->domain[a]],
            m->contents[a := s->contents[a]])
}

// ============================================================================================
// Abort Handling

var $abort_flag: bool;
var $abort_code: int;

function {:inline} $process_abort_code(code: int): int {
    code
}

const $EXEC_FAILURE_CODE: int;
axiom $EXEC_FAILURE_CODE == -1;

// TODO(wrwg): currently we map aborts of native functions like those for vectors also to
//   execution failure. This may need to be aligned with what the runtime actually does.

procedure {:inline 1} $ExecFailureAbort() {
    $abort_flag := true;
    $abort_code := $EXEC_FAILURE_CODE;
}

procedure {:inline 1} $Abort(code: int) {
    $abort_flag := true;
    $abort_code := code;
}

function {:inline} $StdError(cat: int, reason: int): int {
    reason * 256 + cat
}

procedure {:inline 1} $InitVerification() {
    // Set abort_flag to false, and havoc abort_code
    $abort_flag := false;
    havoc $abort_code;
    // Initialize event store
    call $InitEventStore();
}

// ============================================================================================
// Instructions


// Template for cast and shift operations of bitvector types

procedure {:inline 1} $CastBv8to8(src: bv8) returns (dst: bv8)
{
    dst := src;
}



function $shlBv8From8(src1: bv8, src2: bv8) returns (bv8)
{
    $Shl'Bv8'(src1, src2)
}

procedure {:inline 1} $ShlBv8From8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Ge'Bv8'(src2, 8bv8)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv8'(src1, src2);
}

function $shrBv8From8(src1: bv8, src2: bv8) returns (bv8)
{
    $Shr'Bv8'(src1, src2)
}

procedure {:inline 1} $ShrBv8From8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Ge'Bv8'(src2, 8bv8)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv8'(src1, src2);
}

procedure {:inline 1} $CastBv16to8(src: bv16) returns (dst: bv8)
{
    if ($Gt'Bv16'(src, 255bv16)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}



function $shlBv8From16(src1: bv8, src2: bv16) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From16(src1: bv8, src2: bv16) returns (dst: bv8)
{
    if ($Ge'Bv16'(src2, 8bv16)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From16(src1: bv8, src2: bv16) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From16(src1: bv8, src2: bv16) returns (dst: bv8)
{
    if ($Ge'Bv16'(src2, 8bv16)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv32to8(src: bv32) returns (dst: bv8)
{
    if ($Gt'Bv32'(src, 255bv32)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}



function $shlBv8From32(src1: bv8, src2: bv32) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From32(src1: bv8, src2: bv32) returns (dst: bv8)
{
    if ($Ge'Bv32'(src2, 8bv32)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From32(src1: bv8, src2: bv32) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From32(src1: bv8, src2: bv32) returns (dst: bv8)
{
    if ($Ge'Bv32'(src2, 8bv32)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv64to8(src: bv64) returns (dst: bv8)
{
    if ($Gt'Bv64'(src, 255bv64)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}



function $shlBv8From64(src1: bv8, src2: bv64) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From64(src1: bv8, src2: bv64) returns (dst: bv8)
{
    if ($Ge'Bv64'(src2, 8bv64)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From64(src1: bv8, src2: bv64) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From64(src1: bv8, src2: bv64) returns (dst: bv8)
{
    if ($Ge'Bv64'(src2, 8bv64)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv128to8(src: bv128) returns (dst: bv8)
{
    if ($Gt'Bv128'(src, 255bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}



function $shlBv8From128(src1: bv8, src2: bv128) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From128(src1: bv8, src2: bv128) returns (dst: bv8)
{
    if ($Ge'Bv128'(src2, 8bv128)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From128(src1: bv8, src2: bv128) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From128(src1: bv8, src2: bv128) returns (dst: bv8)
{
    if ($Ge'Bv128'(src2, 8bv128)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv256to8(src: bv256) returns (dst: bv8)
{
    if ($Gt'Bv256'(src, 255bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}



function $shlBv8From256(src1: bv8, src2: bv256) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From256(src1: bv8, src2: bv256) returns (dst: bv8)
{
    if ($Ge'Bv256'(src2, 8bv256)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From256(src1: bv8, src2: bv256) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From256(src1: bv8, src2: bv256) returns (dst: bv8)
{
    if ($Ge'Bv256'(src2, 8bv256)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv8to16(src: bv8) returns (dst: bv16)
{
    dst := 0bv8 ++ src;
}



function $shlBv16From8(src1: bv16, src2: bv8) returns (bv16)
{
    $Shl'Bv16'(src1, 0bv8 ++ src2)
}

procedure {:inline 1} $ShlBv16From8(src1: bv16, src2: bv8) returns (dst: bv16)
{
    if ($Ge'Bv8'(src2, 16bv8)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv16'(src1, 0bv8 ++ src2);
}

function $shrBv16From8(src1: bv16, src2: bv8) returns (bv16)
{
    $Shr'Bv16'(src1, 0bv8 ++ src2)
}

procedure {:inline 1} $ShrBv16From8(src1: bv16, src2: bv8) returns (dst: bv16)
{
    if ($Ge'Bv8'(src2, 16bv8)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv16'(src1, 0bv8 ++ src2);
}

procedure {:inline 1} $CastBv16to16(src: bv16) returns (dst: bv16)
{
    dst := src;
}



function $shlBv16From16(src1: bv16, src2: bv16) returns (bv16)
{
    $Shl'Bv16'(src1, src2)
}

procedure {:inline 1} $ShlBv16From16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Ge'Bv16'(src2, 16bv16)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv16'(src1, src2);
}

function $shrBv16From16(src1: bv16, src2: bv16) returns (bv16)
{
    $Shr'Bv16'(src1, src2)
}

procedure {:inline 1} $ShrBv16From16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Ge'Bv16'(src2, 16bv16)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv16'(src1, src2);
}

procedure {:inline 1} $CastBv32to16(src: bv32) returns (dst: bv16)
{
    if ($Gt'Bv32'(src, 65535bv32)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}



function $shlBv16From32(src1: bv16, src2: bv32) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From32(src1: bv16, src2: bv32) returns (dst: bv16)
{
    if ($Ge'Bv32'(src2, 16bv32)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From32(src1: bv16, src2: bv32) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From32(src1: bv16, src2: bv32) returns (dst: bv16)
{
    if ($Ge'Bv32'(src2, 16bv32)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv64to16(src: bv64) returns (dst: bv16)
{
    if ($Gt'Bv64'(src, 65535bv64)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}



function $shlBv16From64(src1: bv16, src2: bv64) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From64(src1: bv16, src2: bv64) returns (dst: bv16)
{
    if ($Ge'Bv64'(src2, 16bv64)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From64(src1: bv16, src2: bv64) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From64(src1: bv16, src2: bv64) returns (dst: bv16)
{
    if ($Ge'Bv64'(src2, 16bv64)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv128to16(src: bv128) returns (dst: bv16)
{
    if ($Gt'Bv128'(src, 65535bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}



function $shlBv16From128(src1: bv16, src2: bv128) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From128(src1: bv16, src2: bv128) returns (dst: bv16)
{
    if ($Ge'Bv128'(src2, 16bv128)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From128(src1: bv16, src2: bv128) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From128(src1: bv16, src2: bv128) returns (dst: bv16)
{
    if ($Ge'Bv128'(src2, 16bv128)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv256to16(src: bv256) returns (dst: bv16)
{
    if ($Gt'Bv256'(src, 65535bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}



function $shlBv16From256(src1: bv16, src2: bv256) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From256(src1: bv16, src2: bv256) returns (dst: bv16)
{
    if ($Ge'Bv256'(src2, 16bv256)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From256(src1: bv16, src2: bv256) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From256(src1: bv16, src2: bv256) returns (dst: bv16)
{
    if ($Ge'Bv256'(src2, 16bv256)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv8to32(src: bv8) returns (dst: bv32)
{
    dst := 0bv24 ++ src;
}



function $shlBv32From8(src1: bv32, src2: bv8) returns (bv32)
{
    $Shl'Bv32'(src1, 0bv24 ++ src2)
}

procedure {:inline 1} $ShlBv32From8(src1: bv32, src2: bv8) returns (dst: bv32)
{
    if ($Ge'Bv8'(src2, 32bv8)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv32'(src1, 0bv24 ++ src2);
}

function $shrBv32From8(src1: bv32, src2: bv8) returns (bv32)
{
    $Shr'Bv32'(src1, 0bv24 ++ src2)
}

procedure {:inline 1} $ShrBv32From8(src1: bv32, src2: bv8) returns (dst: bv32)
{
    if ($Ge'Bv8'(src2, 32bv8)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv32'(src1, 0bv24 ++ src2);
}

procedure {:inline 1} $CastBv16to32(src: bv16) returns (dst: bv32)
{
    dst := 0bv16 ++ src;
}



function $shlBv32From16(src1: bv32, src2: bv16) returns (bv32)
{
    $Shl'Bv32'(src1, 0bv16 ++ src2)
}

procedure {:inline 1} $ShlBv32From16(src1: bv32, src2: bv16) returns (dst: bv32)
{
    if ($Ge'Bv16'(src2, 32bv16)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv32'(src1, 0bv16 ++ src2);
}

function $shrBv32From16(src1: bv32, src2: bv16) returns (bv32)
{
    $Shr'Bv32'(src1, 0bv16 ++ src2)
}

procedure {:inline 1} $ShrBv32From16(src1: bv32, src2: bv16) returns (dst: bv32)
{
    if ($Ge'Bv16'(src2, 32bv16)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv32'(src1, 0bv16 ++ src2);
}

procedure {:inline 1} $CastBv32to32(src: bv32) returns (dst: bv32)
{
    dst := src;
}



function $shlBv32From32(src1: bv32, src2: bv32) returns (bv32)
{
    $Shl'Bv32'(src1, src2)
}

procedure {:inline 1} $ShlBv32From32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Ge'Bv32'(src2, 32bv32)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv32'(src1, src2);
}

function $shrBv32From32(src1: bv32, src2: bv32) returns (bv32)
{
    $Shr'Bv32'(src1, src2)
}

procedure {:inline 1} $ShrBv32From32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Ge'Bv32'(src2, 32bv32)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv32'(src1, src2);
}

procedure {:inline 1} $CastBv64to32(src: bv64) returns (dst: bv32)
{
    if ($Gt'Bv64'(src, 2147483647bv64)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[32:0];
}



function $shlBv32From64(src1: bv32, src2: bv64) returns (bv32)
{
    $Shl'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShlBv32From64(src1: bv32, src2: bv64) returns (dst: bv32)
{
    if ($Ge'Bv64'(src2, 32bv64)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv32'(src1, src2[32:0]);
}

function $shrBv32From64(src1: bv32, src2: bv64) returns (bv32)
{
    $Shr'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShrBv32From64(src1: bv32, src2: bv64) returns (dst: bv32)
{
    if ($Ge'Bv64'(src2, 32bv64)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv32'(src1, src2[32:0]);
}

procedure {:inline 1} $CastBv128to32(src: bv128) returns (dst: bv32)
{
    if ($Gt'Bv128'(src, 2147483647bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[32:0];
}



function $shlBv32From128(src1: bv32, src2: bv128) returns (bv32)
{
    $Shl'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShlBv32From128(src1: bv32, src2: bv128) returns (dst: bv32)
{
    if ($Ge'Bv128'(src2, 32bv128)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv32'(src1, src2[32:0]);
}

function $shrBv32From128(src1: bv32, src2: bv128) returns (bv32)
{
    $Shr'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShrBv32From128(src1: bv32, src2: bv128) returns (dst: bv32)
{
    if ($Ge'Bv128'(src2, 32bv128)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv32'(src1, src2[32:0]);
}

procedure {:inline 1} $CastBv256to32(src: bv256) returns (dst: bv32)
{
    if ($Gt'Bv256'(src, 2147483647bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[32:0];
}



function $shlBv32From256(src1: bv32, src2: bv256) returns (bv32)
{
    $Shl'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShlBv32From256(src1: bv32, src2: bv256) returns (dst: bv32)
{
    if ($Ge'Bv256'(src2, 32bv256)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv32'(src1, src2[32:0]);
}

function $shrBv32From256(src1: bv32, src2: bv256) returns (bv32)
{
    $Shr'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShrBv32From256(src1: bv32, src2: bv256) returns (dst: bv32)
{
    if ($Ge'Bv256'(src2, 32bv256)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv32'(src1, src2[32:0]);
}

procedure {:inline 1} $CastBv8to64(src: bv8) returns (dst: bv64)
{
    dst := 0bv56 ++ src;
}



function $shlBv64From8(src1: bv64, src2: bv8) returns (bv64)
{
    $Shl'Bv64'(src1, 0bv56 ++ src2)
}

procedure {:inline 1} $ShlBv64From8(src1: bv64, src2: bv8) returns (dst: bv64)
{
    if ($Ge'Bv8'(src2, 64bv8)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv64'(src1, 0bv56 ++ src2);
}

function $shrBv64From8(src1: bv64, src2: bv8) returns (bv64)
{
    $Shr'Bv64'(src1, 0bv56 ++ src2)
}

procedure {:inline 1} $ShrBv64From8(src1: bv64, src2: bv8) returns (dst: bv64)
{
    if ($Ge'Bv8'(src2, 64bv8)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv64'(src1, 0bv56 ++ src2);
}

procedure {:inline 1} $CastBv16to64(src: bv16) returns (dst: bv64)
{
    dst := 0bv48 ++ src;
}



function $shlBv64From16(src1: bv64, src2: bv16) returns (bv64)
{
    $Shl'Bv64'(src1, 0bv48 ++ src2)
}

procedure {:inline 1} $ShlBv64From16(src1: bv64, src2: bv16) returns (dst: bv64)
{
    if ($Ge'Bv16'(src2, 64bv16)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv64'(src1, 0bv48 ++ src2);
}

function $shrBv64From16(src1: bv64, src2: bv16) returns (bv64)
{
    $Shr'Bv64'(src1, 0bv48 ++ src2)
}

procedure {:inline 1} $ShrBv64From16(src1: bv64, src2: bv16) returns (dst: bv64)
{
    if ($Ge'Bv16'(src2, 64bv16)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv64'(src1, 0bv48 ++ src2);
}

procedure {:inline 1} $CastBv32to64(src: bv32) returns (dst: bv64)
{
    dst := 0bv32 ++ src;
}



function $shlBv64From32(src1: bv64, src2: bv32) returns (bv64)
{
    $Shl'Bv64'(src1, 0bv32 ++ src2)
}

procedure {:inline 1} $ShlBv64From32(src1: bv64, src2: bv32) returns (dst: bv64)
{
    if ($Ge'Bv32'(src2, 64bv32)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv64'(src1, 0bv32 ++ src2);
}

function $shrBv64From32(src1: bv64, src2: bv32) returns (bv64)
{
    $Shr'Bv64'(src1, 0bv32 ++ src2)
}

procedure {:inline 1} $ShrBv64From32(src1: bv64, src2: bv32) returns (dst: bv64)
{
    if ($Ge'Bv32'(src2, 64bv32)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv64'(src1, 0bv32 ++ src2);
}

procedure {:inline 1} $CastBv64to64(src: bv64) returns (dst: bv64)
{
    dst := src;
}


function $castBv64to64(src: bv64) returns (bv64)
{
    src
}


function $shlBv64From64(src1: bv64, src2: bv64) returns (bv64)
{
    $Shl'Bv64'(src1, src2)
}

procedure {:inline 1} $ShlBv64From64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Ge'Bv64'(src2, 64bv64)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv64'(src1, src2);
}

function $shrBv64From64(src1: bv64, src2: bv64) returns (bv64)
{
    $Shr'Bv64'(src1, src2)
}

procedure {:inline 1} $ShrBv64From64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Ge'Bv64'(src2, 64bv64)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv64'(src1, src2);
}

procedure {:inline 1} $CastBv128to64(src: bv128) returns (dst: bv64)
{
    if ($Gt'Bv128'(src, 18446744073709551615bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[64:0];
}



function $shlBv64From128(src1: bv64, src2: bv128) returns (bv64)
{
    $Shl'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShlBv64From128(src1: bv64, src2: bv128) returns (dst: bv64)
{
    if ($Ge'Bv128'(src2, 64bv128)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv64'(src1, src2[64:0]);
}

function $shrBv64From128(src1: bv64, src2: bv128) returns (bv64)
{
    $Shr'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShrBv64From128(src1: bv64, src2: bv128) returns (dst: bv64)
{
    if ($Ge'Bv128'(src2, 64bv128)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv64'(src1, src2[64:0]);
}

procedure {:inline 1} $CastBv256to64(src: bv256) returns (dst: bv64)
{
    if ($Gt'Bv256'(src, 18446744073709551615bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[64:0];
}


function $castBv256to64(src: bv256) returns (bv64)
{
    if ($Gt'Bv256'(src, 18446744073709551615bv256)) then
        $Arbitrary_value_of'bv64'()
    else
    src[64:0]
}


function $shlBv64From256(src1: bv64, src2: bv256) returns (bv64)
{
    $Shl'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShlBv64From256(src1: bv64, src2: bv256) returns (dst: bv64)
{
    if ($Ge'Bv256'(src2, 64bv256)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv64'(src1, src2[64:0]);
}

function $shrBv64From256(src1: bv64, src2: bv256) returns (bv64)
{
    $Shr'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShrBv64From256(src1: bv64, src2: bv256) returns (dst: bv64)
{
    if ($Ge'Bv256'(src2, 64bv256)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv64'(src1, src2[64:0]);
}

procedure {:inline 1} $CastBv8to128(src: bv8) returns (dst: bv128)
{
    dst := 0bv120 ++ src;
}



function $shlBv128From8(src1: bv128, src2: bv8) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv120 ++ src2)
}

procedure {:inline 1} $ShlBv128From8(src1: bv128, src2: bv8) returns (dst: bv128)
{
    if ($Ge'Bv8'(src2, 128bv8)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv128'(src1, 0bv120 ++ src2);
}

function $shrBv128From8(src1: bv128, src2: bv8) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv120 ++ src2)
}

procedure {:inline 1} $ShrBv128From8(src1: bv128, src2: bv8) returns (dst: bv128)
{
    if ($Ge'Bv8'(src2, 128bv8)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv128'(src1, 0bv120 ++ src2);
}

procedure {:inline 1} $CastBv16to128(src: bv16) returns (dst: bv128)
{
    dst := 0bv112 ++ src;
}



function $shlBv128From16(src1: bv128, src2: bv16) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv112 ++ src2)
}

procedure {:inline 1} $ShlBv128From16(src1: bv128, src2: bv16) returns (dst: bv128)
{
    if ($Ge'Bv16'(src2, 128bv16)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv128'(src1, 0bv112 ++ src2);
}

function $shrBv128From16(src1: bv128, src2: bv16) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv112 ++ src2)
}

procedure {:inline 1} $ShrBv128From16(src1: bv128, src2: bv16) returns (dst: bv128)
{
    if ($Ge'Bv16'(src2, 128bv16)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv128'(src1, 0bv112 ++ src2);
}

procedure {:inline 1} $CastBv32to128(src: bv32) returns (dst: bv128)
{
    dst := 0bv96 ++ src;
}



function $shlBv128From32(src1: bv128, src2: bv32) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv96 ++ src2)
}

procedure {:inline 1} $ShlBv128From32(src1: bv128, src2: bv32) returns (dst: bv128)
{
    if ($Ge'Bv32'(src2, 128bv32)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv128'(src1, 0bv96 ++ src2);
}

function $shrBv128From32(src1: bv128, src2: bv32) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv96 ++ src2)
}

procedure {:inline 1} $ShrBv128From32(src1: bv128, src2: bv32) returns (dst: bv128)
{
    if ($Ge'Bv32'(src2, 128bv32)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv128'(src1, 0bv96 ++ src2);
}

procedure {:inline 1} $CastBv64to128(src: bv64) returns (dst: bv128)
{
    dst := 0bv64 ++ src;
}



function $shlBv128From64(src1: bv128, src2: bv64) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv64 ++ src2)
}

procedure {:inline 1} $ShlBv128From64(src1: bv128, src2: bv64) returns (dst: bv128)
{
    if ($Ge'Bv64'(src2, 128bv64)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv128'(src1, 0bv64 ++ src2);
}

function $shrBv128From64(src1: bv128, src2: bv64) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv64 ++ src2)
}

procedure {:inline 1} $ShrBv128From64(src1: bv128, src2: bv64) returns (dst: bv128)
{
    if ($Ge'Bv64'(src2, 128bv64)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv128'(src1, 0bv64 ++ src2);
}

procedure {:inline 1} $CastBv128to128(src: bv128) returns (dst: bv128)
{
    dst := src;
}



function $shlBv128From128(src1: bv128, src2: bv128) returns (bv128)
{
    $Shl'Bv128'(src1, src2)
}

procedure {:inline 1} $ShlBv128From128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Ge'Bv128'(src2, 128bv128)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv128'(src1, src2);
}

function $shrBv128From128(src1: bv128, src2: bv128) returns (bv128)
{
    $Shr'Bv128'(src1, src2)
}

procedure {:inline 1} $ShrBv128From128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Ge'Bv128'(src2, 128bv128)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv128'(src1, src2);
}

procedure {:inline 1} $CastBv256to128(src: bv256) returns (dst: bv128)
{
    if ($Gt'Bv256'(src, 340282366920938463463374607431768211455bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[128:0];
}



function $shlBv128From256(src1: bv128, src2: bv256) returns (bv128)
{
    $Shl'Bv128'(src1, src2[128:0])
}

procedure {:inline 1} $ShlBv128From256(src1: bv128, src2: bv256) returns (dst: bv128)
{
    if ($Ge'Bv256'(src2, 128bv256)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv128'(src1, src2[128:0]);
}

function $shrBv128From256(src1: bv128, src2: bv256) returns (bv128)
{
    $Shr'Bv128'(src1, src2[128:0])
}

procedure {:inline 1} $ShrBv128From256(src1: bv128, src2: bv256) returns (dst: bv128)
{
    if ($Ge'Bv256'(src2, 128bv256)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv128'(src1, src2[128:0]);
}

procedure {:inline 1} $CastBv8to256(src: bv8) returns (dst: bv256)
{
    dst := 0bv248 ++ src;
}



function $shlBv256From8(src1: bv256, src2: bv8) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv248 ++ src2)
}

procedure {:inline 1} $ShlBv256From8(src1: bv256, src2: bv8) returns (dst: bv256)
{
    assume $bv2int.8(src2) >= 0 && $bv2int.8(src2) < 256;
    dst := $Shl'Bv256'(src1, 0bv248 ++ src2);
}

function $shrBv256From8(src1: bv256, src2: bv8) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv248 ++ src2)
}

procedure {:inline 1} $ShrBv256From8(src1: bv256, src2: bv8) returns (dst: bv256)
{
    assume $bv2int.8(src2) >= 0 && $bv2int.8(src2) < 256;
    dst := $Shr'Bv256'(src1, 0bv248 ++ src2);
}

procedure {:inline 1} $CastBv16to256(src: bv16) returns (dst: bv256)
{
    dst := 0bv240 ++ src;
}



function $shlBv256From16(src1: bv256, src2: bv16) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv240 ++ src2)
}

procedure {:inline 1} $ShlBv256From16(src1: bv256, src2: bv16) returns (dst: bv256)
{
    if ($Ge'Bv16'(src2, 256bv16)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv256'(src1, 0bv240 ++ src2);
}

function $shrBv256From16(src1: bv256, src2: bv16) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv240 ++ src2)
}

procedure {:inline 1} $ShrBv256From16(src1: bv256, src2: bv16) returns (dst: bv256)
{
    if ($Ge'Bv16'(src2, 256bv16)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv256'(src1, 0bv240 ++ src2);
}

procedure {:inline 1} $CastBv32to256(src: bv32) returns (dst: bv256)
{
    dst := 0bv224 ++ src;
}



function $shlBv256From32(src1: bv256, src2: bv32) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv224 ++ src2)
}

procedure {:inline 1} $ShlBv256From32(src1: bv256, src2: bv32) returns (dst: bv256)
{
    if ($Ge'Bv32'(src2, 256bv32)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv256'(src1, 0bv224 ++ src2);
}

function $shrBv256From32(src1: bv256, src2: bv32) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv224 ++ src2)
}

procedure {:inline 1} $ShrBv256From32(src1: bv256, src2: bv32) returns (dst: bv256)
{
    if ($Ge'Bv32'(src2, 256bv32)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv256'(src1, 0bv224 ++ src2);
}

procedure {:inline 1} $CastBv64to256(src: bv64) returns (dst: bv256)
{
    dst := 0bv192 ++ src;
}


function $castBv64to256(src: bv64) returns (bv256)
{
    0bv192 ++ src
}


function $shlBv256From64(src1: bv256, src2: bv64) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv192 ++ src2)
}

procedure {:inline 1} $ShlBv256From64(src1: bv256, src2: bv64) returns (dst: bv256)
{
    if ($Ge'Bv64'(src2, 256bv64)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv256'(src1, 0bv192 ++ src2);
}

function $shrBv256From64(src1: bv256, src2: bv64) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv192 ++ src2)
}

procedure {:inline 1} $ShrBv256From64(src1: bv256, src2: bv64) returns (dst: bv256)
{
    if ($Ge'Bv64'(src2, 256bv64)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv256'(src1, 0bv192 ++ src2);
}

procedure {:inline 1} $CastBv128to256(src: bv128) returns (dst: bv256)
{
    dst := 0bv128 ++ src;
}



function $shlBv256From128(src1: bv256, src2: bv128) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv128 ++ src2)
}

procedure {:inline 1} $ShlBv256From128(src1: bv256, src2: bv128) returns (dst: bv256)
{
    if ($Ge'Bv128'(src2, 256bv128)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv256'(src1, 0bv128 ++ src2);
}

function $shrBv256From128(src1: bv256, src2: bv128) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv128 ++ src2)
}

procedure {:inline 1} $ShrBv256From128(src1: bv256, src2: bv128) returns (dst: bv256)
{
    if ($Ge'Bv128'(src2, 256bv128)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv256'(src1, 0bv128 ++ src2);
}

procedure {:inline 1} $CastBv256to256(src: bv256) returns (dst: bv256)
{
    dst := src;
}


function $castBv256to256(src: bv256) returns (bv256)
{
    src
}


function $shlBv256From256(src1: bv256, src2: bv256) returns (bv256)
{
    $Shl'Bv256'(src1, src2)
}

procedure {:inline 1} $ShlBv256From256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Ge'Bv256'(src2, 256bv256)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shl'Bv256'(src1, src2);
}

function $shrBv256From256(src1: bv256, src2: bv256) returns (bv256)
{
    $Shr'Bv256'(src1, src2)
}

procedure {:inline 1} $ShrBv256From256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Ge'Bv256'(src2, 256bv256)) {
        call $ExecFailureAbort();
        return;
    }

    dst := $Shr'Bv256'(src1, src2);
}

// Pack and Unpack are auto-generated for each type T


// ==================================================================================
// Native Vector

function {:inline} $SliceVecByRange<T>(v: Vec T, r: $Range): Vec T {
    SliceVec(v, r->lb, r->ub)
}

// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `u8`

// Not inlined. It appears faster this way.
function $IsEqual'vec'u8''(v1: Vec (int), v2: Vec (int)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'u8'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'u8''(v: Vec (int), prefix: Vec (int)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'u8'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'u8''(v: Vec (int), suffix: Vec (int)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'u8'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'u8''(v: Vec (int)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'u8'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'u8'(v: Vec (int), e: int): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u8'(ReadVec(v, i), e))
}

function $IndexOfVec'u8'(v: Vec (int), e: int): int;
axiom (forall v: Vec (int), e: int:: {$IndexOfVec'u8'(v, e)}
    (var i := $IndexOfVec'u8'(v, e);
     if (!$ContainsVec'u8'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u8'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'u8'(ReadVec(v, j), e))));


function {:inline} $RangeVec'u8'(v: Vec (int)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'u8'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'u8'() returns (v: Vec (int)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'u8'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'u8'(v: Vec (int)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'u8'(m: $Mutation (Vec (int)), val: int) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'u8'(v: Vec (int), val: int): Vec (int) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'u8'(m: $Mutation (Vec (int))) returns (e: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'u8'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'u8'(m: $Mutation (Vec (int))) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_reverse_append'u8'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), ReverseVec(other)));
}

procedure {:inline 1} $1_vector_trim_reverse'u8'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    v := ReverseVec(v);
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_trim'u8'(m: $Mutation (Vec (int)), new_len: int) returns (v: (Vec (int)), m': $Mutation (Vec (int))) {
    var len: int;
    v := $Dereference(m);
    if (LenVec(v) < new_len) {
        call $ExecFailureAbort();
        return;
    }
    v := SliceVec(v, new_len, LenVec(v));
    m' := $UpdateMutation(m, SliceVec($Dereference(m), 0, new_len));
}

procedure {:inline 1} $1_vector_reverse_slice'u8'(m: $Mutation (Vec (int)), left: int, right: int) returns (m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var mid_vec: Vec (int);
    var right_vec: Vec (int);
    var v: Vec (int);
    if (left > right) {
        call $ExecFailureAbort();
        return;
    }
    if (left == right) {
        m' := m;
        return;
    }
    v := $Dereference(m);
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_vec := ReverseVec(SliceVec(v, left, right));
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
}

procedure {:inline 1} $1_vector_rotate'u8'(m: $Mutation (Vec (int)), rot: int) returns (n: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    var left_vec: Vec (int);
    var right_vec: Vec (int);
    v := $Dereference(m);
    if (!(rot >= 0 && rot <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    left_vec := SliceVec(v, 0, rot);
    right_vec := SliceVec(v, rot, LenVec(v));
    m' := $UpdateMutation(m, ConcatVec(right_vec, left_vec));
    n := LenVec(v) - rot;
}

procedure {:inline 1} $1_vector_rotate_slice'u8'(m: $Mutation (Vec (int)), left: int, rot: int, right: int) returns (n: int, m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var mid_vec: Vec (int);
    var right_vec: Vec (int);
    var mid_left_vec: Vec (int);
    var mid_right_vec: Vec (int);
    var v: Vec (int);
    v := $Dereference(m);
    if (!(left <= rot && rot <= right)) {
        call $ExecFailureAbort();
        return;
    }
    if (!(right >= 0 && right <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    v := $Dereference(m);
    left_vec := SliceVec(v, 0, left);
    right_vec := SliceVec(v, right, LenVec(v));
    mid_left_vec := SliceVec(v, left, rot);
    mid_right_vec := SliceVec(v, rot, right);
    mid_vec := ConcatVec(mid_right_vec, mid_left_vec);
    m' := $UpdateMutation(m, ConcatVec(left_vec, ConcatVec(mid_vec, right_vec)));
    n := left + (right - rot);
}

procedure {:inline 1} $1_vector_insert'u8'(m: $Mutation (Vec (int)), i: int, e: int) returns (m': $Mutation (Vec (int))) {
    var left_vec: Vec (int);
    var right_vec: Vec (int);
    var v: Vec (int);
    v := $Dereference(m);
    if (!(i >= 0 && i <= LenVec(v))) {
        call $ExecFailureAbort();
        return;
    }
    if (i == LenVec(v)) {
        m' := $UpdateMutation(m, ExtendVec(v, e));
    } else {
        left_vec := ExtendVec(SliceVec(v, 0, i), e);
        right_vec := SliceVec(v, i, LenVec(v));
        m' := $UpdateMutation(m, ConcatVec(left_vec, right_vec));
    }
}

procedure {:inline 1} $1_vector_length'u8'(v: Vec (int)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'u8'(v: Vec (int)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'u8'(v: Vec (int), i: int) returns (dst: int) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'u8'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'u8'(m: $Mutation (Vec (int)), index: int)
returns (dst: $Mutation (int), m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(m->l, ExtendVec(m->p, index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'u8'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'u8'(v: Vec (int)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'u8'(m: $Mutation (Vec (int)), i: int, j: int) returns (m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'u8'(v: Vec (int), i: int, j: int): Vec (int) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'u8'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var v: Vec (int);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'u8'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var len: int;
    var v: Vec (int);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'u8'(v: Vec (int), e: int) returns (res: bool)  {
    res := $ContainsVec'u8'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'u8'(v: Vec (int), e: int) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'u8'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ==================================================================================
// Native Table

// ==================================================================================
// Native Hash

// Hash is modeled as an otherwise uninterpreted injection.
// In truth, it is not an injection since the domain has greater cardinality
// (arbitrary length vectors) than the co-domain (vectors of length 32).  But it is
// common to assume in code there are no hash collisions in practice.  Fortunately,
// Boogie is not smart enough to recognized that there is an inconsistency.
// FIXME: If we were using a reliable extensional theory of arrays, and if we could use ==
// instead of $IsEqual, we might be able to avoid so many quantified formulas by
// using a sha2_inverse function in the ensures conditions of Hash_sha2_256 to
// assert that sha2/3 are injections without using global quantified axioms.


function $1_hash_sha2(val: Vec int): Vec int;

// This says that Hash_sha2 is bijective.
axiom (forall v1,v2: Vec int :: {$1_hash_sha2(v1), $1_hash_sha2(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_hash_sha2(v1), $1_hash_sha2(v2)));

procedure $1_hash_sha2_256(val: Vec int) returns (res: Vec int);
ensures res == $1_hash_sha2(val);     // returns Hash_sha2 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_hash_$sha2_256(val: Vec int): Vec int {
    $1_hash_sha2(val)
}

// similarly for Hash_sha3
function $1_hash_sha3(val: Vec int): Vec int;

axiom (forall v1,v2: Vec int :: {$1_hash_sha3(v1), $1_hash_sha3(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_hash_sha3(v1), $1_hash_sha3(v2)));

procedure $1_hash_sha3_256(val: Vec int) returns (res: Vec int);
ensures res == $1_hash_sha3(val);     // returns Hash_sha3 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_hash_$sha3_256(val: Vec int): Vec int {
    $1_hash_sha3(val)
}

// ==================================================================================
// Native string

// TODO: correct implementation of strings

procedure {:inline 1} $1_string_internal_check_utf8(x: Vec int) returns (r: bool) {
}

procedure {:inline 1} $1_string_internal_sub_string(x: Vec int, i: int, j: int) returns (r: Vec int) {
}

procedure {:inline 1} $1_string_internal_index_of(x: Vec int, y: Vec int) returns (r: int) {
}

procedure {:inline 1} $1_string_internal_is_char_boundary(x: Vec int, i: int) returns (r: bool) {
}




// ==================================================================================
// Native diem_account

procedure {:inline 1} $1_DiemAccount_create_signer(
  addr: int
) returns (signer: $signer) {
    // A signer is currently identical to an address.
    signer := $signer(addr);
}

procedure {:inline 1} $1_DiemAccount_destroy_signer(
  signer: $signer
) {
  return;
}

// ==================================================================================
// Native account

procedure {:inline 1} $1_Account_create_signer(
  addr: int
) returns (signer: $signer) {
    // A signer is currently identical to an address.
    signer := $signer(addr);
}

// ==================================================================================
// Native Signer

datatype $signer {
    $signer($addr: int),
    $permissioned_signer($addr: int, $permission_addr: int)
}

function {:inline} $IsValid'signer'(s: $signer): bool {
    if s is $signer then
        $IsValid'address'(s->$addr)
    else
        $IsValid'address'(s->$addr) &&
        $IsValid'address'(s->$permission_addr)
}

function {:inline} $IsEqual'signer'(s1: $signer, s2: $signer): bool {
    if s1 is $signer && s2 is $signer then
        s1 == s2
    else if s1 is $permissioned_signer && s2 is $permissioned_signer then
        s1 == s2
    else
        false
}

procedure {:inline 1} $1_signer_borrow_address(signer: $signer) returns (res: int) {
    res := signer->$addr;
}

function {:inline} $1_signer_$borrow_address(signer: $signer): int
{
    signer->$addr
}

function $1_signer_is_txn_signer(s: $signer): bool;

function $1_signer_is_txn_signer_addr(a: int): bool;


// ==================================================================================
// Native signature

// Signature related functionality is handled via uninterpreted functions. This is sound
// currently because we verify every code path based on signature verification with
// an arbitrary interpretation.

function $1_Signature_$ed25519_validate_pubkey(public_key: Vec int): bool;
function $1_Signature_$ed25519_verify(signature: Vec int, public_key: Vec int, message: Vec int): bool;

// Needed because we do not have extensional equality:
axiom (forall k1, k2: Vec int ::
    {$1_Signature_$ed25519_validate_pubkey(k1), $1_Signature_$ed25519_validate_pubkey(k2)}
    $IsEqual'vec'u8''(k1, k2) ==> $1_Signature_$ed25519_validate_pubkey(k1) == $1_Signature_$ed25519_validate_pubkey(k2));
axiom (forall s1, s2, k1, k2, m1, m2: Vec int ::
    {$1_Signature_$ed25519_verify(s1, k1, m1), $1_Signature_$ed25519_verify(s2, k2, m2)}
    $IsEqual'vec'u8''(s1, s2) && $IsEqual'vec'u8''(k1, k2) && $IsEqual'vec'u8''(m1, m2)
    ==> $1_Signature_$ed25519_verify(s1, k1, m1) == $1_Signature_$ed25519_verify(s2, k2, m2));


procedure {:inline 1} $1_Signature_ed25519_validate_pubkey(public_key: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_validate_pubkey(public_key);
}

procedure {:inline 1} $1_Signature_ed25519_verify(
        signature: Vec int, public_key: Vec int, message: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_verify(signature, public_key, message);
}


// ==================================================================================
// Native bcs::serialize


// ==================================================================================
// Native from_bcs::from_bytes


// ==================================================================================
// Native Event module



procedure {:inline 1} $InitEventStore() {
}

// ============================================================================================
// Type Reflection on Type Parameters

datatype $TypeParamInfo {
    $TypeParamBool(),
    $TypeParamU8(),
    $TypeParamU16(),
    $TypeParamU32(),
    $TypeParamU64(),
    $TypeParamU128(),
    $TypeParamU256(),
    $TypeParamI8(),
    $TypeParamI16(),
    $TypeParamI32(),
    $TypeParamI64(),
    $TypeParamI128(),
    $TypeParamI256(),
    $TypeParamAddress(),
    $TypeParamSigner(),
    $TypeParamVector(e: $TypeParamInfo),
    $TypeParamStruct(a: int, m: Vec int, s: Vec int)
}



//==================================
// Begin Translation



// Given Types for Type Parameters


// struct ProphecyBenchmark3Levels::Node1 at .\sources\ConditionalBorrowChain.move:8:5+131
datatype $bc_ProphecyBenchmark3Levels_Node1 {
    $bc_ProphecyBenchmark3Levels_Node1($v0: int, $v1: int, $v2: int, $v3: int, $v4: int, $v5: int, $v6: int, $v7: int)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0(s: $bc_ProphecyBenchmark3Levels_Node1, x: int): $bc_ProphecyBenchmark3Levels_Node1 {
    $bc_ProphecyBenchmark3Levels_Node1(x, s->$v1, s->$v2, s->$v3, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1(s: $bc_ProphecyBenchmark3Levels_Node1, x: int): $bc_ProphecyBenchmark3Levels_Node1 {
    $bc_ProphecyBenchmark3Levels_Node1(s->$v0, x, s->$v2, s->$v3, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2(s: $bc_ProphecyBenchmark3Levels_Node1, x: int): $bc_ProphecyBenchmark3Levels_Node1 {
    $bc_ProphecyBenchmark3Levels_Node1(s->$v0, s->$v1, x, s->$v3, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3(s: $bc_ProphecyBenchmark3Levels_Node1, x: int): $bc_ProphecyBenchmark3Levels_Node1 {
    $bc_ProphecyBenchmark3Levels_Node1(s->$v0, s->$v1, s->$v2, x, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4(s: $bc_ProphecyBenchmark3Levels_Node1, x: int): $bc_ProphecyBenchmark3Levels_Node1 {
    $bc_ProphecyBenchmark3Levels_Node1(s->$v0, s->$v1, s->$v2, s->$v3, x, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5(s: $bc_ProphecyBenchmark3Levels_Node1, x: int): $bc_ProphecyBenchmark3Levels_Node1 {
    $bc_ProphecyBenchmark3Levels_Node1(s->$v0, s->$v1, s->$v2, s->$v3, s->$v4, x, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6(s: $bc_ProphecyBenchmark3Levels_Node1, x: int): $bc_ProphecyBenchmark3Levels_Node1 {
    $bc_ProphecyBenchmark3Levels_Node1(s->$v0, s->$v1, s->$v2, s->$v3, s->$v4, s->$v5, x, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels_Node1'_v7(s: $bc_ProphecyBenchmark3Levels_Node1, x: int): $bc_ProphecyBenchmark3Levels_Node1 {
    $bc_ProphecyBenchmark3Levels_Node1(s->$v0, s->$v1, s->$v2, s->$v3, s->$v4, s->$v5, s->$v6, x)
}
function $IsValid'$bc_ProphecyBenchmark3Levels_Node1'(s: $bc_ProphecyBenchmark3Levels_Node1): bool {
    $IsValid'u64'(s->$v0)
      && $IsValid'u64'(s->$v1)
      && $IsValid'u64'(s->$v2)
      && $IsValid'u64'(s->$v3)
      && $IsValid'u64'(s->$v4)
      && $IsValid'u64'(s->$v5)
      && $IsValid'u64'(s->$v6)
      && $IsValid'u64'(s->$v7)
}
function {:inline} $IsEqual'$bc_ProphecyBenchmark3Levels_Node1'(s1: $bc_ProphecyBenchmark3Levels_Node1, s2: $bc_ProphecyBenchmark3Levels_Node1): bool {
    s1 == s2
}

// struct ProphecyBenchmark3Levels::Node2 at .\sources\ConditionalBorrowChain.move:14:5+147
datatype $bc_ProphecyBenchmark3Levels_Node2 {
    $bc_ProphecyBenchmark3Levels_Node2($v0: $bc_ProphecyBenchmark3Levels_Node1, $v1: $bc_ProphecyBenchmark3Levels_Node1, $v2: $bc_ProphecyBenchmark3Levels_Node1, $v3: $bc_ProphecyBenchmark3Levels_Node1, $v4: $bc_ProphecyBenchmark3Levels_Node1, $v5: $bc_ProphecyBenchmark3Levels_Node1, $v6: $bc_ProphecyBenchmark3Levels_Node1, $v7: $bc_ProphecyBenchmark3Levels_Node1)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0(s: $bc_ProphecyBenchmark3Levels_Node2, x: $bc_ProphecyBenchmark3Levels_Node1): $bc_ProphecyBenchmark3Levels_Node2 {
    $bc_ProphecyBenchmark3Levels_Node2(x, s->$v1, s->$v2, s->$v3, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1(s: $bc_ProphecyBenchmark3Levels_Node2, x: $bc_ProphecyBenchmark3Levels_Node1): $bc_ProphecyBenchmark3Levels_Node2 {
    $bc_ProphecyBenchmark3Levels_Node2(s->$v0, x, s->$v2, s->$v3, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2(s: $bc_ProphecyBenchmark3Levels_Node2, x: $bc_ProphecyBenchmark3Levels_Node1): $bc_ProphecyBenchmark3Levels_Node2 {
    $bc_ProphecyBenchmark3Levels_Node2(s->$v0, s->$v1, x, s->$v3, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3(s: $bc_ProphecyBenchmark3Levels_Node2, x: $bc_ProphecyBenchmark3Levels_Node1): $bc_ProphecyBenchmark3Levels_Node2 {
    $bc_ProphecyBenchmark3Levels_Node2(s->$v0, s->$v1, s->$v2, x, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4(s: $bc_ProphecyBenchmark3Levels_Node2, x: $bc_ProphecyBenchmark3Levels_Node1): $bc_ProphecyBenchmark3Levels_Node2 {
    $bc_ProphecyBenchmark3Levels_Node2(s->$v0, s->$v1, s->$v2, s->$v3, x, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5(s: $bc_ProphecyBenchmark3Levels_Node2, x: $bc_ProphecyBenchmark3Levels_Node1): $bc_ProphecyBenchmark3Levels_Node2 {
    $bc_ProphecyBenchmark3Levels_Node2(s->$v0, s->$v1, s->$v2, s->$v3, s->$v4, x, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6(s: $bc_ProphecyBenchmark3Levels_Node2, x: $bc_ProphecyBenchmark3Levels_Node1): $bc_ProphecyBenchmark3Levels_Node2 {
    $bc_ProphecyBenchmark3Levels_Node2(s->$v0, s->$v1, s->$v2, s->$v3, s->$v4, s->$v5, x, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels_Node2'_v7(s: $bc_ProphecyBenchmark3Levels_Node2, x: $bc_ProphecyBenchmark3Levels_Node1): $bc_ProphecyBenchmark3Levels_Node2 {
    $bc_ProphecyBenchmark3Levels_Node2(s->$v0, s->$v1, s->$v2, s->$v3, s->$v4, s->$v5, s->$v6, x)
}
function $IsValid'$bc_ProphecyBenchmark3Levels_Node2'(s: $bc_ProphecyBenchmark3Levels_Node2): bool {
    $IsValid'$bc_ProphecyBenchmark3Levels_Node1'(s->$v0)
      && $IsValid'$bc_ProphecyBenchmark3Levels_Node1'(s->$v1)
      && $IsValid'$bc_ProphecyBenchmark3Levels_Node1'(s->$v2)
      && $IsValid'$bc_ProphecyBenchmark3Levels_Node1'(s->$v3)
      && $IsValid'$bc_ProphecyBenchmark3Levels_Node1'(s->$v4)
      && $IsValid'$bc_ProphecyBenchmark3Levels_Node1'(s->$v5)
      && $IsValid'$bc_ProphecyBenchmark3Levels_Node1'(s->$v6)
      && $IsValid'$bc_ProphecyBenchmark3Levels_Node1'(s->$v7)
}
function {:inline} $IsEqual'$bc_ProphecyBenchmark3Levels_Node2'(s1: $bc_ProphecyBenchmark3Levels_Node2, s2: $bc_ProphecyBenchmark3Levels_Node2): bool {
    s1 == s2
}

// struct ProphecyBenchmark3Levels::Node3 at .\sources\ConditionalBorrowChain.move:20:5+147
datatype $bc_ProphecyBenchmark3Levels_Node3 {
    $bc_ProphecyBenchmark3Levels_Node3($v0: $bc_ProphecyBenchmark3Levels_Node2, $v1: $bc_ProphecyBenchmark3Levels_Node2, $v2: $bc_ProphecyBenchmark3Levels_Node2, $v3: $bc_ProphecyBenchmark3Levels_Node2, $v4: $bc_ProphecyBenchmark3Levels_Node2, $v5: $bc_ProphecyBenchmark3Levels_Node2, $v6: $bc_ProphecyBenchmark3Levels_Node2, $v7: $bc_ProphecyBenchmark3Levels_Node2)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0(s: $bc_ProphecyBenchmark3Levels_Node3, x: $bc_ProphecyBenchmark3Levels_Node2): $bc_ProphecyBenchmark3Levels_Node3 {
    $bc_ProphecyBenchmark3Levels_Node3(x, s->$v1, s->$v2, s->$v3, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1(s: $bc_ProphecyBenchmark3Levels_Node3, x: $bc_ProphecyBenchmark3Levels_Node2): $bc_ProphecyBenchmark3Levels_Node3 {
    $bc_ProphecyBenchmark3Levels_Node3(s->$v0, x, s->$v2, s->$v3, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2(s: $bc_ProphecyBenchmark3Levels_Node3, x: $bc_ProphecyBenchmark3Levels_Node2): $bc_ProphecyBenchmark3Levels_Node3 {
    $bc_ProphecyBenchmark3Levels_Node3(s->$v0, s->$v1, x, s->$v3, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3(s: $bc_ProphecyBenchmark3Levels_Node3, x: $bc_ProphecyBenchmark3Levels_Node2): $bc_ProphecyBenchmark3Levels_Node3 {
    $bc_ProphecyBenchmark3Levels_Node3(s->$v0, s->$v1, s->$v2, x, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4(s: $bc_ProphecyBenchmark3Levels_Node3, x: $bc_ProphecyBenchmark3Levels_Node2): $bc_ProphecyBenchmark3Levels_Node3 {
    $bc_ProphecyBenchmark3Levels_Node3(s->$v0, s->$v1, s->$v2, s->$v3, x, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5(s: $bc_ProphecyBenchmark3Levels_Node3, x: $bc_ProphecyBenchmark3Levels_Node2): $bc_ProphecyBenchmark3Levels_Node3 {
    $bc_ProphecyBenchmark3Levels_Node3(s->$v0, s->$v1, s->$v2, s->$v3, s->$v4, x, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6(s: $bc_ProphecyBenchmark3Levels_Node3, x: $bc_ProphecyBenchmark3Levels_Node2): $bc_ProphecyBenchmark3Levels_Node3 {
    $bc_ProphecyBenchmark3Levels_Node3(s->$v0, s->$v1, s->$v2, s->$v3, s->$v4, s->$v5, x, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels_Node3'_v7(s: $bc_ProphecyBenchmark3Levels_Node3, x: $bc_ProphecyBenchmark3Levels_Node2): $bc_ProphecyBenchmark3Levels_Node3 {
    $bc_ProphecyBenchmark3Levels_Node3(s->$v0, s->$v1, s->$v2, s->$v3, s->$v4, s->$v5, s->$v6, x)
}
function $IsValid'$bc_ProphecyBenchmark3Levels_Node3'(s: $bc_ProphecyBenchmark3Levels_Node3): bool {
    $IsValid'$bc_ProphecyBenchmark3Levels_Node2'(s->$v0)
      && $IsValid'$bc_ProphecyBenchmark3Levels_Node2'(s->$v1)
      && $IsValid'$bc_ProphecyBenchmark3Levels_Node2'(s->$v2)
      && $IsValid'$bc_ProphecyBenchmark3Levels_Node2'(s->$v3)
      && $IsValid'$bc_ProphecyBenchmark3Levels_Node2'(s->$v4)
      && $IsValid'$bc_ProphecyBenchmark3Levels_Node2'(s->$v5)
      && $IsValid'$bc_ProphecyBenchmark3Levels_Node2'(s->$v6)
      && $IsValid'$bc_ProphecyBenchmark3Levels_Node2'(s->$v7)
}
function {:inline} $IsEqual'$bc_ProphecyBenchmark3Levels_Node3'(s1: $bc_ProphecyBenchmark3Levels_Node3, s2: $bc_ProphecyBenchmark3Levels_Node3): bool {
    s1 == s2
}

// fun ProphecyBenchmark3Levels::benchmark_from_scratch [verification] at .\sources\ConditionalBorrowChain.move:91:5+500
procedure {:timeLimit 40} $bc_ProphecyBenchmark3Levels_benchmark_from_scratch$verify(_$t0: int, _$t1: int, _$t2: int) returns ($ret0: $bc_ProphecyBenchmark3Levels_Node3)
{
    // declare local variables
    var $t3: $bc_ProphecyBenchmark3Levels_Node3;
    var $t4: $Mutation (int);
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: int;
    var $t10: int;
    var $t11: int;
    var $t12: $Mutation ($bc_ProphecyBenchmark3Levels_Node3);
    var $t13: $Mutation ($bc_ProphecyBenchmark3Levels_Node2);
    var $t14: $Mutation ($bc_ProphecyBenchmark3Levels_Node1);
    var $t15: $Mutation (int);
    var $t16: int;
    var $t17: int;
    var $t18: int;
    var $t19: bool;
    var $t20: bool;
    var $t21: bool;
    var $t22: bool;
    var $t23: bool;
    var $t24: bool;
    var $t25: bool;
    var $t26: bool;
    var $t27: bool;
    var $t28: bool;
    var $t29: bool;
    var $t30: bool;
    var $t31: bool;
    var $t32: bool;
    var $t33: bool;
    var $t34: bool;
    var $t35: bool;
    var $t36: bool;
    var $t37: bool;
    var $t38: bool;
    var $t39: bool;
    var $t40: bool;
    var $t41: bool;
    var $t42: bool;
    var $t43: bool;
    var $t44: bool;
    var $t45: bool;
    var $t46: bool;
    var $t47: bool;
    var $t48: bool;
    var $t49: bool;
    var $t50: bool;
    var $t51: bool;
    var $t52: bool;
    var $t53: bool;
    var $t54: bool;
    var $t55: bool;
    var $t56: bool;
    var $t57: bool;
    var $t58: bool;
    var $t59: bool;
    var $t60: bool;
    var $t61: bool;
    var $t62: bool;
    var $t63: bool;
    var $t64: bool;
    var $t65: bool;
    var $t66: bool;
    var $t67: bool;
    var $t68: bool;
    var $t69: bool;
    var $t70: bool;
    var $t71: bool;
    var $t72: bool;
    var $t73: bool;
    var $t74: bool;
    var $t75: bool;
    var $t76: bool;
    var $t77: bool;
    var $t78: bool;
    var $t79: bool;
    var $t80: bool;
    var $t81: bool;
    var $t82: bool;
    var $t83: bool;
    var $t84: bool;
    var $t85: bool;
    var $t86: bool;
    var $t87: bool;
    var $t88: bool;
    var $t89: bool;
    var $t90: bool;
    var $t91: bool;
    var $t92: bool;
    var $t93: bool;
    var $t94: bool;
    var $t95: bool;
    var $t96: bool;
    var $t97: bool;
    var $t98: bool;
    var $t99: bool;
    var $t100: bool;
    var $t101: bool;
    var $t102: bool;
    var $t103: bool;
    var $t104: bool;
    var $t105: bool;
    var $t106: bool;
    var $t107: bool;
    var $t108: bool;
    var $t109: bool;
    var $t110: bool;
    var $t111: bool;
    var $t112: bool;
    var $t113: bool;
    var $t114: bool;
    var $t115: bool;
    var $t116: bool;
    var $t117: bool;
    var $t118: bool;
    var $t119: bool;
    var $t120: bool;
    var $t121: bool;
    var $t122: bool;
    var $t123: bool;
    var $t124: bool;
    var $t125: bool;
    var $t126: bool;
    var $t127: bool;
    var $t128: bool;
    var $t129: bool;
    var $t130: bool;
    var $t131: bool;
    var $t132: bool;
    var $t133: bool;
    var $t134: bool;
    var $t135: bool;
    var $t136: bool;
    var $t137: bool;
    var $t138: bool;
    var $t139: bool;
    var $t140: bool;
    var $t141: bool;
    var $t142: bool;
    var $t143: bool;
    var $t144: bool;
    var $t145: bool;
    var $t146: bool;
    var $t147: bool;
    var $t148: bool;
    var $t149: bool;
    var $t150: bool;
    var $t151: bool;
    var $t152: bool;
    var $t153: bool;
    var $t154: bool;
    var $t155: bool;
    var $t156: bool;
    var $t157: bool;
    var $t158: bool;
    var $t159: bool;
    var $t160: bool;
    var $t161: bool;
    var $t162: bool;
    var $t163: bool;
    var $t164: bool;
    var $t165: bool;
    var $t166: bool;
    var $t167: bool;
    var $t168: bool;
    var $t169: bool;
    var $t170: bool;
    var $t171: bool;
    var $t172: bool;
    var $t173: bool;
    var $t174: bool;
    var $t175: bool;
    var $t176: bool;
    var $t177: bool;
    var $t178: bool;
    var $t179: bool;
    var $t180: bool;
    var $t181: bool;
    var $t182: bool;
    var $t183: bool;
    var $t184: bool;
    var $t185: bool;
    var $t186: bool;
    var $t187: bool;
    var $t188: bool;
    var $t189: bool;
    var $t190: bool;
    var $t191: bool;
    var $t192: bool;
    var $t193: bool;
    var $t194: bool;
    var $t195: bool;
    var $t196: bool;
    var $t197: bool;
    var $t198: bool;
    var $t199: bool;
    var $t200: bool;
    var $t201: bool;
    var $t202: bool;
    var $t203: bool;
    var $t204: bool;
    var $t205: bool;
    var $t206: bool;
    var $t207: bool;
    var $t208: bool;
    var $t209: bool;
    var $t210: bool;
    var $t211: bool;
    var $t212: bool;
    var $t213: bool;
    var $t214: bool;
    var $t215: bool;
    var $t216: bool;
    var $t217: bool;
    var $t218: bool;
    var $t219: bool;
    var $t220: bool;
    var $t221: bool;
    var $t222: bool;
    var $t223: bool;
    var $t224: bool;
    var $t225: bool;
    var $t226: bool;
    var $t227: bool;
    var $t228: bool;
    var $t229: bool;
    var $t230: bool;
    var $t231: bool;
    var $t232: bool;
    var $t233: bool;
    var $t234: bool;
    var $t235: bool;
    var $t236: bool;
    var $t237: bool;
    var $t238: bool;
    var $t239: bool;
    var $t240: bool;
    var $t241: bool;
    var $t242: bool;
    var $t243: bool;
    var $t244: bool;
    var $t245: bool;
    var $t246: bool;
    var $t247: bool;
    var $t248: bool;
    var $t249: bool;
    var $t250: bool;
    var $t251: bool;
    var $t252: bool;
    var $t253: bool;
    var $t254: bool;
    var $t255: bool;
    var $t256: bool;
    var $t257: bool;
    var $t258: bool;
    var $t259: bool;
    var $t260: bool;
    var $t261: bool;
    var $t262: bool;
    var $t263: bool;
    var $t264: bool;
    var $t265: bool;
    var $t266: bool;
    var $t267: bool;
    var $t268: bool;
    var $t269: bool;
    var $t270: bool;
    var $t271: bool;
    var $t272: bool;
    var $t273: bool;
    var $t274: bool;
    var $t275: bool;
    var $t276: bool;
    var $t277: bool;
    var $t278: bool;
    var $t279: bool;
    var $t280: bool;
    var $t281: bool;
    var $t282: bool;
    var $t283: bool;
    var $t284: bool;
    var $t285: bool;
    var $t286: bool;
    var $t287: bool;
    var $t288: bool;
    var $t289: bool;
    var $t290: bool;
    var $t291: bool;
    var $t292: bool;
    var $t293: bool;
    var $t294: bool;
    var $t295: bool;
    var $t296: bool;
    var $t297: bool;
    var $t298: bool;
    var $t299: bool;
    var $t300: bool;
    var $t301: bool;
    var $t302: bool;
    var $t303: bool;
    var $t304: bool;
    var $t305: bool;
    var $t306: bool;
    var $t307: bool;
    var $t308: bool;
    var $t309: bool;
    var $t310: bool;
    var $t311: bool;
    var $t312: bool;
    var $t313: bool;
    var $t314: bool;
    var $t315: bool;
    var $t316: bool;
    var $t317: bool;
    var $t318: bool;
    var $t319: bool;
    var $t320: bool;
    var $t321: bool;
    var $t322: bool;
    var $t323: bool;
    var $t324: bool;
    var $t325: bool;
    var $t326: bool;
    var $t327: bool;
    var $t328: bool;
    var $t329: bool;
    var $t330: bool;
    var $t331: bool;
    var $t332: bool;
    var $t333: bool;
    var $t334: bool;
    var $t335: bool;
    var $t336: bool;
    var $t337: bool;
    var $t338: bool;
    var $t339: bool;
    var $t340: bool;
    var $t341: bool;
    var $t342: bool;
    var $t343: bool;
    var $t344: bool;
    var $t345: bool;
    var $t346: bool;
    var $t347: bool;
    var $t348: bool;
    var $t349: bool;
    var $t350: bool;
    var $t351: bool;
    var $t352: bool;
    var $t353: bool;
    var $t354: bool;
    var $t355: bool;
    var $t356: bool;
    var $t357: bool;
    var $t358: bool;
    var $t359: bool;
    var $t360: bool;
    var $t361: bool;
    var $t362: bool;
    var $t363: bool;
    var $t364: bool;
    var $t365: bool;
    var $t366: bool;
    var $t367: bool;
    var $t368: bool;
    var $t369: bool;
    var $t370: bool;
    var $t371: bool;
    var $t372: bool;
    var $t373: bool;
    var $t374: bool;
    var $t375: bool;
    var $t376: bool;
    var $t377: bool;
    var $t378: bool;
    var $t379: bool;
    var $t380: bool;
    var $t381: bool;
    var $t382: bool;
    var $t383: bool;
    var $t384: bool;
    var $t385: bool;
    var $t386: bool;
    var $t387: bool;
    var $t388: bool;
    var $t389: bool;
    var $t390: bool;
    var $t391: bool;
    var $t392: bool;
    var $t393: bool;
    var $t394: bool;
    var $t395: bool;
    var $t396: bool;
    var $t397: bool;
    var $t398: bool;
    var $t399: bool;
    var $t400: bool;
    var $t401: bool;
    var $t402: bool;
    var $t403: bool;
    var $t404: bool;
    var $t405: bool;
    var $t406: bool;
    var $t407: bool;
    var $t408: bool;
    var $t409: bool;
    var $t410: bool;
    var $t411: bool;
    var $t412: bool;
    var $t413: bool;
    var $t414: bool;
    var $t415: bool;
    var $t416: bool;
    var $t417: bool;
    var $t418: bool;
    var $t419: bool;
    var $t420: bool;
    var $t421: bool;
    var $t422: bool;
    var $t423: bool;
    var $t424: bool;
    var $t425: bool;
    var $t426: bool;
    var $t427: bool;
    var $t428: bool;
    var $t429: bool;
    var $t430: bool;
    var $t431: bool;
    var $t432: bool;
    var $t433: bool;
    var $t434: bool;
    var $t435: bool;
    var $t436: bool;
    var $t437: bool;
    var $t438: bool;
    var $t439: bool;
    var $t440: bool;
    var $t441: bool;
    var $t442: bool;
    var $t443: bool;
    var $t444: bool;
    var $t445: bool;
    var $t446: bool;
    var $t447: bool;
    var $t448: bool;
    var $t449: bool;
    var $t450: bool;
    var $t451: bool;
    var $t452: bool;
    var $t453: bool;
    var $t454: bool;
    var $t455: bool;
    var $t456: bool;
    var $t457: bool;
    var $t458: bool;
    var $t459: bool;
    var $t460: bool;
    var $t461: bool;
    var $t462: bool;
    var $t463: bool;
    var $t464: bool;
    var $t465: bool;
    var $t466: bool;
    var $t467: bool;
    var $t468: bool;
    var $t469: bool;
    var $t470: bool;
    var $t471: bool;
    var $t472: bool;
    var $t473: bool;
    var $t474: bool;
    var $t475: bool;
    var $t476: bool;
    var $t477: bool;
    var $t478: bool;
    var $t479: bool;
    var $t480: bool;
    var $t481: bool;
    var $t482: bool;
    var $t483: bool;
    var $t484: bool;
    var $t485: bool;
    var $t486: bool;
    var $t487: bool;
    var $t488: bool;
    var $t489: bool;
    var $t490: bool;
    var $t491: bool;
    var $t492: bool;
    var $t493: bool;
    var $t494: bool;
    var $t495: bool;
    var $t496: bool;
    var $t497: bool;
    var $t498: bool;
    var $t499: bool;
    var $t500: bool;
    var $t501: bool;
    var $t502: bool;
    var $t503: bool;
    var $t504: bool;
    var $t505: bool;
    var $t506: bool;
    var $t507: bool;
    var $t508: bool;
    var $t509: bool;
    var $t510: bool;
    var $t511: bool;
    var $t512: bool;
    var $t513: bool;
    var $t514: bool;
    var $t515: bool;
    var $t516: bool;
    var $t517: bool;
    var $t518: bool;
    var $t519: bool;
    var $t520: bool;
    var $t521: bool;
    var $t522: bool;
    var $t523: bool;
    var $t524: bool;
    var $t525: bool;
    var $t526: bool;
    var $t527: bool;
    var $t528: bool;
    var $t529: bool;
    var $t530: bool;
    var $t531: bool;
    var $t532: bool;
    var $t533: bool;
    var $t534: bool;
    var $t535: bool;
    var $t536: bool;
    var $t537: bool;
    var $t538: bool;
    var $t539: bool;
    var $t540: bool;
    var $t541: bool;
    var $t542: bool;
    var $t543: bool;
    var $t544: bool;
    var $t545: bool;
    var $t546: bool;
    var $t547: bool;
    var $t548: bool;
    var $t549: bool;
    var $t550: bool;
    var $t551: bool;
    var $t552: bool;
    var $t553: bool;
    var $t554: bool;
    var $t555: bool;
    var $t556: bool;
    var $t557: bool;
    var $t558: bool;
    var $t559: bool;
    var $t560: bool;
    var $t561: bool;
    var $t562: bool;
    var $t563: bool;
    var $t564: bool;
    var $t565: bool;
    var $t566: bool;
    var $t567: bool;
    var $t568: bool;
    var $t569: bool;
    var $t570: bool;
    var $t571: bool;
    var $t572: bool;
    var $t573: bool;
    var $t574: bool;
    var $t575: bool;
    var $t576: bool;
    var $t577: bool;
    var $t578: bool;
    var $t579: bool;
    var $t580: bool;
    var $t581: bool;
    var $t582: bool;
    var $t583: bool;
    var $t584: bool;
    var $t585: bool;
    var $t586: bool;
    var $t587: bool;
    var $t588: bool;
    var $t589: bool;
    var $t590: bool;
    var $t591: bool;
    var $t592: bool;
    var $t593: bool;
    var $t594: bool;
    var $t595: bool;
    var $t596: bool;
    var $t597: bool;
    var $t598: bool;
    var $t599: bool;
    var $t600: bool;
    var $t601: bool;
    var $t602: bool;
    var $t603: bool;
    var $t604: bool;
    var $t605: bool;
    var $t606: bool;
    var $t607: bool;
    var $t608: bool;
    var $t609: bool;
    var $t610: bool;
    var $t611: bool;
    var $t612: bool;
    var $t613: bool;
    var $t614: bool;
    var $t615: bool;
    var $t616: bool;
    var $t617: bool;
    var $t618: bool;
    var $t619: bool;
    var $t620: bool;
    var $t621: bool;
    var $t622: bool;
    var $t623: bool;
    var $t624: bool;
    var $t625: bool;
    var $t626: bool;
    var $t627: bool;
    var $t628: bool;
    var $t629: bool;
    var $t630: bool;
    var $t631: bool;
    var $t632: bool;
    var $t633: bool;
    var $t634: bool;
    var $t635: bool;
    var $t636: bool;
    var $t637: bool;
    var $t638: bool;
    var $t639: bool;
    var $t640: bool;
    var $t641: bool;
    var $t642: bool;
    var $t643: bool;
    var $t644: bool;
    var $t645: bool;
    var $t646: bool;
    var $t647: bool;
    var $t648: bool;
    var $t649: bool;
    var $t650: bool;
    var $t651: bool;
    var $t652: bool;
    var $t653: bool;
    var $t654: bool;
    var $t655: bool;
    var $t656: bool;
    var $t657: bool;
    var $t658: bool;
    var $t659: bool;
    var $t660: bool;
    var $t661: bool;
    var $t662: bool;
    var $t663: bool;
    var $t664: bool;
    var $t665: bool;
    var $t666: bool;
    var $t667: bool;
    var $t668: bool;
    var $t669: bool;
    var $t670: bool;
    var $t671: bool;
    var $t672: bool;
    var $t673: bool;
    var $t674: bool;
    var $t675: bool;
    var $t676: bool;
    var $t677: bool;
    var $t678: bool;
    var $t679: bool;
    var $t680: bool;
    var $t681: bool;
    var $t682: bool;
    var $t683: bool;
    var $t684: bool;
    var $t685: bool;
    var $t686: bool;
    var $t687: bool;
    var $t688: bool;
    var $t689: bool;
    var $t690: bool;
    var $t691: bool;
    var $t692: bool;
    var $t693: bool;
    var $t694: bool;
    var $t695: bool;
    var $t696: bool;
    var $t697: bool;
    var $t698: bool;
    var $t699: bool;
    var $t700: bool;
    var $t701: bool;
    var $t702: bool;
    var $t703: bool;
    var $t704: bool;
    var $t705: bool;
    var $t706: bool;
    var $t707: bool;
    var $t708: bool;
    var $t709: bool;
    var $t710: bool;
    var $t711: bool;
    var $t712: bool;
    var $t713: bool;
    var $t714: bool;
    var $t715: bool;
    var $t716: bool;
    var $t717: bool;
    var $t718: bool;
    var $t719: bool;
    var $t720: bool;
    var $t721: bool;
    var $t722: bool;
    var $t723: bool;
    var $t724: bool;
    var $t725: bool;
    var $t726: bool;
    var $t727: bool;
    var $t728: bool;
    var $t729: bool;
    var $t730: bool;
    var $t731: bool;
    var $t732: bool;
    var $t733: bool;
    var $t734: bool;
    var $t735: bool;
    var $t736: bool;
    var $t737: bool;
    var $t738: bool;
    var $t739: bool;
    var $t740: bool;
    var $t741: bool;
    var $t742: bool;
    var $t743: bool;
    var $t744: bool;
    var $t745: bool;
    var $t746: bool;
    var $t747: bool;
    var $t748: bool;
    var $t749: bool;
    var $t750: bool;
    var $t751: bool;
    var $t752: bool;
    var $t753: bool;
    var $t754: bool;
    var $t755: bool;
    var $t756: bool;
    var $t757: bool;
    var $t758: bool;
    var $t759: bool;
    var $t760: bool;
    var $t761: bool;
    var $t762: bool;
    var $t763: bool;
    var $t764: bool;
    var $t765: bool;
    var $t766: bool;
    var $t767: bool;
    var $t768: bool;
    var $t769: bool;
    var $t770: bool;
    var $t771: bool;
    var $t772: bool;
    var $t773: bool;
    var $t774: bool;
    var $t775: bool;
    var $t776: bool;
    var $t777: bool;
    var $t778: bool;
    var $t779: bool;
    var $t780: bool;
    var $t781: bool;
    var $t782: bool;
    var $t783: bool;
    var $t784: bool;
    var $t785: bool;
    var $t786: bool;
    var $t787: bool;
    var $t788: bool;
    var $t789: bool;
    var $t790: bool;
    var $t791: bool;
    var $t792: bool;
    var $t793: bool;
    var $t794: bool;
    var $t795: bool;
    var $t796: bool;
    var $t797: bool;
    var $t798: bool;
    var $t799: bool;
    var $t800: bool;
    var $t801: bool;
    var $t802: bool;
    var $t803: bool;
    var $t804: bool;
    var $t805: bool;
    var $t806: bool;
    var $t807: bool;
    var $t808: bool;
    var $t809: bool;
    var $t810: bool;
    var $t811: bool;
    var $t812: bool;
    var $t813: bool;
    var $t814: bool;
    var $t815: bool;
    var $t816: bool;
    var $t817: bool;
    var $t818: bool;
    var $t819: bool;
    var $t820: bool;
    var $t821: bool;
    var $t822: bool;
    var $t823: bool;
    var $t824: bool;
    var $t825: bool;
    var $t826: bool;
    var $t827: bool;
    var $t828: bool;
    var $t829: bool;
    var $t830: bool;
    var $t831: bool;
    var $t832: bool;
    var $t833: bool;
    var $t834: bool;
    var $t835: bool;
    var $t836: bool;
    var $t837: bool;
    var $t838: bool;
    var $t839: bool;
    var $t840: bool;
    var $t841: bool;
    var $t842: bool;
    var $t843: bool;
    var $t844: bool;
    var $t845: bool;
    var $t846: bool;
    var $t847: bool;
    var $t848: bool;
    var $t849: bool;
    var $t850: bool;
    var $t851: bool;
    var $t852: bool;
    var $t853: bool;
    var $t854: bool;
    var $t855: bool;
    var $t856: bool;
    var $t857: bool;
    var $t858: bool;
    var $t859: bool;
    var $t860: bool;
    var $t861: bool;
    var $t862: bool;
    var $t863: bool;
    var $t864: bool;
    var $t865: bool;
    var $t866: bool;
    var $t867: bool;
    var $t868: bool;
    var $t869: bool;
    var $t870: bool;
    var $t871: bool;
    var $t872: bool;
    var $t873: bool;
    var $t874: bool;
    var $t875: bool;
    var $t876: bool;
    var $t877: bool;
    var $t878: bool;
    var $t879: bool;
    var $t880: bool;
    var $t881: bool;
    var $t882: bool;
    var $t883: bool;
    var $t884: bool;
    var $t885: bool;
    var $t886: bool;
    var $t887: bool;
    var $t888: bool;
    var $t889: bool;
    var $t890: bool;
    var $t891: bool;
    var $t892: bool;
    var $t893: bool;
    var $t894: bool;
    var $t895: bool;
    var $t896: bool;
    var $t897: bool;
    var $t898: bool;
    var $t899: bool;
    var $t900: bool;
    var $t901: bool;
    var $t902: bool;
    var $t903: bool;
    var $t904: bool;
    var $t905: bool;
    var $t906: bool;
    var $t907: bool;
    var $t908: bool;
    var $t909: bool;
    var $t910: bool;
    var $t911: bool;
    var $t912: bool;
    var $t913: bool;
    var $t914: bool;
    var $t915: bool;
    var $t916: bool;
    var $t917: bool;
    var $t918: bool;
    var $t919: bool;
    var $t920: bool;
    var $t921: bool;
    var $t922: bool;
    var $t923: bool;
    var $t924: bool;
    var $t925: bool;
    var $t926: bool;
    var $t927: bool;
    var $t928: bool;
    var $t929: bool;
    var $t930: bool;
    var $t931: bool;
    var $t932: bool;
    var $t933: bool;
    var $t934: bool;
    var $t935: bool;
    var $t936: bool;
    var $t937: bool;
    var $t938: bool;
    var $t939: bool;
    var $t940: bool;
    var $t941: bool;
    var $t942: bool;
    var $t943: bool;
    var $t944: bool;
    var $t945: bool;
    var $t946: bool;
    var $t947: bool;
    var $t948: bool;
    var $t949: bool;
    var $t950: bool;
    var $t951: bool;
    var $t952: bool;
    var $t953: bool;
    var $t954: bool;
    var $t955: bool;
    var $t956: bool;
    var $t957: bool;
    var $t958: bool;
    var $t959: bool;
    var $t960: bool;
    var $t961: bool;
    var $t962: bool;
    var $t963: bool;
    var $t964: bool;
    var $t965: bool;
    var $t966: bool;
    var $t967: bool;
    var $t968: bool;
    var $t969: bool;
    var $t970: bool;
    var $t971: bool;
    var $t972: bool;
    var $t973: bool;
    var $t974: bool;
    var $t975: bool;
    var $t976: bool;
    var $t977: bool;
    var $t978: bool;
    var $t979: bool;
    var $t980: bool;
    var $t981: bool;
    var $t982: bool;
    var $t983: bool;
    var $t984: bool;
    var $t985: bool;
    var $t986: bool;
    var $t987: bool;
    var $t988: bool;
    var $t989: bool;
    var $t990: bool;
    var $t991: bool;
    var $t992: bool;
    var $t993: bool;
    var $t994: bool;
    var $t995: bool;
    var $t996: bool;
    var $t997: bool;
    var $t998: bool;
    var $t999: bool;
    var $t1000: bool;
    var $t1001: bool;
    var $t1002: bool;
    var $t1003: bool;
    var $t1004: bool;
    var $t1005: bool;
    var $t1006: bool;
    var $t1007: bool;
    var $t1008: bool;
    var $t1009: bool;
    var $t1010: bool;
    var $t1011: bool;
    var $t1012: bool;
    var $t1013: bool;
    var $t1014: bool;
    var $t1015: bool;
    var $t1016: bool;
    var $t1017: bool;
    var $t1018: bool;
    var $t1019: bool;
    var $t1020: bool;
    var $t1021: bool;
    var $t1022: bool;
    var $t1023: bool;
    var $t1024: bool;
    var $t1025: bool;
    var $t1026: bool;
    var $t1027: bool;
    var $t1028: bool;
    var $t1029: bool;
    var $t1030: bool;
    var $t1031: bool;
    var $t1032: bool;
    var $t1033: bool;
    var $t1034: bool;
    var $t1035: bool;
    var $t1036: bool;
    var $t1037: bool;
    var $t1038: bool;
    var $t1039: bool;
    var $t1040: bool;
    var $t1041: bool;
    var $t1042: bool;
    var $t1043: bool;
    var $t1044: bool;
    var $t1045: bool;
    var $t1046: bool;
    var $t1047: bool;
    var $t1048: bool;
    var $t1049: bool;
    var $t1050: bool;
    var $t1051: bool;
    var $t1052: bool;
    var $t1053: bool;
    var $t1054: bool;
    var $t1055: bool;
    var $t1056: bool;
    var $t1057: bool;
    var $t1058: bool;
    var $t1059: bool;
    var $t1060: bool;
    var $t1061: bool;
    var $t1062: bool;
    var $t1063: bool;
    var $t1064: bool;
    var $t1065: bool;
    var $t1066: bool;
    var $t1067: bool;
    var $t1068: bool;
    var $t1069: bool;
    var $t1070: bool;
    var $t1071: bool;
    var $t1072: bool;
    var $t1073: bool;
    var $t1074: bool;
    var $t1075: bool;
    var $t1076: bool;
    var $t1077: bool;
    var $t1078: bool;
    var $t1079: bool;
    var $t1080: bool;
    var $t1081: bool;
    var $t1082: bool;
    var $t1083: bool;
    var $t1084: bool;
    var $t1085: bool;
    var $t1086: bool;
    var $t1087: bool;
    var $t1088: bool;
    var $t1089: bool;
    var $t1090: bool;
    var $t1091: bool;
    var $t1092: bool;
    var $t1093: bool;
    var $t1094: bool;
    var $t1095: bool;
    var $t1096: bool;
    var $t1097: bool;
    var $t1098: bool;
    var $t1099: bool;
    var $t1100: bool;
    var $t1101: bool;
    var $t1102: bool;
    var $t1103: bool;
    var $t1104: bool;
    var $t1105: bool;
    var $t1106: bool;
    var $t1107: bool;
    var $t1108: bool;
    var $t1109: bool;
    var $t1110: bool;
    var $t1111: bool;
    var $t1112: bool;
    var $t1113: bool;
    var $t1114: bool;
    var $t1115: bool;
    var $t1116: bool;
    var $t1117: bool;
    var $t1118: bool;
    var $t1119: bool;
    var $t1120: bool;
    var $t1121: bool;
    var $t1122: bool;
    var $t1123: bool;
    var $t1124: bool;
    var $t1125: bool;
    var $t1126: bool;
    var $t1127: bool;
    var $t1128: bool;
    var $t1129: bool;
    var $t1130: bool;
    var $t1131: bool;
    var $t1132: bool;
    var $t1133: bool;
    var $t1134: bool;
    var $t1135: bool;
    var $t1136: bool;
    var $t1137: bool;
    var $t1138: bool;
    var $t1139: bool;
    var $t1140: bool;
    var $t1141: bool;
    var $t1142: bool;
    var $t1143: bool;
    var $t1144: bool;
    var $t1145: bool;
    var $t1146: bool;
    var $t1147: bool;
    var $t1148: bool;
    var $t1149: bool;
    var $t1150: bool;
    var $t1151: bool;
    var $t1152: bool;
    var $t1153: bool;
    var $t1154: bool;
    var $t1155: bool;
    var $t1156: bool;
    var $t1157: bool;
    var $t1158: bool;
    var $t1159: bool;
    var $t1160: bool;
    var $t1161: bool;
    var $t1162: bool;
    var $t1163: bool;
    var $t1164: bool;
    var $t1165: bool;
    var $t1166: bool;
    var $t1167: bool;
    var $t1168: bool;
    var $t1169: bool;
    var $t1170: bool;
    var $t1171: bool;
    var $t1172: bool;
    var $t1173: bool;
    var $t1174: bool;
    var $t1175: bool;
    var $t1176: bool;
    var $t1177: bool;
    var $t1178: bool;
    var $t1179: bool;
    var $t1180: bool;
    var $t1181: bool;
    var $t1182: bool;
    var $t1183: bool;
    var $t1184: bool;
    var $t1185: bool;
    var $t1186: bool;
    var $t1187: bool;
    var $t1188: bool;
    var $t1189: bool;
    var $t1190: bool;
    var $t1191: bool;
    var $t1192: bool;
    var $t1193: bool;
    var $t1194: bool;
    var $t1195: bool;
    var $t1196: bool;
    var $t1197: bool;
    var $t1198: bool;
    var $t1199: bool;
    var $t1200: bool;
    var $t1201: bool;
    var $t1202: bool;
    var $t1203: bool;
    var $t1204: bool;
    var $t1205: bool;
    var $t1206: bool;
    var $t1207: bool;
    var $t1208: bool;
    var $t1209: bool;
    var $t1210: bool;
    var $t1211: bool;
    var $t1212: bool;
    var $t1213: bool;
    var $t1214: bool;
    var $t1215: bool;
    var $t1216: bool;
    var $t1217: bool;
    var $t1218: bool;
    var $t1219: bool;
    var $t1220: bool;
    var $t1221: bool;
    var $t1222: bool;
    var $t1223: bool;
    var $t1224: bool;
    var $t1225: bool;
    var $t1226: bool;
    var $t1227: bool;
    var $t1228: bool;
    var $t1229: bool;
    var $t1230: bool;
    var $t1231: bool;
    var $t1232: bool;
    var $t1233: bool;
    var $t1234: bool;
    var $t1235: bool;
    var $t1236: bool;
    var $t1237: bool;
    var $t1238: bool;
    var $t1239: bool;
    var $t1240: bool;
    var $t1241: bool;
    var $t1242: bool;
    var $t1243: bool;
    var $t1244: bool;
    var $t1245: bool;
    var $t1246: bool;
    var $t1247: bool;
    var $t1248: bool;
    var $t1249: bool;
    var $t1250: bool;
    var $t1251: bool;
    var $t1252: bool;
    var $t1253: bool;
    var $t1254: bool;
    var $t1255: bool;
    var $t1256: bool;
    var $t1257: bool;
    var $t1258: bool;
    var $t1259: bool;
    var $t1260: bool;
    var $t1261: bool;
    var $t1262: bool;
    var $t1263: bool;
    var $t1264: bool;
    var $t1265: bool;
    var $t1266: bool;
    var $t1267: bool;
    var $t1268: bool;
    var $t1269: bool;
    var $t1270: bool;
    var $t1271: bool;
    var $t1272: bool;
    var $t1273: bool;
    var $t1274: bool;
    var $t1275: bool;
    var $t1276: bool;
    var $t1277: bool;
    var $t1278: bool;
    var $t1279: bool;
    var $t1280: bool;
    var $t1281: bool;
    var $t1282: bool;
    var $t1283: bool;
    var $t1284: bool;
    var $t1285: bool;
    var $t1286: bool;
    var $t1287: bool;
    var $t1288: bool;
    var $t1289: bool;
    var $t1290: bool;
    var $t1291: bool;
    var $t1292: bool;
    var $t1293: bool;
    var $t1294: bool;
    var $t1295: bool;
    var $t1296: bool;
    var $t1297: bool;
    var $t1298: bool;
    var $t1299: bool;
    var $t1300: bool;
    var $t1301: bool;
    var $t1302: bool;
    var $t1303: bool;
    var $t1304: bool;
    var $t1305: bool;
    var $t1306: bool;
    var $t1307: bool;
    var $t1308: bool;
    var $t1309: bool;
    var $t1310: bool;
    var $t1311: bool;
    var $t1312: bool;
    var $t1313: bool;
    var $t1314: bool;
    var $t1315: bool;
    var $t1316: bool;
    var $t1317: bool;
    var $t1318: bool;
    var $t1319: bool;
    var $t1320: bool;
    var $t1321: bool;
    var $t1322: bool;
    var $t1323: bool;
    var $t1324: bool;
    var $t1325: bool;
    var $t1326: bool;
    var $t1327: bool;
    var $t1328: bool;
    var $t1329: bool;
    var $t1330: bool;
    var $t1331: bool;
    var $t1332: bool;
    var $t1333: bool;
    var $t1334: bool;
    var $t1335: bool;
    var $t1336: bool;
    var $t1337: bool;
    var $t1338: bool;
    var $t1339: bool;
    var $t1340: bool;
    var $t1341: bool;
    var $t1342: bool;
    var $t1343: bool;
    var $t1344: bool;
    var $t1345: bool;
    var $t1346: bool;
    var $t1347: bool;
    var $t1348: bool;
    var $t1349: bool;
    var $t1350: bool;
    var $t1351: bool;
    var $t1352: bool;
    var $t1353: bool;
    var $t1354: bool;
    var $t1355: bool;
    var $t1356: bool;
    var $t1357: bool;
    var $t1358: bool;
    var $t1359: bool;
    var $t1360: bool;
    var $t1361: bool;
    var $t1362: bool;
    var $t1363: bool;
    var $t1364: bool;
    var $t1365: bool;
    var $t1366: bool;
    var $t1367: bool;
    var $t1368: bool;
    var $t1369: bool;
    var $t1370: bool;
    var $t1371: bool;
    var $t1372: bool;
    var $t1373: bool;
    var $t1374: bool;
    var $t1375: bool;
    var $t1376: bool;
    var $t1377: bool;
    var $t1378: bool;
    var $t1379: bool;
    var $t1380: bool;
    var $t1381: bool;
    var $t1382: bool;
    var $t1383: bool;
    var $t1384: bool;
    var $t1385: bool;
    var $t1386: bool;
    var $t1387: bool;
    var $t1388: bool;
    var $t1389: bool;
    var $t1390: bool;
    var $t1391: bool;
    var $t1392: bool;
    var $t1393: bool;
    var $t1394: bool;
    var $t1395: bool;
    var $t1396: bool;
    var $t1397: bool;
    var $t1398: bool;
    var $t1399: bool;
    var $t1400: bool;
    var $t1401: bool;
    var $t1402: bool;
    var $t1403: bool;
    var $t1404: bool;
    var $t1405: bool;
    var $t1406: bool;
    var $t1407: bool;
    var $t1408: bool;
    var $t1409: bool;
    var $t1410: bool;
    var $t1411: bool;
    var $t1412: bool;
    var $t1413: bool;
    var $t1414: bool;
    var $t1415: bool;
    var $t1416: bool;
    var $t1417: bool;
    var $t1418: bool;
    var $t1419: bool;
    var $t1420: bool;
    var $t1421: bool;
    var $t1422: bool;
    var $t1423: bool;
    var $t1424: bool;
    var $t1425: bool;
    var $t1426: bool;
    var $t1427: bool;
    var $t1428: bool;
    var $t1429: bool;
    var $t1430: bool;
    var $t1431: bool;
    var $t1432: bool;
    var $t1433: bool;
    var $t1434: bool;
    var $t1435: bool;
    var $t1436: bool;
    var $t1437: bool;
    var $t1438: bool;
    var $t1439: bool;
    var $t1440: bool;
    var $t1441: bool;
    var $t1442: bool;
    var $t1443: bool;
    var $t1444: bool;
    var $t1445: bool;
    var $t1446: bool;
    var $t1447: bool;
    var $t1448: bool;
    var $t1449: bool;
    var $t1450: bool;
    var $t1451: bool;
    var $t1452: bool;
    var $t1453: bool;
    var $t1454: bool;
    var $t1455: bool;
    var $t1456: bool;
    var $t1457: bool;
    var $t1458: bool;
    var $t1459: bool;
    var $t1460: bool;
    var $t1461: bool;
    var $t1462: bool;
    var $t1463: bool;
    var $t1464: bool;
    var $t1465: bool;
    var $t1466: bool;
    var $t1467: bool;
    var $t1468: bool;
    var $t1469: bool;
    var $t1470: bool;
    var $t1471: bool;
    var $t1472: bool;
    var $t1473: bool;
    var $t1474: bool;
    var $t1475: bool;
    var $t1476: bool;
    var $t1477: bool;
    var $t1478: bool;
    var $t1479: bool;
    var $t1480: bool;
    var $t1481: bool;
    var $t1482: bool;
    var $t1483: bool;
    var $t1484: bool;
    var $t1485: bool;
    var $t1486: bool;
    var $t1487: bool;
    var $t1488: bool;
    var $t1489: bool;
    var $t1490: bool;
    var $t1491: bool;
    var $t1492: bool;
    var $t1493: bool;
    var $t1494: bool;
    var $t1495: bool;
    var $t1496: bool;
    var $t1497: bool;
    var $t1498: bool;
    var $t1499: bool;
    var $t1500: bool;
    var $t1501: bool;
    var $t1502: bool;
    var $t1503: bool;
    var $t1504: bool;
    var $t1505: bool;
    var $t1506: bool;
    var $t1507: bool;
    var $t1508: bool;
    var $t1509: bool;
    var $t1510: bool;
    var $t1511: bool;
    var $t1512: bool;
    var $t1513: bool;
    var $t1514: bool;
    var $t1515: bool;
    var $t1516: bool;
    var $t1517: bool;
    var $t1518: bool;
    var $t1519: bool;
    var $t1520: bool;
    var $t1521: bool;
    var $t1522: bool;
    var $t1523: bool;
    var $t1524: bool;
    var $t1525: bool;
    var $t1526: bool;
    var $t1527: bool;
    var $t1528: bool;
    var $t1529: bool;
    var $t1530: bool;
    var $t1531: bool;
    var $t1532: bool;
    var $t1533: bool;
    var $t1534: bool;
    var $t1535: bool;
    var $t1536: bool;
    var $t1537: bool;
    var $t1538: bool;
    var $t1539: bool;
    var $t1540: bool;
    var $t1541: bool;
    var $t1542: bool;
    var $t1543: bool;
    var $t1544: bool;
    var $t1545: bool;
    var $t1546: bool;
    var $t1547: bool;
    var $t1548: bool;
    var $t1549: bool;
    var $t1550: bool;
    var $t1551: bool;
    var $t1552: bool;
    var $t1553: bool;
    var $t1554: bool;
    var $t1555: bool;
    var $t1556: bool;
    var $t1557: bool;
    var $t1558: bool;
    var $t1559: bool;
    var $t1560: bool;
    var $t1561: bool;
    var $t1562: bool;
    var $t1563: bool;
    var $t1564: bool;
    var $t1565: bool;
    var $t1566: bool;
    var $t1567: bool;
    var $t1568: bool;
    var $t1569: bool;
    var $t1570: bool;
    var $t1571: bool;
    var $t1572: bool;
    var $t1573: bool;
    var $t1574: bool;
    var $t1575: bool;
    var $t1576: bool;
    var $t1577: bool;
    var $t1578: bool;
    var $t1579: bool;
    var $t1580: bool;
    var $t1581: bool;
    var $t1582: bool;
    var $t1583: bool;
    var $t1584: bool;
    var $t1585: bool;
    var $t1586: bool;
    var $t1587: bool;
    var $t1588: bool;
    var $t1589: bool;
    var $t1590: bool;
    var $t1591: bool;
    var $t1592: bool;
    var $t1593: bool;
    var $t1594: bool;
    var $t1595: bool;
    var $t1596: bool;
    var $t1597: bool;
    var $t1598: bool;
    var $t1599: bool;
    var $t1600: bool;
    var $t1601: bool;
    var $t1602: bool;
    var $t1603: bool;
    var $t1604: bool;
    var $t1605: bool;
    var $t1606: bool;
    var $t1607: bool;
    var $t1608: bool;
    var $t1609: bool;
    var $t1610: bool;
    var $t1611: bool;
    var $t1612: bool;
    var $t1613: bool;
    var $t1614: bool;
    var $t1615: bool;
    var $t1616: bool;
    var $t1617: bool;
    var $t1618: bool;
    var $t1619: bool;
    var $t1620: bool;
    var $t1621: bool;
    var $t1622: bool;
    var $t1623: bool;
    var $t1624: bool;
    var $t1625: bool;
    var $t1626: bool;
    var $t1627: bool;
    var $t1628: bool;
    var $t1629: bool;
    var $t1630: bool;
    var $t1631: bool;
    var $t1632: bool;
    var $t1633: bool;
    var $t1634: bool;
    var $t1635: bool;
    var $t1636: bool;
    var $t1637: bool;
    var $t1638: bool;
    var $t1639: bool;
    var $t1640: bool;
    var $t1641: bool;
    var $t1642: bool;
    var $t1643: bool;
    var $t1644: bool;
    var $t1645: bool;
    var $t1646: bool;
    var $t1647: bool;
    var $t1648: bool;
    var $t1649: bool;
    var $t1650: bool;
    var $t1651: bool;
    var $t1652: bool;
    var $t1653: bool;
    var $t1654: bool;
    var $t1655: bool;
    var $t1656: bool;
    var $t1657: bool;
    var $t1658: bool;
    var $t1659: bool;
    var $t1660: bool;
    var $t1661: bool;
    var $t1662: bool;
    var $t1663: bool;
    var $t1664: bool;
    var $t1665: bool;
    var $t1666: bool;
    var $t1667: bool;
    var $t1668: bool;
    var $t1669: bool;
    var $t1670: bool;
    var $t1671: bool;
    var $t1672: bool;
    var $t1673: bool;
    var $t1674: bool;
    var $t1675: bool;
    var $t1676: bool;
    var $t1677: bool;
    var $t1678: bool;
    var $t1679: bool;
    var $t1680: bool;
    var $t1681: bool;
    var $t1682: bool;
    var $t1683: bool;
    var $t1684: bool;
    var $t1685: bool;
    var $t1686: bool;
    var $t1687: bool;
    var $t1688: bool;
    var $t1689: bool;
    var $t1690: bool;
    var $t1691: bool;
    var $t1692: bool;
    var $t1693: bool;
    var $t1694: bool;
    var $t1695: bool;
    var $t1696: bool;
    var $t1697: bool;
    var $t1698: bool;
    var $t1699: bool;
    var $t1700: bool;
    var $t1701: bool;
    var $t1702: bool;
    var $t1703: bool;
    var $t1704: bool;
    var $t1705: bool;
    var $t1706: bool;
    var $t1707: bool;
    var $t1708: bool;
    var $t1709: bool;
    var $t1710: bool;
    var $t1711: bool;
    var $t1712: bool;
    var $t1713: bool;
    var $t1714: bool;
    var $t1715: bool;
    var $t1716: bool;
    var $t1717: bool;
    var $t1718: bool;
    var $t1719: bool;
    var $t1720: bool;
    var $t1721: bool;
    var $t1722: bool;
    var $t1723: bool;
    var $t1724: bool;
    var $t1725: bool;
    var $t1726: bool;
    var $t1727: bool;
    var $t1728: bool;
    var $t1729: bool;
    var $t1730: bool;
    var $t1731: bool;
    var $t1732: bool;
    var $t1733: bool;
    var $t1734: $bc_ProphecyBenchmark3Levels_Node3;
    var $t0: int;
    var $t1: int;
    var $t2: int;
    var $temp_0'$bc_ProphecyBenchmark3Levels_Node3': $bc_ProphecyBenchmark3Levels_Node3;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at .\sources\ConditionalBorrowChain.move:91:5+1
    assume {:print "$at(3,3072,3073)"} true;
    assume $IsValid'u64'($t0);

    // assume WellFormed($t1) at .\sources\ConditionalBorrowChain.move:91:5+1
    assume $IsValid'u64'($t1);

    // assume WellFormed($t2) at .\sources\ConditionalBorrowChain.move:91:5+1
    assume $IsValid'u64'($t2);

    // trace_local[c3]($t0) at .\sources\ConditionalBorrowChain.move:91:5+1
    assume {:print "$track_local(2,0,0):", $t0} $t0 == $t0;

    // trace_local[c2]($t1) at .\sources\ConditionalBorrowChain.move:91:5+1
    assume {:print "$track_local(2,0,1):", $t1} $t1 == $t1;

    // trace_local[c1]($t2) at .\sources\ConditionalBorrowChain.move:91:5+1
    assume {:print "$track_local(2,0,2):", $t2} $t2 == $t2;

    // $t3 := ProphecyBenchmark3Levels::new_node3() on_abort goto L688 with $t5 at .\sources\ConditionalBorrowChain.move:94:20+11
    assume {:print "$at(3,3175,3186)"} true;
    call $t3 := $bc_ProphecyBenchmark3Levels_new_node3();
    if ($abort_flag) {
        assume {:print "$at(3,3175,3186)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,0):", $t5} $t5 == $t5;
        goto L688;
    }

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:94:20+11
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // $t6 := 8 at .\sources\ConditionalBorrowChain.move:96:25+1
    assume {:print "$at(3,3221,3222)"} true;
    $t6 := 8;
    assume $IsValid'u64'($t6);

    // $t7 := %($t0, $t6) on_abort goto L688 with $t5 at .\sources\ConditionalBorrowChain.move:96:20+6
    call $t7 := $Mod($t0, $t6);
    if ($abort_flag) {
        assume {:print "$at(3,3216,3222)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,0):", $t5} $t5 == $t5;
        goto L688;
    }

    // trace_local[c3]($t7) at .\sources\ConditionalBorrowChain.move:96:20+6
    assume {:print "$track_local(2,0,0):", $t7} $t7 == $t7;

    // $t8 := 8 at .\sources\ConditionalBorrowChain.move:97:25+1
    assume {:print "$at(3,3248,3249)"} true;
    $t8 := 8;
    assume $IsValid'u64'($t8);

    // $t9 := %($t1, $t8) on_abort goto L688 with $t5 at .\sources\ConditionalBorrowChain.move:97:20+6
    call $t9 := $Mod($t1, $t8);
    if ($abort_flag) {
        assume {:print "$at(3,3243,3249)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,0):", $t5} $t5 == $t5;
        goto L688;
    }

    // trace_local[c2]($t9) at .\sources\ConditionalBorrowChain.move:97:20+6
    assume {:print "$track_local(2,0,1):", $t9} $t9 == $t9;

    // $t10 := 8 at .\sources\ConditionalBorrowChain.move:98:25+1
    assume {:print "$at(3,3275,3276)"} true;
    $t10 := 8;
    assume $IsValid'u64'($t10);

    // $t11 := %($t2, $t10) on_abort goto L688 with $t5 at .\sources\ConditionalBorrowChain.move:98:20+6
    call $t11 := $Mod($t2, $t10);
    if ($abort_flag) {
        assume {:print "$at(3,3270,3276)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,0):", $t5} $t5 == $t5;
        goto L688;
    }

    // trace_local[c1]($t11) at .\sources\ConditionalBorrowChain.move:98:20+6
    assume {:print "$track_local(2,0,2):", $t11} $t11 == $t11;

    // $t12 := borrow_local($t3) at .\sources\ConditionalBorrowChain.move:100:22+9
    assume {:print "$at(3,3300,3309)"} true;
    $t12 := $Mutation($Local(3), EmptyVec(), $t3);

    // $t13 := ProphecyBenchmark3Levels::select_n2($t12, $t7) on_abort goto L688 with $t5 at .\sources\ConditionalBorrowChain.move:103:22+23
    assume {:print "$at(3,3397,3420)"} true;
    call $t13,$t12 := $bc_ProphecyBenchmark3Levels_select_n2($t12, $t7);
    if ($abort_flag) {
        assume {:print "$at(3,3397,3420)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,0):", $t5} $t5 == $t5;
        goto L688;
    }

    // $t14 := ProphecyBenchmark3Levels::select_n1($t13, $t9) on_abort goto L688 with $t5 at .\sources\ConditionalBorrowChain.move:104:22+23
    assume {:print "$at(3,3443,3466)"} true;
    call $t14,$t13 := $bc_ProphecyBenchmark3Levels_select_n1($t13, $t9);
    if ($abort_flag) {
        assume {:print "$at(3,3443,3466)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,0):", $t5} $t5 == $t5;
        goto L688;
    }

    // $t15 := ProphecyBenchmark3Levels::select_leaf($t14, $t11) on_abort goto L688 with $t5 at .\sources\ConditionalBorrowChain.move:105:24+25
    assume {:print "$at(3,3491,3516)"} true;
    call $t15,$t14 := $bc_ProphecyBenchmark3Levels_select_leaf($t14, $t11);
    if ($abort_flag) {
        assume {:print "$at(3,3491,3516)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,0):", $t5} $t5 == $t5;
        goto L688;
    }

    // trace_local[leaf_ref]($t15) at .\sources\ConditionalBorrowChain.move:105:24+25
    $temp_0'u64' := $Dereference($t15);
    assume {:print "$track_local(2,0,4):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t16 := read_ref($t15) at .\sources\ConditionalBorrowChain.move:106:21+9
    assume {:print "$at(3,3538,3547)"} true;
    $t16 := $Dereference($t15);

    // $t17 := 1 at .\sources\ConditionalBorrowChain.move:106:33+1
    $t17 := 1;
    assume $IsValid'u64'($t17);

    // $t18 := +($t16, $t17) on_abort goto L688 with $t5 at .\sources\ConditionalBorrowChain.move:106:21+13
    call $t18 := $AddU64($t16, $t17);
    if ($abort_flag) {
        assume {:print "$at(3,3538,3551)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,0):", $t5} $t5 == $t5;
        goto L688;
    }

    // write_ref($t15, $t18) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t15 := $UpdateMutation($t15, $t18);

    // $t19 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t19 := $IsParentMutation($t14, 0, $t15);

    // $t20 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t20 := $IsParentMutation($t13, 0, $t14);

    // $t21 := &&($t19, $t20) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t21 := $And($t19, $t20);

    // $t22 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t22 := $IsParentMutation($t12, 0, $t13);

    // $t23 := &&($t21, $t22) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t23 := $And($t21, $t22);

    // if ($t23) goto L1 else goto L2 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t23) { goto L1; } else { goto L2; }

    // label L1 at .\sources\ConditionalBorrowChain.move:106:9+25
L1:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L2 at .\sources\ConditionalBorrowChain.move:106:9+25
L2:

    // $t24 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t24 := $IsParentMutation($t14, 0, $t15);

    // $t25 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t25 := $IsParentMutation($t13, 0, $t14);

    // $t26 := &&($t24, $t25) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t26 := $And($t24, $t25);

    // $t27 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t27 := $IsParentMutation($t12, 1, $t13);

    // $t28 := &&($t26, $t27) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t28 := $And($t26, $t27);

    // if ($t28) goto L3 else goto L4 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t28) { goto L3; } else { goto L4; }

    // label L3 at .\sources\ConditionalBorrowChain.move:106:9+25
L3:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L4 at .\sources\ConditionalBorrowChain.move:106:9+25
L4:

    // $t29 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t29 := $IsParentMutation($t14, 0, $t15);

    // $t30 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t30 := $IsParentMutation($t13, 0, $t14);

    // $t31 := &&($t29, $t30) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t31 := $And($t29, $t30);

    // $t32 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t32 := $IsParentMutation($t12, 2, $t13);

    // $t33 := &&($t31, $t32) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t33 := $And($t31, $t32);

    // if ($t33) goto L5 else goto L6 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t33) { goto L5; } else { goto L6; }

    // label L5 at .\sources\ConditionalBorrowChain.move:106:9+25
L5:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L6 at .\sources\ConditionalBorrowChain.move:106:9+25
L6:

    // $t34 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t34 := $IsParentMutation($t14, 0, $t15);

    // $t35 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t35 := $IsParentMutation($t13, 0, $t14);

    // $t36 := &&($t34, $t35) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t36 := $And($t34, $t35);

    // $t37 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t37 := $IsParentMutation($t12, 3, $t13);

    // $t38 := &&($t36, $t37) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t38 := $And($t36, $t37);

    // if ($t38) goto L7 else goto L8 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t38) { goto L7; } else { goto L8; }

    // label L7 at .\sources\ConditionalBorrowChain.move:106:9+25
L7:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L8 at .\sources\ConditionalBorrowChain.move:106:9+25
L8:

    // $t39 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t39 := $IsParentMutation($t14, 0, $t15);

    // $t40 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t40 := $IsParentMutation($t13, 0, $t14);

    // $t41 := &&($t39, $t40) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t41 := $And($t39, $t40);

    // $t42 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t42 := $IsParentMutation($t12, 4, $t13);

    // $t43 := &&($t41, $t42) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t43 := $And($t41, $t42);

    // if ($t43) goto L9 else goto L10 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t43) { goto L9; } else { goto L10; }

    // label L9 at .\sources\ConditionalBorrowChain.move:106:9+25
L9:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L10 at .\sources\ConditionalBorrowChain.move:106:9+25
L10:

    // $t44 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t44 := $IsParentMutation($t14, 0, $t15);

    // $t45 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t45 := $IsParentMutation($t13, 0, $t14);

    // $t46 := &&($t44, $t45) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t46 := $And($t44, $t45);

    // $t47 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t47 := $IsParentMutation($t12, 5, $t13);

    // $t48 := &&($t46, $t47) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t48 := $And($t46, $t47);

    // if ($t48) goto L11 else goto L12 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t48) { goto L11; } else { goto L12; }

    // label L11 at .\sources\ConditionalBorrowChain.move:106:9+25
L11:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L12 at .\sources\ConditionalBorrowChain.move:106:9+25
L12:

    // $t49 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t49 := $IsParentMutation($t14, 0, $t15);

    // $t50 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t50 := $IsParentMutation($t13, 0, $t14);

    // $t51 := &&($t49, $t50) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t51 := $And($t49, $t50);

    // $t52 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t52 := $IsParentMutation($t12, 6, $t13);

    // $t53 := &&($t51, $t52) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t53 := $And($t51, $t52);

    // if ($t53) goto L13 else goto L14 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t53) { goto L13; } else { goto L14; }

    // label L13 at .\sources\ConditionalBorrowChain.move:106:9+25
L13:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L14 at .\sources\ConditionalBorrowChain.move:106:9+25
L14:

    // $t54 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t54 := $IsParentMutation($t14, 0, $t15);

    // $t55 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t55 := $IsParentMutation($t13, 1, $t14);

    // $t56 := &&($t54, $t55) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t56 := $And($t54, $t55);

    // $t57 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t57 := $IsParentMutation($t12, 0, $t13);

    // $t58 := &&($t56, $t57) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t58 := $And($t56, $t57);

    // if ($t58) goto L15 else goto L16 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t58) { goto L15; } else { goto L16; }

    // label L15 at .\sources\ConditionalBorrowChain.move:106:9+25
L15:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L16 at .\sources\ConditionalBorrowChain.move:106:9+25
L16:

    // $t59 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t59 := $IsParentMutation($t14, 0, $t15);

    // $t60 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t60 := $IsParentMutation($t13, 1, $t14);

    // $t61 := &&($t59, $t60) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t61 := $And($t59, $t60);

    // $t62 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t62 := $IsParentMutation($t12, 1, $t13);

    // $t63 := &&($t61, $t62) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t63 := $And($t61, $t62);

    // if ($t63) goto L17 else goto L18 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t63) { goto L17; } else { goto L18; }

    // label L17 at .\sources\ConditionalBorrowChain.move:106:9+25
L17:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L18 at .\sources\ConditionalBorrowChain.move:106:9+25
L18:

    // $t64 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t64 := $IsParentMutation($t14, 0, $t15);

    // $t65 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t65 := $IsParentMutation($t13, 1, $t14);

    // $t66 := &&($t64, $t65) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t66 := $And($t64, $t65);

    // $t67 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t67 := $IsParentMutation($t12, 2, $t13);

    // $t68 := &&($t66, $t67) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t68 := $And($t66, $t67);

    // if ($t68) goto L19 else goto L20 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t68) { goto L19; } else { goto L20; }

    // label L19 at .\sources\ConditionalBorrowChain.move:106:9+25
L19:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L20 at .\sources\ConditionalBorrowChain.move:106:9+25
L20:

    // $t69 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t69 := $IsParentMutation($t14, 0, $t15);

    // $t70 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t70 := $IsParentMutation($t13, 1, $t14);

    // $t71 := &&($t69, $t70) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t71 := $And($t69, $t70);

    // $t72 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t72 := $IsParentMutation($t12, 3, $t13);

    // $t73 := &&($t71, $t72) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t73 := $And($t71, $t72);

    // if ($t73) goto L21 else goto L22 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t73) { goto L21; } else { goto L22; }

    // label L21 at .\sources\ConditionalBorrowChain.move:106:9+25
L21:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L22 at .\sources\ConditionalBorrowChain.move:106:9+25
L22:

    // $t74 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t74 := $IsParentMutation($t14, 0, $t15);

    // $t75 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t75 := $IsParentMutation($t13, 1, $t14);

    // $t76 := &&($t74, $t75) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t76 := $And($t74, $t75);

    // $t77 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t77 := $IsParentMutation($t12, 4, $t13);

    // $t78 := &&($t76, $t77) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t78 := $And($t76, $t77);

    // if ($t78) goto L23 else goto L24 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t78) { goto L23; } else { goto L24; }

    // label L23 at .\sources\ConditionalBorrowChain.move:106:9+25
L23:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L24 at .\sources\ConditionalBorrowChain.move:106:9+25
L24:

    // $t79 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t79 := $IsParentMutation($t14, 0, $t15);

    // $t80 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t80 := $IsParentMutation($t13, 1, $t14);

    // $t81 := &&($t79, $t80) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t81 := $And($t79, $t80);

    // $t82 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t82 := $IsParentMutation($t12, 5, $t13);

    // $t83 := &&($t81, $t82) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t83 := $And($t81, $t82);

    // if ($t83) goto L25 else goto L26 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t83) { goto L25; } else { goto L26; }

    // label L25 at .\sources\ConditionalBorrowChain.move:106:9+25
L25:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L26 at .\sources\ConditionalBorrowChain.move:106:9+25
L26:

    // $t84 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t84 := $IsParentMutation($t14, 0, $t15);

    // $t85 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t85 := $IsParentMutation($t13, 1, $t14);

    // $t86 := &&($t84, $t85) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t86 := $And($t84, $t85);

    // $t87 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t87 := $IsParentMutation($t12, 6, $t13);

    // $t88 := &&($t86, $t87) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t88 := $And($t86, $t87);

    // if ($t88) goto L27 else goto L28 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t88) { goto L27; } else { goto L28; }

    // label L27 at .\sources\ConditionalBorrowChain.move:106:9+25
L27:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L28 at .\sources\ConditionalBorrowChain.move:106:9+25
L28:

    // $t89 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t89 := $IsParentMutation($t14, 0, $t15);

    // $t90 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t90 := $IsParentMutation($t13, 2, $t14);

    // $t91 := &&($t89, $t90) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t91 := $And($t89, $t90);

    // $t92 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t92 := $IsParentMutation($t12, 0, $t13);

    // $t93 := &&($t91, $t92) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t93 := $And($t91, $t92);

    // if ($t93) goto L29 else goto L30 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t93) { goto L29; } else { goto L30; }

    // label L29 at .\sources\ConditionalBorrowChain.move:106:9+25
L29:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L30 at .\sources\ConditionalBorrowChain.move:106:9+25
L30:

    // $t94 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t94 := $IsParentMutation($t14, 0, $t15);

    // $t95 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t95 := $IsParentMutation($t13, 2, $t14);

    // $t96 := &&($t94, $t95) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t96 := $And($t94, $t95);

    // $t97 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t97 := $IsParentMutation($t12, 1, $t13);

    // $t98 := &&($t96, $t97) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t98 := $And($t96, $t97);

    // if ($t98) goto L31 else goto L32 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t98) { goto L31; } else { goto L32; }

    // label L31 at .\sources\ConditionalBorrowChain.move:106:9+25
L31:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L32 at .\sources\ConditionalBorrowChain.move:106:9+25
L32:

    // $t99 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t99 := $IsParentMutation($t14, 0, $t15);

    // $t100 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t100 := $IsParentMutation($t13, 2, $t14);

    // $t101 := &&($t99, $t100) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t101 := $And($t99, $t100);

    // $t102 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t102 := $IsParentMutation($t12, 2, $t13);

    // $t103 := &&($t101, $t102) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t103 := $And($t101, $t102);

    // if ($t103) goto L33 else goto L34 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t103) { goto L33; } else { goto L34; }

    // label L33 at .\sources\ConditionalBorrowChain.move:106:9+25
L33:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L34 at .\sources\ConditionalBorrowChain.move:106:9+25
L34:

    // $t104 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t104 := $IsParentMutation($t14, 0, $t15);

    // $t105 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t105 := $IsParentMutation($t13, 2, $t14);

    // $t106 := &&($t104, $t105) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t106 := $And($t104, $t105);

    // $t107 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t107 := $IsParentMutation($t12, 3, $t13);

    // $t108 := &&($t106, $t107) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t108 := $And($t106, $t107);

    // if ($t108) goto L35 else goto L36 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t108) { goto L35; } else { goto L36; }

    // label L35 at .\sources\ConditionalBorrowChain.move:106:9+25
L35:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L36 at .\sources\ConditionalBorrowChain.move:106:9+25
L36:

    // $t109 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t109 := $IsParentMutation($t14, 0, $t15);

    // $t110 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t110 := $IsParentMutation($t13, 2, $t14);

    // $t111 := &&($t109, $t110) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t111 := $And($t109, $t110);

    // $t112 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t112 := $IsParentMutation($t12, 4, $t13);

    // $t113 := &&($t111, $t112) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t113 := $And($t111, $t112);

    // if ($t113) goto L37 else goto L38 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t113) { goto L37; } else { goto L38; }

    // label L37 at .\sources\ConditionalBorrowChain.move:106:9+25
L37:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L38 at .\sources\ConditionalBorrowChain.move:106:9+25
L38:

    // $t114 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t114 := $IsParentMutation($t14, 0, $t15);

    // $t115 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t115 := $IsParentMutation($t13, 2, $t14);

    // $t116 := &&($t114, $t115) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t116 := $And($t114, $t115);

    // $t117 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t117 := $IsParentMutation($t12, 5, $t13);

    // $t118 := &&($t116, $t117) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t118 := $And($t116, $t117);

    // if ($t118) goto L39 else goto L40 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t118) { goto L39; } else { goto L40; }

    // label L39 at .\sources\ConditionalBorrowChain.move:106:9+25
L39:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L40 at .\sources\ConditionalBorrowChain.move:106:9+25
L40:

    // $t119 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t119 := $IsParentMutation($t14, 0, $t15);

    // $t120 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t120 := $IsParentMutation($t13, 2, $t14);

    // $t121 := &&($t119, $t120) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t121 := $And($t119, $t120);

    // $t122 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t122 := $IsParentMutation($t12, 6, $t13);

    // $t123 := &&($t121, $t122) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t123 := $And($t121, $t122);

    // if ($t123) goto L41 else goto L42 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t123) { goto L41; } else { goto L42; }

    // label L41 at .\sources\ConditionalBorrowChain.move:106:9+25
L41:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L42 at .\sources\ConditionalBorrowChain.move:106:9+25
L42:

    // $t124 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t124 := $IsParentMutation($t14, 0, $t15);

    // $t125 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t125 := $IsParentMutation($t13, 3, $t14);

    // $t126 := &&($t124, $t125) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t126 := $And($t124, $t125);

    // $t127 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t127 := $IsParentMutation($t12, 0, $t13);

    // $t128 := &&($t126, $t127) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t128 := $And($t126, $t127);

    // if ($t128) goto L43 else goto L44 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t128) { goto L43; } else { goto L44; }

    // label L43 at .\sources\ConditionalBorrowChain.move:106:9+25
L43:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L44 at .\sources\ConditionalBorrowChain.move:106:9+25
L44:

    // $t129 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t129 := $IsParentMutation($t14, 0, $t15);

    // $t130 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t130 := $IsParentMutation($t13, 3, $t14);

    // $t131 := &&($t129, $t130) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t131 := $And($t129, $t130);

    // $t132 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t132 := $IsParentMutation($t12, 1, $t13);

    // $t133 := &&($t131, $t132) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t133 := $And($t131, $t132);

    // if ($t133) goto L45 else goto L46 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t133) { goto L45; } else { goto L46; }

    // label L45 at .\sources\ConditionalBorrowChain.move:106:9+25
L45:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L46 at .\sources\ConditionalBorrowChain.move:106:9+25
L46:

    // $t134 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t134 := $IsParentMutation($t14, 0, $t15);

    // $t135 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t135 := $IsParentMutation($t13, 3, $t14);

    // $t136 := &&($t134, $t135) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t136 := $And($t134, $t135);

    // $t137 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t137 := $IsParentMutation($t12, 2, $t13);

    // $t138 := &&($t136, $t137) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t138 := $And($t136, $t137);

    // if ($t138) goto L47 else goto L48 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t138) { goto L47; } else { goto L48; }

    // label L47 at .\sources\ConditionalBorrowChain.move:106:9+25
L47:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L48 at .\sources\ConditionalBorrowChain.move:106:9+25
L48:

    // $t139 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t139 := $IsParentMutation($t14, 0, $t15);

    // $t140 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t140 := $IsParentMutation($t13, 3, $t14);

    // $t141 := &&($t139, $t140) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t141 := $And($t139, $t140);

    // $t142 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t142 := $IsParentMutation($t12, 3, $t13);

    // $t143 := &&($t141, $t142) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t143 := $And($t141, $t142);

    // if ($t143) goto L49 else goto L50 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t143) { goto L49; } else { goto L50; }

    // label L49 at .\sources\ConditionalBorrowChain.move:106:9+25
L49:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L50 at .\sources\ConditionalBorrowChain.move:106:9+25
L50:

    // $t144 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t144 := $IsParentMutation($t14, 0, $t15);

    // $t145 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t145 := $IsParentMutation($t13, 3, $t14);

    // $t146 := &&($t144, $t145) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t146 := $And($t144, $t145);

    // $t147 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t147 := $IsParentMutation($t12, 4, $t13);

    // $t148 := &&($t146, $t147) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t148 := $And($t146, $t147);

    // if ($t148) goto L51 else goto L52 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t148) { goto L51; } else { goto L52; }

    // label L51 at .\sources\ConditionalBorrowChain.move:106:9+25
L51:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L52 at .\sources\ConditionalBorrowChain.move:106:9+25
L52:

    // $t149 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t149 := $IsParentMutation($t14, 0, $t15);

    // $t150 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t150 := $IsParentMutation($t13, 3, $t14);

    // $t151 := &&($t149, $t150) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t151 := $And($t149, $t150);

    // $t152 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t152 := $IsParentMutation($t12, 5, $t13);

    // $t153 := &&($t151, $t152) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t153 := $And($t151, $t152);

    // if ($t153) goto L53 else goto L54 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t153) { goto L53; } else { goto L54; }

    // label L53 at .\sources\ConditionalBorrowChain.move:106:9+25
L53:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L54 at .\sources\ConditionalBorrowChain.move:106:9+25
L54:

    // $t154 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t154 := $IsParentMutation($t14, 0, $t15);

    // $t155 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t155 := $IsParentMutation($t13, 3, $t14);

    // $t156 := &&($t154, $t155) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t156 := $And($t154, $t155);

    // $t157 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t157 := $IsParentMutation($t12, 6, $t13);

    // $t158 := &&($t156, $t157) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t158 := $And($t156, $t157);

    // if ($t158) goto L55 else goto L56 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t158) { goto L55; } else { goto L56; }

    // label L55 at .\sources\ConditionalBorrowChain.move:106:9+25
L55:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L56 at .\sources\ConditionalBorrowChain.move:106:9+25
L56:

    // $t159 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t159 := $IsParentMutation($t14, 0, $t15);

    // $t160 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t160 := $IsParentMutation($t13, 4, $t14);

    // $t161 := &&($t159, $t160) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t161 := $And($t159, $t160);

    // $t162 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t162 := $IsParentMutation($t12, 0, $t13);

    // $t163 := &&($t161, $t162) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t163 := $And($t161, $t162);

    // if ($t163) goto L57 else goto L58 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t163) { goto L57; } else { goto L58; }

    // label L57 at .\sources\ConditionalBorrowChain.move:106:9+25
L57:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L58 at .\sources\ConditionalBorrowChain.move:106:9+25
L58:

    // $t164 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t164 := $IsParentMutation($t14, 0, $t15);

    // $t165 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t165 := $IsParentMutation($t13, 4, $t14);

    // $t166 := &&($t164, $t165) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t166 := $And($t164, $t165);

    // $t167 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t167 := $IsParentMutation($t12, 1, $t13);

    // $t168 := &&($t166, $t167) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t168 := $And($t166, $t167);

    // if ($t168) goto L59 else goto L60 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t168) { goto L59; } else { goto L60; }

    // label L59 at .\sources\ConditionalBorrowChain.move:106:9+25
L59:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L60 at .\sources\ConditionalBorrowChain.move:106:9+25
L60:

    // $t169 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t169 := $IsParentMutation($t14, 0, $t15);

    // $t170 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t170 := $IsParentMutation($t13, 4, $t14);

    // $t171 := &&($t169, $t170) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t171 := $And($t169, $t170);

    // $t172 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t172 := $IsParentMutation($t12, 2, $t13);

    // $t173 := &&($t171, $t172) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t173 := $And($t171, $t172);

    // if ($t173) goto L61 else goto L62 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t173) { goto L61; } else { goto L62; }

    // label L61 at .\sources\ConditionalBorrowChain.move:106:9+25
L61:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L62 at .\sources\ConditionalBorrowChain.move:106:9+25
L62:

    // $t174 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t174 := $IsParentMutation($t14, 0, $t15);

    // $t175 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t175 := $IsParentMutation($t13, 4, $t14);

    // $t176 := &&($t174, $t175) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t176 := $And($t174, $t175);

    // $t177 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t177 := $IsParentMutation($t12, 3, $t13);

    // $t178 := &&($t176, $t177) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t178 := $And($t176, $t177);

    // if ($t178) goto L63 else goto L64 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t178) { goto L63; } else { goto L64; }

    // label L63 at .\sources\ConditionalBorrowChain.move:106:9+25
L63:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L64 at .\sources\ConditionalBorrowChain.move:106:9+25
L64:

    // $t179 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t179 := $IsParentMutation($t14, 0, $t15);

    // $t180 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t180 := $IsParentMutation($t13, 4, $t14);

    // $t181 := &&($t179, $t180) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t181 := $And($t179, $t180);

    // $t182 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t182 := $IsParentMutation($t12, 4, $t13);

    // $t183 := &&($t181, $t182) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t183 := $And($t181, $t182);

    // if ($t183) goto L65 else goto L66 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t183) { goto L65; } else { goto L66; }

    // label L65 at .\sources\ConditionalBorrowChain.move:106:9+25
L65:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L66 at .\sources\ConditionalBorrowChain.move:106:9+25
L66:

    // $t184 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t184 := $IsParentMutation($t14, 0, $t15);

    // $t185 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t185 := $IsParentMutation($t13, 4, $t14);

    // $t186 := &&($t184, $t185) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t186 := $And($t184, $t185);

    // $t187 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t187 := $IsParentMutation($t12, 5, $t13);

    // $t188 := &&($t186, $t187) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t188 := $And($t186, $t187);

    // if ($t188) goto L67 else goto L68 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t188) { goto L67; } else { goto L68; }

    // label L67 at .\sources\ConditionalBorrowChain.move:106:9+25
L67:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L68 at .\sources\ConditionalBorrowChain.move:106:9+25
L68:

    // $t189 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t189 := $IsParentMutation($t14, 0, $t15);

    // $t190 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t190 := $IsParentMutation($t13, 4, $t14);

    // $t191 := &&($t189, $t190) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t191 := $And($t189, $t190);

    // $t192 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t192 := $IsParentMutation($t12, 6, $t13);

    // $t193 := &&($t191, $t192) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t193 := $And($t191, $t192);

    // if ($t193) goto L69 else goto L70 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t193) { goto L69; } else { goto L70; }

    // label L69 at .\sources\ConditionalBorrowChain.move:106:9+25
L69:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L70 at .\sources\ConditionalBorrowChain.move:106:9+25
L70:

    // $t194 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t194 := $IsParentMutation($t14, 0, $t15);

    // $t195 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t195 := $IsParentMutation($t13, 5, $t14);

    // $t196 := &&($t194, $t195) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t196 := $And($t194, $t195);

    // $t197 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t197 := $IsParentMutation($t12, 0, $t13);

    // $t198 := &&($t196, $t197) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t198 := $And($t196, $t197);

    // if ($t198) goto L71 else goto L72 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t198) { goto L71; } else { goto L72; }

    // label L71 at .\sources\ConditionalBorrowChain.move:106:9+25
L71:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L72 at .\sources\ConditionalBorrowChain.move:106:9+25
L72:

    // $t199 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t199 := $IsParentMutation($t14, 0, $t15);

    // $t200 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t200 := $IsParentMutation($t13, 5, $t14);

    // $t201 := &&($t199, $t200) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t201 := $And($t199, $t200);

    // $t202 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t202 := $IsParentMutation($t12, 1, $t13);

    // $t203 := &&($t201, $t202) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t203 := $And($t201, $t202);

    // if ($t203) goto L73 else goto L74 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t203) { goto L73; } else { goto L74; }

    // label L73 at .\sources\ConditionalBorrowChain.move:106:9+25
L73:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L74 at .\sources\ConditionalBorrowChain.move:106:9+25
L74:

    // $t204 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t204 := $IsParentMutation($t14, 0, $t15);

    // $t205 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t205 := $IsParentMutation($t13, 5, $t14);

    // $t206 := &&($t204, $t205) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t206 := $And($t204, $t205);

    // $t207 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t207 := $IsParentMutation($t12, 2, $t13);

    // $t208 := &&($t206, $t207) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t208 := $And($t206, $t207);

    // if ($t208) goto L75 else goto L76 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t208) { goto L75; } else { goto L76; }

    // label L75 at .\sources\ConditionalBorrowChain.move:106:9+25
L75:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L76 at .\sources\ConditionalBorrowChain.move:106:9+25
L76:

    // $t209 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t209 := $IsParentMutation($t14, 0, $t15);

    // $t210 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t210 := $IsParentMutation($t13, 5, $t14);

    // $t211 := &&($t209, $t210) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t211 := $And($t209, $t210);

    // $t212 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t212 := $IsParentMutation($t12, 3, $t13);

    // $t213 := &&($t211, $t212) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t213 := $And($t211, $t212);

    // if ($t213) goto L77 else goto L78 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t213) { goto L77; } else { goto L78; }

    // label L77 at .\sources\ConditionalBorrowChain.move:106:9+25
L77:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L78 at .\sources\ConditionalBorrowChain.move:106:9+25
L78:

    // $t214 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t214 := $IsParentMutation($t14, 0, $t15);

    // $t215 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t215 := $IsParentMutation($t13, 5, $t14);

    // $t216 := &&($t214, $t215) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t216 := $And($t214, $t215);

    // $t217 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t217 := $IsParentMutation($t12, 4, $t13);

    // $t218 := &&($t216, $t217) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t218 := $And($t216, $t217);

    // if ($t218) goto L79 else goto L80 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t218) { goto L79; } else { goto L80; }

    // label L79 at .\sources\ConditionalBorrowChain.move:106:9+25
L79:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L80 at .\sources\ConditionalBorrowChain.move:106:9+25
L80:

    // $t219 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t219 := $IsParentMutation($t14, 0, $t15);

    // $t220 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t220 := $IsParentMutation($t13, 5, $t14);

    // $t221 := &&($t219, $t220) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t221 := $And($t219, $t220);

    // $t222 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t222 := $IsParentMutation($t12, 5, $t13);

    // $t223 := &&($t221, $t222) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t223 := $And($t221, $t222);

    // if ($t223) goto L81 else goto L82 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t223) { goto L81; } else { goto L82; }

    // label L81 at .\sources\ConditionalBorrowChain.move:106:9+25
L81:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L82 at .\sources\ConditionalBorrowChain.move:106:9+25
L82:

    // $t224 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t224 := $IsParentMutation($t14, 0, $t15);

    // $t225 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t225 := $IsParentMutation($t13, 5, $t14);

    // $t226 := &&($t224, $t225) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t226 := $And($t224, $t225);

    // $t227 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t227 := $IsParentMutation($t12, 6, $t13);

    // $t228 := &&($t226, $t227) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t228 := $And($t226, $t227);

    // if ($t228) goto L83 else goto L84 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t228) { goto L83; } else { goto L84; }

    // label L83 at .\sources\ConditionalBorrowChain.move:106:9+25
L83:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L84 at .\sources\ConditionalBorrowChain.move:106:9+25
L84:

    // $t229 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t229 := $IsParentMutation($t14, 0, $t15);

    // $t230 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t230 := $IsParentMutation($t13, 6, $t14);

    // $t231 := &&($t229, $t230) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t231 := $And($t229, $t230);

    // $t232 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t232 := $IsParentMutation($t12, 0, $t13);

    // $t233 := &&($t231, $t232) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t233 := $And($t231, $t232);

    // if ($t233) goto L85 else goto L86 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t233) { goto L85; } else { goto L86; }

    // label L85 at .\sources\ConditionalBorrowChain.move:106:9+25
L85:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L86 at .\sources\ConditionalBorrowChain.move:106:9+25
L86:

    // $t234 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t234 := $IsParentMutation($t14, 0, $t15);

    // $t235 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t235 := $IsParentMutation($t13, 6, $t14);

    // $t236 := &&($t234, $t235) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t236 := $And($t234, $t235);

    // $t237 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t237 := $IsParentMutation($t12, 1, $t13);

    // $t238 := &&($t236, $t237) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t238 := $And($t236, $t237);

    // if ($t238) goto L87 else goto L88 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t238) { goto L87; } else { goto L88; }

    // label L87 at .\sources\ConditionalBorrowChain.move:106:9+25
L87:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L88 at .\sources\ConditionalBorrowChain.move:106:9+25
L88:

    // $t239 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t239 := $IsParentMutation($t14, 0, $t15);

    // $t240 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t240 := $IsParentMutation($t13, 6, $t14);

    // $t241 := &&($t239, $t240) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t241 := $And($t239, $t240);

    // $t242 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t242 := $IsParentMutation($t12, 2, $t13);

    // $t243 := &&($t241, $t242) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t243 := $And($t241, $t242);

    // if ($t243) goto L89 else goto L90 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t243) { goto L89; } else { goto L90; }

    // label L89 at .\sources\ConditionalBorrowChain.move:106:9+25
L89:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L90 at .\sources\ConditionalBorrowChain.move:106:9+25
L90:

    // $t244 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t244 := $IsParentMutation($t14, 0, $t15);

    // $t245 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t245 := $IsParentMutation($t13, 6, $t14);

    // $t246 := &&($t244, $t245) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t246 := $And($t244, $t245);

    // $t247 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t247 := $IsParentMutation($t12, 3, $t13);

    // $t248 := &&($t246, $t247) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t248 := $And($t246, $t247);

    // if ($t248) goto L91 else goto L92 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t248) { goto L91; } else { goto L92; }

    // label L91 at .\sources\ConditionalBorrowChain.move:106:9+25
L91:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L92 at .\sources\ConditionalBorrowChain.move:106:9+25
L92:

    // $t249 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t249 := $IsParentMutation($t14, 0, $t15);

    // $t250 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t250 := $IsParentMutation($t13, 6, $t14);

    // $t251 := &&($t249, $t250) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t251 := $And($t249, $t250);

    // $t252 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t252 := $IsParentMutation($t12, 4, $t13);

    // $t253 := &&($t251, $t252) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t253 := $And($t251, $t252);

    // if ($t253) goto L93 else goto L94 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t253) { goto L93; } else { goto L94; }

    // label L93 at .\sources\ConditionalBorrowChain.move:106:9+25
L93:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L94 at .\sources\ConditionalBorrowChain.move:106:9+25
L94:

    // $t254 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t254 := $IsParentMutation($t14, 0, $t15);

    // $t255 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t255 := $IsParentMutation($t13, 6, $t14);

    // $t256 := &&($t254, $t255) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t256 := $And($t254, $t255);

    // $t257 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t257 := $IsParentMutation($t12, 5, $t13);

    // $t258 := &&($t256, $t257) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t258 := $And($t256, $t257);

    // if ($t258) goto L95 else goto L96 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t258) { goto L95; } else { goto L96; }

    // label L95 at .\sources\ConditionalBorrowChain.move:106:9+25
L95:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L96 at .\sources\ConditionalBorrowChain.move:106:9+25
L96:

    // $t259 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t259 := $IsParentMutation($t14, 0, $t15);

    // $t260 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t260 := $IsParentMutation($t13, 6, $t14);

    // $t261 := &&($t259, $t260) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t261 := $And($t259, $t260);

    // $t262 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t262 := $IsParentMutation($t12, 6, $t13);

    // $t263 := &&($t261, $t262) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t263 := $And($t261, $t262);

    // if ($t263) goto L97 else goto L98 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t263) { goto L97; } else { goto L98; }

    // label L97 at .\sources\ConditionalBorrowChain.move:106:9+25
L97:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L98 at .\sources\ConditionalBorrowChain.move:106:9+25
L98:

    // $t264 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t264 := $IsParentMutation($t14, 1, $t15);

    // $t265 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t265 := $IsParentMutation($t13, 0, $t14);

    // $t266 := &&($t264, $t265) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t266 := $And($t264, $t265);

    // $t267 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t267 := $IsParentMutation($t12, 0, $t13);

    // $t268 := &&($t266, $t267) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t268 := $And($t266, $t267);

    // if ($t268) goto L99 else goto L100 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t268) { goto L99; } else { goto L100; }

    // label L99 at .\sources\ConditionalBorrowChain.move:106:9+25
L99:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L100 at .\sources\ConditionalBorrowChain.move:106:9+25
L100:

    // $t269 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t269 := $IsParentMutation($t14, 1, $t15);

    // $t270 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t270 := $IsParentMutation($t13, 0, $t14);

    // $t271 := &&($t269, $t270) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t271 := $And($t269, $t270);

    // $t272 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t272 := $IsParentMutation($t12, 1, $t13);

    // $t273 := &&($t271, $t272) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t273 := $And($t271, $t272);

    // if ($t273) goto L101 else goto L102 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t273) { goto L101; } else { goto L102; }

    // label L101 at .\sources\ConditionalBorrowChain.move:106:9+25
L101:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L102 at .\sources\ConditionalBorrowChain.move:106:9+25
L102:

    // $t274 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t274 := $IsParentMutation($t14, 1, $t15);

    // $t275 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t275 := $IsParentMutation($t13, 0, $t14);

    // $t276 := &&($t274, $t275) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t276 := $And($t274, $t275);

    // $t277 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t277 := $IsParentMutation($t12, 2, $t13);

    // $t278 := &&($t276, $t277) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t278 := $And($t276, $t277);

    // if ($t278) goto L103 else goto L104 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t278) { goto L103; } else { goto L104; }

    // label L103 at .\sources\ConditionalBorrowChain.move:106:9+25
L103:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L104 at .\sources\ConditionalBorrowChain.move:106:9+25
L104:

    // $t279 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t279 := $IsParentMutation($t14, 1, $t15);

    // $t280 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t280 := $IsParentMutation($t13, 0, $t14);

    // $t281 := &&($t279, $t280) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t281 := $And($t279, $t280);

    // $t282 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t282 := $IsParentMutation($t12, 3, $t13);

    // $t283 := &&($t281, $t282) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t283 := $And($t281, $t282);

    // if ($t283) goto L105 else goto L106 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t283) { goto L105; } else { goto L106; }

    // label L105 at .\sources\ConditionalBorrowChain.move:106:9+25
L105:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L106 at .\sources\ConditionalBorrowChain.move:106:9+25
L106:

    // $t284 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t284 := $IsParentMutation($t14, 1, $t15);

    // $t285 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t285 := $IsParentMutation($t13, 0, $t14);

    // $t286 := &&($t284, $t285) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t286 := $And($t284, $t285);

    // $t287 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t287 := $IsParentMutation($t12, 4, $t13);

    // $t288 := &&($t286, $t287) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t288 := $And($t286, $t287);

    // if ($t288) goto L107 else goto L108 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t288) { goto L107; } else { goto L108; }

    // label L107 at .\sources\ConditionalBorrowChain.move:106:9+25
L107:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L108 at .\sources\ConditionalBorrowChain.move:106:9+25
L108:

    // $t289 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t289 := $IsParentMutation($t14, 1, $t15);

    // $t290 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t290 := $IsParentMutation($t13, 0, $t14);

    // $t291 := &&($t289, $t290) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t291 := $And($t289, $t290);

    // $t292 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t292 := $IsParentMutation($t12, 5, $t13);

    // $t293 := &&($t291, $t292) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t293 := $And($t291, $t292);

    // if ($t293) goto L109 else goto L110 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t293) { goto L109; } else { goto L110; }

    // label L109 at .\sources\ConditionalBorrowChain.move:106:9+25
L109:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L110 at .\sources\ConditionalBorrowChain.move:106:9+25
L110:

    // $t294 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t294 := $IsParentMutation($t14, 1, $t15);

    // $t295 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t295 := $IsParentMutation($t13, 0, $t14);

    // $t296 := &&($t294, $t295) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t296 := $And($t294, $t295);

    // $t297 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t297 := $IsParentMutation($t12, 6, $t13);

    // $t298 := &&($t296, $t297) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t298 := $And($t296, $t297);

    // if ($t298) goto L111 else goto L112 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t298) { goto L111; } else { goto L112; }

    // label L111 at .\sources\ConditionalBorrowChain.move:106:9+25
L111:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L112 at .\sources\ConditionalBorrowChain.move:106:9+25
L112:

    // $t299 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t299 := $IsParentMutation($t14, 1, $t15);

    // $t300 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t300 := $IsParentMutation($t13, 1, $t14);

    // $t301 := &&($t299, $t300) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t301 := $And($t299, $t300);

    // $t302 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t302 := $IsParentMutation($t12, 0, $t13);

    // $t303 := &&($t301, $t302) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t303 := $And($t301, $t302);

    // if ($t303) goto L113 else goto L114 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t303) { goto L113; } else { goto L114; }

    // label L113 at .\sources\ConditionalBorrowChain.move:106:9+25
L113:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L114 at .\sources\ConditionalBorrowChain.move:106:9+25
L114:

    // $t304 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t304 := $IsParentMutation($t14, 1, $t15);

    // $t305 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t305 := $IsParentMutation($t13, 1, $t14);

    // $t306 := &&($t304, $t305) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t306 := $And($t304, $t305);

    // $t307 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t307 := $IsParentMutation($t12, 1, $t13);

    // $t308 := &&($t306, $t307) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t308 := $And($t306, $t307);

    // if ($t308) goto L115 else goto L116 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t308) { goto L115; } else { goto L116; }

    // label L115 at .\sources\ConditionalBorrowChain.move:106:9+25
L115:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L116 at .\sources\ConditionalBorrowChain.move:106:9+25
L116:

    // $t309 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t309 := $IsParentMutation($t14, 1, $t15);

    // $t310 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t310 := $IsParentMutation($t13, 1, $t14);

    // $t311 := &&($t309, $t310) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t311 := $And($t309, $t310);

    // $t312 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t312 := $IsParentMutation($t12, 2, $t13);

    // $t313 := &&($t311, $t312) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t313 := $And($t311, $t312);

    // if ($t313) goto L117 else goto L118 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t313) { goto L117; } else { goto L118; }

    // label L117 at .\sources\ConditionalBorrowChain.move:106:9+25
L117:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L118 at .\sources\ConditionalBorrowChain.move:106:9+25
L118:

    // $t314 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t314 := $IsParentMutation($t14, 1, $t15);

    // $t315 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t315 := $IsParentMutation($t13, 1, $t14);

    // $t316 := &&($t314, $t315) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t316 := $And($t314, $t315);

    // $t317 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t317 := $IsParentMutation($t12, 3, $t13);

    // $t318 := &&($t316, $t317) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t318 := $And($t316, $t317);

    // if ($t318) goto L119 else goto L120 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t318) { goto L119; } else { goto L120; }

    // label L119 at .\sources\ConditionalBorrowChain.move:106:9+25
L119:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L120 at .\sources\ConditionalBorrowChain.move:106:9+25
L120:

    // $t319 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t319 := $IsParentMutation($t14, 1, $t15);

    // $t320 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t320 := $IsParentMutation($t13, 1, $t14);

    // $t321 := &&($t319, $t320) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t321 := $And($t319, $t320);

    // $t322 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t322 := $IsParentMutation($t12, 4, $t13);

    // $t323 := &&($t321, $t322) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t323 := $And($t321, $t322);

    // if ($t323) goto L121 else goto L122 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t323) { goto L121; } else { goto L122; }

    // label L121 at .\sources\ConditionalBorrowChain.move:106:9+25
L121:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L122 at .\sources\ConditionalBorrowChain.move:106:9+25
L122:

    // $t324 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t324 := $IsParentMutation($t14, 1, $t15);

    // $t325 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t325 := $IsParentMutation($t13, 1, $t14);

    // $t326 := &&($t324, $t325) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t326 := $And($t324, $t325);

    // $t327 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t327 := $IsParentMutation($t12, 5, $t13);

    // $t328 := &&($t326, $t327) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t328 := $And($t326, $t327);

    // if ($t328) goto L123 else goto L124 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t328) { goto L123; } else { goto L124; }

    // label L123 at .\sources\ConditionalBorrowChain.move:106:9+25
L123:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L124 at .\sources\ConditionalBorrowChain.move:106:9+25
L124:

    // $t329 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t329 := $IsParentMutation($t14, 1, $t15);

    // $t330 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t330 := $IsParentMutation($t13, 1, $t14);

    // $t331 := &&($t329, $t330) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t331 := $And($t329, $t330);

    // $t332 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t332 := $IsParentMutation($t12, 6, $t13);

    // $t333 := &&($t331, $t332) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t333 := $And($t331, $t332);

    // if ($t333) goto L125 else goto L126 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t333) { goto L125; } else { goto L126; }

    // label L125 at .\sources\ConditionalBorrowChain.move:106:9+25
L125:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L126 at .\sources\ConditionalBorrowChain.move:106:9+25
L126:

    // $t334 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t334 := $IsParentMutation($t14, 1, $t15);

    // $t335 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t335 := $IsParentMutation($t13, 2, $t14);

    // $t336 := &&($t334, $t335) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t336 := $And($t334, $t335);

    // $t337 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t337 := $IsParentMutation($t12, 0, $t13);

    // $t338 := &&($t336, $t337) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t338 := $And($t336, $t337);

    // if ($t338) goto L127 else goto L128 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t338) { goto L127; } else { goto L128; }

    // label L127 at .\sources\ConditionalBorrowChain.move:106:9+25
L127:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L128 at .\sources\ConditionalBorrowChain.move:106:9+25
L128:

    // $t339 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t339 := $IsParentMutation($t14, 1, $t15);

    // $t340 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t340 := $IsParentMutation($t13, 2, $t14);

    // $t341 := &&($t339, $t340) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t341 := $And($t339, $t340);

    // $t342 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t342 := $IsParentMutation($t12, 1, $t13);

    // $t343 := &&($t341, $t342) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t343 := $And($t341, $t342);

    // if ($t343) goto L129 else goto L130 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t343) { goto L129; } else { goto L130; }

    // label L129 at .\sources\ConditionalBorrowChain.move:106:9+25
L129:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L130 at .\sources\ConditionalBorrowChain.move:106:9+25
L130:

    // $t344 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t344 := $IsParentMutation($t14, 1, $t15);

    // $t345 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t345 := $IsParentMutation($t13, 2, $t14);

    // $t346 := &&($t344, $t345) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t346 := $And($t344, $t345);

    // $t347 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t347 := $IsParentMutation($t12, 2, $t13);

    // $t348 := &&($t346, $t347) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t348 := $And($t346, $t347);

    // if ($t348) goto L131 else goto L132 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t348) { goto L131; } else { goto L132; }

    // label L131 at .\sources\ConditionalBorrowChain.move:106:9+25
L131:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L132 at .\sources\ConditionalBorrowChain.move:106:9+25
L132:

    // $t349 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t349 := $IsParentMutation($t14, 1, $t15);

    // $t350 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t350 := $IsParentMutation($t13, 2, $t14);

    // $t351 := &&($t349, $t350) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t351 := $And($t349, $t350);

    // $t352 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t352 := $IsParentMutation($t12, 3, $t13);

    // $t353 := &&($t351, $t352) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t353 := $And($t351, $t352);

    // if ($t353) goto L133 else goto L134 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t353) { goto L133; } else { goto L134; }

    // label L133 at .\sources\ConditionalBorrowChain.move:106:9+25
L133:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L134 at .\sources\ConditionalBorrowChain.move:106:9+25
L134:

    // $t354 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t354 := $IsParentMutation($t14, 1, $t15);

    // $t355 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t355 := $IsParentMutation($t13, 2, $t14);

    // $t356 := &&($t354, $t355) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t356 := $And($t354, $t355);

    // $t357 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t357 := $IsParentMutation($t12, 4, $t13);

    // $t358 := &&($t356, $t357) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t358 := $And($t356, $t357);

    // if ($t358) goto L135 else goto L136 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t358) { goto L135; } else { goto L136; }

    // label L135 at .\sources\ConditionalBorrowChain.move:106:9+25
L135:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L136 at .\sources\ConditionalBorrowChain.move:106:9+25
L136:

    // $t359 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t359 := $IsParentMutation($t14, 1, $t15);

    // $t360 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t360 := $IsParentMutation($t13, 2, $t14);

    // $t361 := &&($t359, $t360) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t361 := $And($t359, $t360);

    // $t362 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t362 := $IsParentMutation($t12, 5, $t13);

    // $t363 := &&($t361, $t362) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t363 := $And($t361, $t362);

    // if ($t363) goto L137 else goto L138 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t363) { goto L137; } else { goto L138; }

    // label L137 at .\sources\ConditionalBorrowChain.move:106:9+25
L137:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L138 at .\sources\ConditionalBorrowChain.move:106:9+25
L138:

    // $t364 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t364 := $IsParentMutation($t14, 1, $t15);

    // $t365 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t365 := $IsParentMutation($t13, 2, $t14);

    // $t366 := &&($t364, $t365) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t366 := $And($t364, $t365);

    // $t367 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t367 := $IsParentMutation($t12, 6, $t13);

    // $t368 := &&($t366, $t367) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t368 := $And($t366, $t367);

    // if ($t368) goto L139 else goto L140 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t368) { goto L139; } else { goto L140; }

    // label L139 at .\sources\ConditionalBorrowChain.move:106:9+25
L139:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L140 at .\sources\ConditionalBorrowChain.move:106:9+25
L140:

    // $t369 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t369 := $IsParentMutation($t14, 1, $t15);

    // $t370 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t370 := $IsParentMutation($t13, 3, $t14);

    // $t371 := &&($t369, $t370) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t371 := $And($t369, $t370);

    // $t372 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t372 := $IsParentMutation($t12, 0, $t13);

    // $t373 := &&($t371, $t372) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t373 := $And($t371, $t372);

    // if ($t373) goto L141 else goto L142 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t373) { goto L141; } else { goto L142; }

    // label L141 at .\sources\ConditionalBorrowChain.move:106:9+25
L141:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L142 at .\sources\ConditionalBorrowChain.move:106:9+25
L142:

    // $t374 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t374 := $IsParentMutation($t14, 1, $t15);

    // $t375 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t375 := $IsParentMutation($t13, 3, $t14);

    // $t376 := &&($t374, $t375) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t376 := $And($t374, $t375);

    // $t377 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t377 := $IsParentMutation($t12, 1, $t13);

    // $t378 := &&($t376, $t377) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t378 := $And($t376, $t377);

    // if ($t378) goto L143 else goto L144 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t378) { goto L143; } else { goto L144; }

    // label L143 at .\sources\ConditionalBorrowChain.move:106:9+25
L143:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L144 at .\sources\ConditionalBorrowChain.move:106:9+25
L144:

    // $t379 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t379 := $IsParentMutation($t14, 1, $t15);

    // $t380 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t380 := $IsParentMutation($t13, 3, $t14);

    // $t381 := &&($t379, $t380) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t381 := $And($t379, $t380);

    // $t382 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t382 := $IsParentMutation($t12, 2, $t13);

    // $t383 := &&($t381, $t382) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t383 := $And($t381, $t382);

    // if ($t383) goto L145 else goto L146 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t383) { goto L145; } else { goto L146; }

    // label L145 at .\sources\ConditionalBorrowChain.move:106:9+25
L145:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L146 at .\sources\ConditionalBorrowChain.move:106:9+25
L146:

    // $t384 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t384 := $IsParentMutation($t14, 1, $t15);

    // $t385 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t385 := $IsParentMutation($t13, 3, $t14);

    // $t386 := &&($t384, $t385) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t386 := $And($t384, $t385);

    // $t387 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t387 := $IsParentMutation($t12, 3, $t13);

    // $t388 := &&($t386, $t387) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t388 := $And($t386, $t387);

    // if ($t388) goto L147 else goto L148 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t388) { goto L147; } else { goto L148; }

    // label L147 at .\sources\ConditionalBorrowChain.move:106:9+25
L147:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L148 at .\sources\ConditionalBorrowChain.move:106:9+25
L148:

    // $t389 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t389 := $IsParentMutation($t14, 1, $t15);

    // $t390 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t390 := $IsParentMutation($t13, 3, $t14);

    // $t391 := &&($t389, $t390) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t391 := $And($t389, $t390);

    // $t392 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t392 := $IsParentMutation($t12, 4, $t13);

    // $t393 := &&($t391, $t392) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t393 := $And($t391, $t392);

    // if ($t393) goto L149 else goto L150 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t393) { goto L149; } else { goto L150; }

    // label L149 at .\sources\ConditionalBorrowChain.move:106:9+25
L149:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L150 at .\sources\ConditionalBorrowChain.move:106:9+25
L150:

    // $t394 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t394 := $IsParentMutation($t14, 1, $t15);

    // $t395 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t395 := $IsParentMutation($t13, 3, $t14);

    // $t396 := &&($t394, $t395) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t396 := $And($t394, $t395);

    // $t397 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t397 := $IsParentMutation($t12, 5, $t13);

    // $t398 := &&($t396, $t397) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t398 := $And($t396, $t397);

    // if ($t398) goto L151 else goto L152 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t398) { goto L151; } else { goto L152; }

    // label L151 at .\sources\ConditionalBorrowChain.move:106:9+25
L151:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L152 at .\sources\ConditionalBorrowChain.move:106:9+25
L152:

    // $t399 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t399 := $IsParentMutation($t14, 1, $t15);

    // $t400 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t400 := $IsParentMutation($t13, 3, $t14);

    // $t401 := &&($t399, $t400) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t401 := $And($t399, $t400);

    // $t402 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t402 := $IsParentMutation($t12, 6, $t13);

    // $t403 := &&($t401, $t402) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t403 := $And($t401, $t402);

    // if ($t403) goto L153 else goto L154 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t403) { goto L153; } else { goto L154; }

    // label L153 at .\sources\ConditionalBorrowChain.move:106:9+25
L153:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L154 at .\sources\ConditionalBorrowChain.move:106:9+25
L154:

    // $t404 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t404 := $IsParentMutation($t14, 1, $t15);

    // $t405 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t405 := $IsParentMutation($t13, 4, $t14);

    // $t406 := &&($t404, $t405) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t406 := $And($t404, $t405);

    // $t407 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t407 := $IsParentMutation($t12, 0, $t13);

    // $t408 := &&($t406, $t407) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t408 := $And($t406, $t407);

    // if ($t408) goto L155 else goto L156 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t408) { goto L155; } else { goto L156; }

    // label L155 at .\sources\ConditionalBorrowChain.move:106:9+25
L155:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L156 at .\sources\ConditionalBorrowChain.move:106:9+25
L156:

    // $t409 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t409 := $IsParentMutation($t14, 1, $t15);

    // $t410 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t410 := $IsParentMutation($t13, 4, $t14);

    // $t411 := &&($t409, $t410) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t411 := $And($t409, $t410);

    // $t412 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t412 := $IsParentMutation($t12, 1, $t13);

    // $t413 := &&($t411, $t412) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t413 := $And($t411, $t412);

    // if ($t413) goto L157 else goto L158 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t413) { goto L157; } else { goto L158; }

    // label L157 at .\sources\ConditionalBorrowChain.move:106:9+25
L157:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L158 at .\sources\ConditionalBorrowChain.move:106:9+25
L158:

    // $t414 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t414 := $IsParentMutation($t14, 1, $t15);

    // $t415 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t415 := $IsParentMutation($t13, 4, $t14);

    // $t416 := &&($t414, $t415) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t416 := $And($t414, $t415);

    // $t417 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t417 := $IsParentMutation($t12, 2, $t13);

    // $t418 := &&($t416, $t417) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t418 := $And($t416, $t417);

    // if ($t418) goto L159 else goto L160 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t418) { goto L159; } else { goto L160; }

    // label L159 at .\sources\ConditionalBorrowChain.move:106:9+25
L159:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L160 at .\sources\ConditionalBorrowChain.move:106:9+25
L160:

    // $t419 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t419 := $IsParentMutation($t14, 1, $t15);

    // $t420 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t420 := $IsParentMutation($t13, 4, $t14);

    // $t421 := &&($t419, $t420) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t421 := $And($t419, $t420);

    // $t422 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t422 := $IsParentMutation($t12, 3, $t13);

    // $t423 := &&($t421, $t422) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t423 := $And($t421, $t422);

    // if ($t423) goto L161 else goto L162 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t423) { goto L161; } else { goto L162; }

    // label L161 at .\sources\ConditionalBorrowChain.move:106:9+25
L161:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L162 at .\sources\ConditionalBorrowChain.move:106:9+25
L162:

    // $t424 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t424 := $IsParentMutation($t14, 1, $t15);

    // $t425 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t425 := $IsParentMutation($t13, 4, $t14);

    // $t426 := &&($t424, $t425) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t426 := $And($t424, $t425);

    // $t427 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t427 := $IsParentMutation($t12, 4, $t13);

    // $t428 := &&($t426, $t427) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t428 := $And($t426, $t427);

    // if ($t428) goto L163 else goto L164 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t428) { goto L163; } else { goto L164; }

    // label L163 at .\sources\ConditionalBorrowChain.move:106:9+25
L163:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L164 at .\sources\ConditionalBorrowChain.move:106:9+25
L164:

    // $t429 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t429 := $IsParentMutation($t14, 1, $t15);

    // $t430 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t430 := $IsParentMutation($t13, 4, $t14);

    // $t431 := &&($t429, $t430) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t431 := $And($t429, $t430);

    // $t432 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t432 := $IsParentMutation($t12, 5, $t13);

    // $t433 := &&($t431, $t432) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t433 := $And($t431, $t432);

    // if ($t433) goto L165 else goto L166 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t433) { goto L165; } else { goto L166; }

    // label L165 at .\sources\ConditionalBorrowChain.move:106:9+25
L165:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L166 at .\sources\ConditionalBorrowChain.move:106:9+25
L166:

    // $t434 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t434 := $IsParentMutation($t14, 1, $t15);

    // $t435 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t435 := $IsParentMutation($t13, 4, $t14);

    // $t436 := &&($t434, $t435) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t436 := $And($t434, $t435);

    // $t437 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t437 := $IsParentMutation($t12, 6, $t13);

    // $t438 := &&($t436, $t437) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t438 := $And($t436, $t437);

    // if ($t438) goto L167 else goto L168 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t438) { goto L167; } else { goto L168; }

    // label L167 at .\sources\ConditionalBorrowChain.move:106:9+25
L167:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L168 at .\sources\ConditionalBorrowChain.move:106:9+25
L168:

    // $t439 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t439 := $IsParentMutation($t14, 1, $t15);

    // $t440 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t440 := $IsParentMutation($t13, 5, $t14);

    // $t441 := &&($t439, $t440) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t441 := $And($t439, $t440);

    // $t442 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t442 := $IsParentMutation($t12, 0, $t13);

    // $t443 := &&($t441, $t442) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t443 := $And($t441, $t442);

    // if ($t443) goto L169 else goto L170 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t443) { goto L169; } else { goto L170; }

    // label L169 at .\sources\ConditionalBorrowChain.move:106:9+25
L169:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L170 at .\sources\ConditionalBorrowChain.move:106:9+25
L170:

    // $t444 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t444 := $IsParentMutation($t14, 1, $t15);

    // $t445 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t445 := $IsParentMutation($t13, 5, $t14);

    // $t446 := &&($t444, $t445) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t446 := $And($t444, $t445);

    // $t447 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t447 := $IsParentMutation($t12, 1, $t13);

    // $t448 := &&($t446, $t447) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t448 := $And($t446, $t447);

    // if ($t448) goto L171 else goto L172 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t448) { goto L171; } else { goto L172; }

    // label L171 at .\sources\ConditionalBorrowChain.move:106:9+25
L171:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L172 at .\sources\ConditionalBorrowChain.move:106:9+25
L172:

    // $t449 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t449 := $IsParentMutation($t14, 1, $t15);

    // $t450 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t450 := $IsParentMutation($t13, 5, $t14);

    // $t451 := &&($t449, $t450) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t451 := $And($t449, $t450);

    // $t452 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t452 := $IsParentMutation($t12, 2, $t13);

    // $t453 := &&($t451, $t452) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t453 := $And($t451, $t452);

    // if ($t453) goto L173 else goto L174 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t453) { goto L173; } else { goto L174; }

    // label L173 at .\sources\ConditionalBorrowChain.move:106:9+25
L173:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L174 at .\sources\ConditionalBorrowChain.move:106:9+25
L174:

    // $t454 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t454 := $IsParentMutation($t14, 1, $t15);

    // $t455 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t455 := $IsParentMutation($t13, 5, $t14);

    // $t456 := &&($t454, $t455) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t456 := $And($t454, $t455);

    // $t457 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t457 := $IsParentMutation($t12, 3, $t13);

    // $t458 := &&($t456, $t457) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t458 := $And($t456, $t457);

    // if ($t458) goto L175 else goto L176 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t458) { goto L175; } else { goto L176; }

    // label L175 at .\sources\ConditionalBorrowChain.move:106:9+25
L175:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L176 at .\sources\ConditionalBorrowChain.move:106:9+25
L176:

    // $t459 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t459 := $IsParentMutation($t14, 1, $t15);

    // $t460 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t460 := $IsParentMutation($t13, 5, $t14);

    // $t461 := &&($t459, $t460) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t461 := $And($t459, $t460);

    // $t462 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t462 := $IsParentMutation($t12, 4, $t13);

    // $t463 := &&($t461, $t462) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t463 := $And($t461, $t462);

    // if ($t463) goto L177 else goto L178 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t463) { goto L177; } else { goto L178; }

    // label L177 at .\sources\ConditionalBorrowChain.move:106:9+25
L177:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L178 at .\sources\ConditionalBorrowChain.move:106:9+25
L178:

    // $t464 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t464 := $IsParentMutation($t14, 1, $t15);

    // $t465 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t465 := $IsParentMutation($t13, 5, $t14);

    // $t466 := &&($t464, $t465) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t466 := $And($t464, $t465);

    // $t467 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t467 := $IsParentMutation($t12, 5, $t13);

    // $t468 := &&($t466, $t467) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t468 := $And($t466, $t467);

    // if ($t468) goto L179 else goto L180 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t468) { goto L179; } else { goto L180; }

    // label L179 at .\sources\ConditionalBorrowChain.move:106:9+25
L179:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L180 at .\sources\ConditionalBorrowChain.move:106:9+25
L180:

    // $t469 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t469 := $IsParentMutation($t14, 1, $t15);

    // $t470 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t470 := $IsParentMutation($t13, 5, $t14);

    // $t471 := &&($t469, $t470) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t471 := $And($t469, $t470);

    // $t472 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t472 := $IsParentMutation($t12, 6, $t13);

    // $t473 := &&($t471, $t472) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t473 := $And($t471, $t472);

    // if ($t473) goto L181 else goto L182 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t473) { goto L181; } else { goto L182; }

    // label L181 at .\sources\ConditionalBorrowChain.move:106:9+25
L181:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L182 at .\sources\ConditionalBorrowChain.move:106:9+25
L182:

    // $t474 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t474 := $IsParentMutation($t14, 1, $t15);

    // $t475 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t475 := $IsParentMutation($t13, 6, $t14);

    // $t476 := &&($t474, $t475) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t476 := $And($t474, $t475);

    // $t477 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t477 := $IsParentMutation($t12, 0, $t13);

    // $t478 := &&($t476, $t477) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t478 := $And($t476, $t477);

    // if ($t478) goto L183 else goto L184 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t478) { goto L183; } else { goto L184; }

    // label L183 at .\sources\ConditionalBorrowChain.move:106:9+25
L183:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L184 at .\sources\ConditionalBorrowChain.move:106:9+25
L184:

    // $t479 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t479 := $IsParentMutation($t14, 1, $t15);

    // $t480 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t480 := $IsParentMutation($t13, 6, $t14);

    // $t481 := &&($t479, $t480) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t481 := $And($t479, $t480);

    // $t482 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t482 := $IsParentMutation($t12, 1, $t13);

    // $t483 := &&($t481, $t482) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t483 := $And($t481, $t482);

    // if ($t483) goto L185 else goto L186 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t483) { goto L185; } else { goto L186; }

    // label L185 at .\sources\ConditionalBorrowChain.move:106:9+25
L185:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L186 at .\sources\ConditionalBorrowChain.move:106:9+25
L186:

    // $t484 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t484 := $IsParentMutation($t14, 1, $t15);

    // $t485 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t485 := $IsParentMutation($t13, 6, $t14);

    // $t486 := &&($t484, $t485) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t486 := $And($t484, $t485);

    // $t487 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t487 := $IsParentMutation($t12, 2, $t13);

    // $t488 := &&($t486, $t487) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t488 := $And($t486, $t487);

    // if ($t488) goto L187 else goto L188 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t488) { goto L187; } else { goto L188; }

    // label L187 at .\sources\ConditionalBorrowChain.move:106:9+25
L187:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L188 at .\sources\ConditionalBorrowChain.move:106:9+25
L188:

    // $t489 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t489 := $IsParentMutation($t14, 1, $t15);

    // $t490 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t490 := $IsParentMutation($t13, 6, $t14);

    // $t491 := &&($t489, $t490) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t491 := $And($t489, $t490);

    // $t492 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t492 := $IsParentMutation($t12, 3, $t13);

    // $t493 := &&($t491, $t492) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t493 := $And($t491, $t492);

    // if ($t493) goto L189 else goto L190 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t493) { goto L189; } else { goto L190; }

    // label L189 at .\sources\ConditionalBorrowChain.move:106:9+25
L189:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L190 at .\sources\ConditionalBorrowChain.move:106:9+25
L190:

    // $t494 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t494 := $IsParentMutation($t14, 1, $t15);

    // $t495 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t495 := $IsParentMutation($t13, 6, $t14);

    // $t496 := &&($t494, $t495) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t496 := $And($t494, $t495);

    // $t497 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t497 := $IsParentMutation($t12, 4, $t13);

    // $t498 := &&($t496, $t497) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t498 := $And($t496, $t497);

    // if ($t498) goto L191 else goto L192 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t498) { goto L191; } else { goto L192; }

    // label L191 at .\sources\ConditionalBorrowChain.move:106:9+25
L191:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L192 at .\sources\ConditionalBorrowChain.move:106:9+25
L192:

    // $t499 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t499 := $IsParentMutation($t14, 1, $t15);

    // $t500 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t500 := $IsParentMutation($t13, 6, $t14);

    // $t501 := &&($t499, $t500) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t501 := $And($t499, $t500);

    // $t502 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t502 := $IsParentMutation($t12, 5, $t13);

    // $t503 := &&($t501, $t502) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t503 := $And($t501, $t502);

    // if ($t503) goto L193 else goto L194 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t503) { goto L193; } else { goto L194; }

    // label L193 at .\sources\ConditionalBorrowChain.move:106:9+25
L193:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L194 at .\sources\ConditionalBorrowChain.move:106:9+25
L194:

    // $t504 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t504 := $IsParentMutation($t14, 1, $t15);

    // $t505 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t505 := $IsParentMutation($t13, 6, $t14);

    // $t506 := &&($t504, $t505) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t506 := $And($t504, $t505);

    // $t507 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t507 := $IsParentMutation($t12, 6, $t13);

    // $t508 := &&($t506, $t507) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t508 := $And($t506, $t507);

    // if ($t508) goto L195 else goto L196 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t508) { goto L195; } else { goto L196; }

    // label L195 at .\sources\ConditionalBorrowChain.move:106:9+25
L195:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L196 at .\sources\ConditionalBorrowChain.move:106:9+25
L196:

    // $t509 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t509 := $IsParentMutation($t14, 2, $t15);

    // $t510 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t510 := $IsParentMutation($t13, 0, $t14);

    // $t511 := &&($t509, $t510) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t511 := $And($t509, $t510);

    // $t512 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t512 := $IsParentMutation($t12, 0, $t13);

    // $t513 := &&($t511, $t512) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t513 := $And($t511, $t512);

    // if ($t513) goto L197 else goto L198 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t513) { goto L197; } else { goto L198; }

    // label L197 at .\sources\ConditionalBorrowChain.move:106:9+25
L197:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L198 at .\sources\ConditionalBorrowChain.move:106:9+25
L198:

    // $t514 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t514 := $IsParentMutation($t14, 2, $t15);

    // $t515 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t515 := $IsParentMutation($t13, 0, $t14);

    // $t516 := &&($t514, $t515) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t516 := $And($t514, $t515);

    // $t517 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t517 := $IsParentMutation($t12, 1, $t13);

    // $t518 := &&($t516, $t517) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t518 := $And($t516, $t517);

    // if ($t518) goto L199 else goto L200 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t518) { goto L199; } else { goto L200; }

    // label L199 at .\sources\ConditionalBorrowChain.move:106:9+25
L199:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L200 at .\sources\ConditionalBorrowChain.move:106:9+25
L200:

    // $t519 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t519 := $IsParentMutation($t14, 2, $t15);

    // $t520 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t520 := $IsParentMutation($t13, 0, $t14);

    // $t521 := &&($t519, $t520) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t521 := $And($t519, $t520);

    // $t522 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t522 := $IsParentMutation($t12, 2, $t13);

    // $t523 := &&($t521, $t522) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t523 := $And($t521, $t522);

    // if ($t523) goto L201 else goto L202 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t523) { goto L201; } else { goto L202; }

    // label L201 at .\sources\ConditionalBorrowChain.move:106:9+25
L201:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L202 at .\sources\ConditionalBorrowChain.move:106:9+25
L202:

    // $t524 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t524 := $IsParentMutation($t14, 2, $t15);

    // $t525 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t525 := $IsParentMutation($t13, 0, $t14);

    // $t526 := &&($t524, $t525) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t526 := $And($t524, $t525);

    // $t527 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t527 := $IsParentMutation($t12, 3, $t13);

    // $t528 := &&($t526, $t527) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t528 := $And($t526, $t527);

    // if ($t528) goto L203 else goto L204 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t528) { goto L203; } else { goto L204; }

    // label L203 at .\sources\ConditionalBorrowChain.move:106:9+25
L203:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L204 at .\sources\ConditionalBorrowChain.move:106:9+25
L204:

    // $t529 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t529 := $IsParentMutation($t14, 2, $t15);

    // $t530 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t530 := $IsParentMutation($t13, 0, $t14);

    // $t531 := &&($t529, $t530) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t531 := $And($t529, $t530);

    // $t532 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t532 := $IsParentMutation($t12, 4, $t13);

    // $t533 := &&($t531, $t532) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t533 := $And($t531, $t532);

    // if ($t533) goto L205 else goto L206 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t533) { goto L205; } else { goto L206; }

    // label L205 at .\sources\ConditionalBorrowChain.move:106:9+25
L205:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L206 at .\sources\ConditionalBorrowChain.move:106:9+25
L206:

    // $t534 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t534 := $IsParentMutation($t14, 2, $t15);

    // $t535 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t535 := $IsParentMutation($t13, 0, $t14);

    // $t536 := &&($t534, $t535) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t536 := $And($t534, $t535);

    // $t537 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t537 := $IsParentMutation($t12, 5, $t13);

    // $t538 := &&($t536, $t537) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t538 := $And($t536, $t537);

    // if ($t538) goto L207 else goto L208 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t538) { goto L207; } else { goto L208; }

    // label L207 at .\sources\ConditionalBorrowChain.move:106:9+25
L207:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L208 at .\sources\ConditionalBorrowChain.move:106:9+25
L208:

    // $t539 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t539 := $IsParentMutation($t14, 2, $t15);

    // $t540 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t540 := $IsParentMutation($t13, 0, $t14);

    // $t541 := &&($t539, $t540) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t541 := $And($t539, $t540);

    // $t542 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t542 := $IsParentMutation($t12, 6, $t13);

    // $t543 := &&($t541, $t542) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t543 := $And($t541, $t542);

    // if ($t543) goto L209 else goto L210 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t543) { goto L209; } else { goto L210; }

    // label L209 at .\sources\ConditionalBorrowChain.move:106:9+25
L209:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L210 at .\sources\ConditionalBorrowChain.move:106:9+25
L210:

    // $t544 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t544 := $IsParentMutation($t14, 2, $t15);

    // $t545 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t545 := $IsParentMutation($t13, 1, $t14);

    // $t546 := &&($t544, $t545) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t546 := $And($t544, $t545);

    // $t547 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t547 := $IsParentMutation($t12, 0, $t13);

    // $t548 := &&($t546, $t547) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t548 := $And($t546, $t547);

    // if ($t548) goto L211 else goto L212 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t548) { goto L211; } else { goto L212; }

    // label L211 at .\sources\ConditionalBorrowChain.move:106:9+25
L211:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L212 at .\sources\ConditionalBorrowChain.move:106:9+25
L212:

    // $t549 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t549 := $IsParentMutation($t14, 2, $t15);

    // $t550 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t550 := $IsParentMutation($t13, 1, $t14);

    // $t551 := &&($t549, $t550) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t551 := $And($t549, $t550);

    // $t552 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t552 := $IsParentMutation($t12, 1, $t13);

    // $t553 := &&($t551, $t552) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t553 := $And($t551, $t552);

    // if ($t553) goto L213 else goto L214 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t553) { goto L213; } else { goto L214; }

    // label L213 at .\sources\ConditionalBorrowChain.move:106:9+25
L213:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L214 at .\sources\ConditionalBorrowChain.move:106:9+25
L214:

    // $t554 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t554 := $IsParentMutation($t14, 2, $t15);

    // $t555 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t555 := $IsParentMutation($t13, 1, $t14);

    // $t556 := &&($t554, $t555) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t556 := $And($t554, $t555);

    // $t557 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t557 := $IsParentMutation($t12, 2, $t13);

    // $t558 := &&($t556, $t557) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t558 := $And($t556, $t557);

    // if ($t558) goto L215 else goto L216 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t558) { goto L215; } else { goto L216; }

    // label L215 at .\sources\ConditionalBorrowChain.move:106:9+25
L215:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L216 at .\sources\ConditionalBorrowChain.move:106:9+25
L216:

    // $t559 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t559 := $IsParentMutation($t14, 2, $t15);

    // $t560 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t560 := $IsParentMutation($t13, 1, $t14);

    // $t561 := &&($t559, $t560) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t561 := $And($t559, $t560);

    // $t562 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t562 := $IsParentMutation($t12, 3, $t13);

    // $t563 := &&($t561, $t562) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t563 := $And($t561, $t562);

    // if ($t563) goto L217 else goto L218 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t563) { goto L217; } else { goto L218; }

    // label L217 at .\sources\ConditionalBorrowChain.move:106:9+25
L217:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L218 at .\sources\ConditionalBorrowChain.move:106:9+25
L218:

    // $t564 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t564 := $IsParentMutation($t14, 2, $t15);

    // $t565 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t565 := $IsParentMutation($t13, 1, $t14);

    // $t566 := &&($t564, $t565) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t566 := $And($t564, $t565);

    // $t567 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t567 := $IsParentMutation($t12, 4, $t13);

    // $t568 := &&($t566, $t567) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t568 := $And($t566, $t567);

    // if ($t568) goto L219 else goto L220 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t568) { goto L219; } else { goto L220; }

    // label L219 at .\sources\ConditionalBorrowChain.move:106:9+25
L219:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L220 at .\sources\ConditionalBorrowChain.move:106:9+25
L220:

    // $t569 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t569 := $IsParentMutation($t14, 2, $t15);

    // $t570 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t570 := $IsParentMutation($t13, 1, $t14);

    // $t571 := &&($t569, $t570) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t571 := $And($t569, $t570);

    // $t572 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t572 := $IsParentMutation($t12, 5, $t13);

    // $t573 := &&($t571, $t572) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t573 := $And($t571, $t572);

    // if ($t573) goto L221 else goto L222 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t573) { goto L221; } else { goto L222; }

    // label L221 at .\sources\ConditionalBorrowChain.move:106:9+25
L221:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L222 at .\sources\ConditionalBorrowChain.move:106:9+25
L222:

    // $t574 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t574 := $IsParentMutation($t14, 2, $t15);

    // $t575 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t575 := $IsParentMutation($t13, 1, $t14);

    // $t576 := &&($t574, $t575) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t576 := $And($t574, $t575);

    // $t577 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t577 := $IsParentMutation($t12, 6, $t13);

    // $t578 := &&($t576, $t577) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t578 := $And($t576, $t577);

    // if ($t578) goto L223 else goto L224 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t578) { goto L223; } else { goto L224; }

    // label L223 at .\sources\ConditionalBorrowChain.move:106:9+25
L223:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L224 at .\sources\ConditionalBorrowChain.move:106:9+25
L224:

    // $t579 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t579 := $IsParentMutation($t14, 2, $t15);

    // $t580 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t580 := $IsParentMutation($t13, 2, $t14);

    // $t581 := &&($t579, $t580) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t581 := $And($t579, $t580);

    // $t582 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t582 := $IsParentMutation($t12, 0, $t13);

    // $t583 := &&($t581, $t582) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t583 := $And($t581, $t582);

    // if ($t583) goto L225 else goto L226 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t583) { goto L225; } else { goto L226; }

    // label L225 at .\sources\ConditionalBorrowChain.move:106:9+25
L225:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L226 at .\sources\ConditionalBorrowChain.move:106:9+25
L226:

    // $t584 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t584 := $IsParentMutation($t14, 2, $t15);

    // $t585 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t585 := $IsParentMutation($t13, 2, $t14);

    // $t586 := &&($t584, $t585) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t586 := $And($t584, $t585);

    // $t587 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t587 := $IsParentMutation($t12, 1, $t13);

    // $t588 := &&($t586, $t587) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t588 := $And($t586, $t587);

    // if ($t588) goto L227 else goto L228 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t588) { goto L227; } else { goto L228; }

    // label L227 at .\sources\ConditionalBorrowChain.move:106:9+25
L227:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L228 at .\sources\ConditionalBorrowChain.move:106:9+25
L228:

    // $t589 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t589 := $IsParentMutation($t14, 2, $t15);

    // $t590 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t590 := $IsParentMutation($t13, 2, $t14);

    // $t591 := &&($t589, $t590) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t591 := $And($t589, $t590);

    // $t592 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t592 := $IsParentMutation($t12, 2, $t13);

    // $t593 := &&($t591, $t592) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t593 := $And($t591, $t592);

    // if ($t593) goto L229 else goto L230 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t593) { goto L229; } else { goto L230; }

    // label L229 at .\sources\ConditionalBorrowChain.move:106:9+25
L229:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L230 at .\sources\ConditionalBorrowChain.move:106:9+25
L230:

    // $t594 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t594 := $IsParentMutation($t14, 2, $t15);

    // $t595 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t595 := $IsParentMutation($t13, 2, $t14);

    // $t596 := &&($t594, $t595) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t596 := $And($t594, $t595);

    // $t597 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t597 := $IsParentMutation($t12, 3, $t13);

    // $t598 := &&($t596, $t597) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t598 := $And($t596, $t597);

    // if ($t598) goto L231 else goto L232 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t598) { goto L231; } else { goto L232; }

    // label L231 at .\sources\ConditionalBorrowChain.move:106:9+25
L231:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L232 at .\sources\ConditionalBorrowChain.move:106:9+25
L232:

    // $t599 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t599 := $IsParentMutation($t14, 2, $t15);

    // $t600 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t600 := $IsParentMutation($t13, 2, $t14);

    // $t601 := &&($t599, $t600) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t601 := $And($t599, $t600);

    // $t602 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t602 := $IsParentMutation($t12, 4, $t13);

    // $t603 := &&($t601, $t602) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t603 := $And($t601, $t602);

    // if ($t603) goto L233 else goto L234 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t603) { goto L233; } else { goto L234; }

    // label L233 at .\sources\ConditionalBorrowChain.move:106:9+25
L233:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L234 at .\sources\ConditionalBorrowChain.move:106:9+25
L234:

    // $t604 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t604 := $IsParentMutation($t14, 2, $t15);

    // $t605 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t605 := $IsParentMutation($t13, 2, $t14);

    // $t606 := &&($t604, $t605) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t606 := $And($t604, $t605);

    // $t607 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t607 := $IsParentMutation($t12, 5, $t13);

    // $t608 := &&($t606, $t607) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t608 := $And($t606, $t607);

    // if ($t608) goto L235 else goto L236 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t608) { goto L235; } else { goto L236; }

    // label L235 at .\sources\ConditionalBorrowChain.move:106:9+25
L235:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L236 at .\sources\ConditionalBorrowChain.move:106:9+25
L236:

    // $t609 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t609 := $IsParentMutation($t14, 2, $t15);

    // $t610 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t610 := $IsParentMutation($t13, 2, $t14);

    // $t611 := &&($t609, $t610) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t611 := $And($t609, $t610);

    // $t612 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t612 := $IsParentMutation($t12, 6, $t13);

    // $t613 := &&($t611, $t612) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t613 := $And($t611, $t612);

    // if ($t613) goto L237 else goto L238 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t613) { goto L237; } else { goto L238; }

    // label L237 at .\sources\ConditionalBorrowChain.move:106:9+25
L237:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L238 at .\sources\ConditionalBorrowChain.move:106:9+25
L238:

    // $t614 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t614 := $IsParentMutation($t14, 2, $t15);

    // $t615 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t615 := $IsParentMutation($t13, 3, $t14);

    // $t616 := &&($t614, $t615) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t616 := $And($t614, $t615);

    // $t617 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t617 := $IsParentMutation($t12, 0, $t13);

    // $t618 := &&($t616, $t617) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t618 := $And($t616, $t617);

    // if ($t618) goto L239 else goto L240 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t618) { goto L239; } else { goto L240; }

    // label L239 at .\sources\ConditionalBorrowChain.move:106:9+25
L239:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L240 at .\sources\ConditionalBorrowChain.move:106:9+25
L240:

    // $t619 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t619 := $IsParentMutation($t14, 2, $t15);

    // $t620 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t620 := $IsParentMutation($t13, 3, $t14);

    // $t621 := &&($t619, $t620) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t621 := $And($t619, $t620);

    // $t622 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t622 := $IsParentMutation($t12, 1, $t13);

    // $t623 := &&($t621, $t622) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t623 := $And($t621, $t622);

    // if ($t623) goto L241 else goto L242 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t623) { goto L241; } else { goto L242; }

    // label L241 at .\sources\ConditionalBorrowChain.move:106:9+25
L241:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L242 at .\sources\ConditionalBorrowChain.move:106:9+25
L242:

    // $t624 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t624 := $IsParentMutation($t14, 2, $t15);

    // $t625 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t625 := $IsParentMutation($t13, 3, $t14);

    // $t626 := &&($t624, $t625) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t626 := $And($t624, $t625);

    // $t627 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t627 := $IsParentMutation($t12, 2, $t13);

    // $t628 := &&($t626, $t627) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t628 := $And($t626, $t627);

    // if ($t628) goto L243 else goto L244 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t628) { goto L243; } else { goto L244; }

    // label L243 at .\sources\ConditionalBorrowChain.move:106:9+25
L243:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L244 at .\sources\ConditionalBorrowChain.move:106:9+25
L244:

    // $t629 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t629 := $IsParentMutation($t14, 2, $t15);

    // $t630 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t630 := $IsParentMutation($t13, 3, $t14);

    // $t631 := &&($t629, $t630) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t631 := $And($t629, $t630);

    // $t632 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t632 := $IsParentMutation($t12, 3, $t13);

    // $t633 := &&($t631, $t632) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t633 := $And($t631, $t632);

    // if ($t633) goto L245 else goto L246 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t633) { goto L245; } else { goto L246; }

    // label L245 at .\sources\ConditionalBorrowChain.move:106:9+25
L245:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L246 at .\sources\ConditionalBorrowChain.move:106:9+25
L246:

    // $t634 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t634 := $IsParentMutation($t14, 2, $t15);

    // $t635 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t635 := $IsParentMutation($t13, 3, $t14);

    // $t636 := &&($t634, $t635) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t636 := $And($t634, $t635);

    // $t637 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t637 := $IsParentMutation($t12, 4, $t13);

    // $t638 := &&($t636, $t637) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t638 := $And($t636, $t637);

    // if ($t638) goto L247 else goto L248 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t638) { goto L247; } else { goto L248; }

    // label L247 at .\sources\ConditionalBorrowChain.move:106:9+25
L247:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L248 at .\sources\ConditionalBorrowChain.move:106:9+25
L248:

    // $t639 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t639 := $IsParentMutation($t14, 2, $t15);

    // $t640 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t640 := $IsParentMutation($t13, 3, $t14);

    // $t641 := &&($t639, $t640) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t641 := $And($t639, $t640);

    // $t642 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t642 := $IsParentMutation($t12, 5, $t13);

    // $t643 := &&($t641, $t642) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t643 := $And($t641, $t642);

    // if ($t643) goto L249 else goto L250 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t643) { goto L249; } else { goto L250; }

    // label L249 at .\sources\ConditionalBorrowChain.move:106:9+25
L249:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L250 at .\sources\ConditionalBorrowChain.move:106:9+25
L250:

    // $t644 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t644 := $IsParentMutation($t14, 2, $t15);

    // $t645 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t645 := $IsParentMutation($t13, 3, $t14);

    // $t646 := &&($t644, $t645) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t646 := $And($t644, $t645);

    // $t647 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t647 := $IsParentMutation($t12, 6, $t13);

    // $t648 := &&($t646, $t647) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t648 := $And($t646, $t647);

    // if ($t648) goto L251 else goto L252 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t648) { goto L251; } else { goto L252; }

    // label L251 at .\sources\ConditionalBorrowChain.move:106:9+25
L251:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L252 at .\sources\ConditionalBorrowChain.move:106:9+25
L252:

    // $t649 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t649 := $IsParentMutation($t14, 2, $t15);

    // $t650 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t650 := $IsParentMutation($t13, 4, $t14);

    // $t651 := &&($t649, $t650) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t651 := $And($t649, $t650);

    // $t652 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t652 := $IsParentMutation($t12, 0, $t13);

    // $t653 := &&($t651, $t652) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t653 := $And($t651, $t652);

    // if ($t653) goto L253 else goto L254 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t653) { goto L253; } else { goto L254; }

    // label L253 at .\sources\ConditionalBorrowChain.move:106:9+25
L253:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L254 at .\sources\ConditionalBorrowChain.move:106:9+25
L254:

    // $t654 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t654 := $IsParentMutation($t14, 2, $t15);

    // $t655 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t655 := $IsParentMutation($t13, 4, $t14);

    // $t656 := &&($t654, $t655) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t656 := $And($t654, $t655);

    // $t657 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t657 := $IsParentMutation($t12, 1, $t13);

    // $t658 := &&($t656, $t657) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t658 := $And($t656, $t657);

    // if ($t658) goto L255 else goto L256 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t658) { goto L255; } else { goto L256; }

    // label L255 at .\sources\ConditionalBorrowChain.move:106:9+25
L255:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L256 at .\sources\ConditionalBorrowChain.move:106:9+25
L256:

    // $t659 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t659 := $IsParentMutation($t14, 2, $t15);

    // $t660 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t660 := $IsParentMutation($t13, 4, $t14);

    // $t661 := &&($t659, $t660) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t661 := $And($t659, $t660);

    // $t662 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t662 := $IsParentMutation($t12, 2, $t13);

    // $t663 := &&($t661, $t662) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t663 := $And($t661, $t662);

    // if ($t663) goto L257 else goto L258 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t663) { goto L257; } else { goto L258; }

    // label L257 at .\sources\ConditionalBorrowChain.move:106:9+25
L257:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L258 at .\sources\ConditionalBorrowChain.move:106:9+25
L258:

    // $t664 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t664 := $IsParentMutation($t14, 2, $t15);

    // $t665 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t665 := $IsParentMutation($t13, 4, $t14);

    // $t666 := &&($t664, $t665) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t666 := $And($t664, $t665);

    // $t667 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t667 := $IsParentMutation($t12, 3, $t13);

    // $t668 := &&($t666, $t667) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t668 := $And($t666, $t667);

    // if ($t668) goto L259 else goto L260 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t668) { goto L259; } else { goto L260; }

    // label L259 at .\sources\ConditionalBorrowChain.move:106:9+25
L259:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L260 at .\sources\ConditionalBorrowChain.move:106:9+25
L260:

    // $t669 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t669 := $IsParentMutation($t14, 2, $t15);

    // $t670 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t670 := $IsParentMutation($t13, 4, $t14);

    // $t671 := &&($t669, $t670) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t671 := $And($t669, $t670);

    // $t672 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t672 := $IsParentMutation($t12, 4, $t13);

    // $t673 := &&($t671, $t672) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t673 := $And($t671, $t672);

    // if ($t673) goto L261 else goto L262 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t673) { goto L261; } else { goto L262; }

    // label L261 at .\sources\ConditionalBorrowChain.move:106:9+25
L261:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L262 at .\sources\ConditionalBorrowChain.move:106:9+25
L262:

    // $t674 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t674 := $IsParentMutation($t14, 2, $t15);

    // $t675 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t675 := $IsParentMutation($t13, 4, $t14);

    // $t676 := &&($t674, $t675) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t676 := $And($t674, $t675);

    // $t677 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t677 := $IsParentMutation($t12, 5, $t13);

    // $t678 := &&($t676, $t677) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t678 := $And($t676, $t677);

    // if ($t678) goto L263 else goto L264 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t678) { goto L263; } else { goto L264; }

    // label L263 at .\sources\ConditionalBorrowChain.move:106:9+25
L263:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L264 at .\sources\ConditionalBorrowChain.move:106:9+25
L264:

    // $t679 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t679 := $IsParentMutation($t14, 2, $t15);

    // $t680 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t680 := $IsParentMutation($t13, 4, $t14);

    // $t681 := &&($t679, $t680) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t681 := $And($t679, $t680);

    // $t682 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t682 := $IsParentMutation($t12, 6, $t13);

    // $t683 := &&($t681, $t682) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t683 := $And($t681, $t682);

    // if ($t683) goto L265 else goto L266 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t683) { goto L265; } else { goto L266; }

    // label L265 at .\sources\ConditionalBorrowChain.move:106:9+25
L265:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L266 at .\sources\ConditionalBorrowChain.move:106:9+25
L266:

    // $t684 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t684 := $IsParentMutation($t14, 2, $t15);

    // $t685 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t685 := $IsParentMutation($t13, 5, $t14);

    // $t686 := &&($t684, $t685) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t686 := $And($t684, $t685);

    // $t687 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t687 := $IsParentMutation($t12, 0, $t13);

    // $t688 := &&($t686, $t687) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t688 := $And($t686, $t687);

    // if ($t688) goto L267 else goto L268 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t688) { goto L267; } else { goto L268; }

    // label L267 at .\sources\ConditionalBorrowChain.move:106:9+25
L267:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L268 at .\sources\ConditionalBorrowChain.move:106:9+25
L268:

    // $t689 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t689 := $IsParentMutation($t14, 2, $t15);

    // $t690 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t690 := $IsParentMutation($t13, 5, $t14);

    // $t691 := &&($t689, $t690) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t691 := $And($t689, $t690);

    // $t692 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t692 := $IsParentMutation($t12, 1, $t13);

    // $t693 := &&($t691, $t692) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t693 := $And($t691, $t692);

    // if ($t693) goto L269 else goto L270 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t693) { goto L269; } else { goto L270; }

    // label L269 at .\sources\ConditionalBorrowChain.move:106:9+25
L269:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L270 at .\sources\ConditionalBorrowChain.move:106:9+25
L270:

    // $t694 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t694 := $IsParentMutation($t14, 2, $t15);

    // $t695 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t695 := $IsParentMutation($t13, 5, $t14);

    // $t696 := &&($t694, $t695) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t696 := $And($t694, $t695);

    // $t697 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t697 := $IsParentMutation($t12, 2, $t13);

    // $t698 := &&($t696, $t697) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t698 := $And($t696, $t697);

    // if ($t698) goto L271 else goto L272 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t698) { goto L271; } else { goto L272; }

    // label L271 at .\sources\ConditionalBorrowChain.move:106:9+25
L271:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L272 at .\sources\ConditionalBorrowChain.move:106:9+25
L272:

    // $t699 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t699 := $IsParentMutation($t14, 2, $t15);

    // $t700 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t700 := $IsParentMutation($t13, 5, $t14);

    // $t701 := &&($t699, $t700) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t701 := $And($t699, $t700);

    // $t702 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t702 := $IsParentMutation($t12, 3, $t13);

    // $t703 := &&($t701, $t702) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t703 := $And($t701, $t702);

    // if ($t703) goto L273 else goto L274 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t703) { goto L273; } else { goto L274; }

    // label L273 at .\sources\ConditionalBorrowChain.move:106:9+25
L273:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L274 at .\sources\ConditionalBorrowChain.move:106:9+25
L274:

    // $t704 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t704 := $IsParentMutation($t14, 2, $t15);

    // $t705 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t705 := $IsParentMutation($t13, 5, $t14);

    // $t706 := &&($t704, $t705) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t706 := $And($t704, $t705);

    // $t707 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t707 := $IsParentMutation($t12, 4, $t13);

    // $t708 := &&($t706, $t707) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t708 := $And($t706, $t707);

    // if ($t708) goto L275 else goto L276 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t708) { goto L275; } else { goto L276; }

    // label L275 at .\sources\ConditionalBorrowChain.move:106:9+25
L275:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L276 at .\sources\ConditionalBorrowChain.move:106:9+25
L276:

    // $t709 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t709 := $IsParentMutation($t14, 2, $t15);

    // $t710 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t710 := $IsParentMutation($t13, 5, $t14);

    // $t711 := &&($t709, $t710) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t711 := $And($t709, $t710);

    // $t712 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t712 := $IsParentMutation($t12, 5, $t13);

    // $t713 := &&($t711, $t712) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t713 := $And($t711, $t712);

    // if ($t713) goto L277 else goto L278 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t713) { goto L277; } else { goto L278; }

    // label L277 at .\sources\ConditionalBorrowChain.move:106:9+25
L277:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L278 at .\sources\ConditionalBorrowChain.move:106:9+25
L278:

    // $t714 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t714 := $IsParentMutation($t14, 2, $t15);

    // $t715 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t715 := $IsParentMutation($t13, 5, $t14);

    // $t716 := &&($t714, $t715) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t716 := $And($t714, $t715);

    // $t717 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t717 := $IsParentMutation($t12, 6, $t13);

    // $t718 := &&($t716, $t717) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t718 := $And($t716, $t717);

    // if ($t718) goto L279 else goto L280 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t718) { goto L279; } else { goto L280; }

    // label L279 at .\sources\ConditionalBorrowChain.move:106:9+25
L279:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L280 at .\sources\ConditionalBorrowChain.move:106:9+25
L280:

    // $t719 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t719 := $IsParentMutation($t14, 2, $t15);

    // $t720 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t720 := $IsParentMutation($t13, 6, $t14);

    // $t721 := &&($t719, $t720) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t721 := $And($t719, $t720);

    // $t722 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t722 := $IsParentMutation($t12, 0, $t13);

    // $t723 := &&($t721, $t722) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t723 := $And($t721, $t722);

    // if ($t723) goto L281 else goto L282 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t723) { goto L281; } else { goto L282; }

    // label L281 at .\sources\ConditionalBorrowChain.move:106:9+25
L281:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L282 at .\sources\ConditionalBorrowChain.move:106:9+25
L282:

    // $t724 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t724 := $IsParentMutation($t14, 2, $t15);

    // $t725 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t725 := $IsParentMutation($t13, 6, $t14);

    // $t726 := &&($t724, $t725) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t726 := $And($t724, $t725);

    // $t727 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t727 := $IsParentMutation($t12, 1, $t13);

    // $t728 := &&($t726, $t727) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t728 := $And($t726, $t727);

    // if ($t728) goto L283 else goto L284 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t728) { goto L283; } else { goto L284; }

    // label L283 at .\sources\ConditionalBorrowChain.move:106:9+25
L283:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L284 at .\sources\ConditionalBorrowChain.move:106:9+25
L284:

    // $t729 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t729 := $IsParentMutation($t14, 2, $t15);

    // $t730 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t730 := $IsParentMutation($t13, 6, $t14);

    // $t731 := &&($t729, $t730) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t731 := $And($t729, $t730);

    // $t732 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t732 := $IsParentMutation($t12, 2, $t13);

    // $t733 := &&($t731, $t732) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t733 := $And($t731, $t732);

    // if ($t733) goto L285 else goto L286 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t733) { goto L285; } else { goto L286; }

    // label L285 at .\sources\ConditionalBorrowChain.move:106:9+25
L285:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L286 at .\sources\ConditionalBorrowChain.move:106:9+25
L286:

    // $t734 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t734 := $IsParentMutation($t14, 2, $t15);

    // $t735 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t735 := $IsParentMutation($t13, 6, $t14);

    // $t736 := &&($t734, $t735) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t736 := $And($t734, $t735);

    // $t737 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t737 := $IsParentMutation($t12, 3, $t13);

    // $t738 := &&($t736, $t737) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t738 := $And($t736, $t737);

    // if ($t738) goto L287 else goto L288 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t738) { goto L287; } else { goto L288; }

    // label L287 at .\sources\ConditionalBorrowChain.move:106:9+25
L287:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L288 at .\sources\ConditionalBorrowChain.move:106:9+25
L288:

    // $t739 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t739 := $IsParentMutation($t14, 2, $t15);

    // $t740 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t740 := $IsParentMutation($t13, 6, $t14);

    // $t741 := &&($t739, $t740) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t741 := $And($t739, $t740);

    // $t742 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t742 := $IsParentMutation($t12, 4, $t13);

    // $t743 := &&($t741, $t742) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t743 := $And($t741, $t742);

    // if ($t743) goto L289 else goto L290 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t743) { goto L289; } else { goto L290; }

    // label L289 at .\sources\ConditionalBorrowChain.move:106:9+25
L289:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L290 at .\sources\ConditionalBorrowChain.move:106:9+25
L290:

    // $t744 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t744 := $IsParentMutation($t14, 2, $t15);

    // $t745 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t745 := $IsParentMutation($t13, 6, $t14);

    // $t746 := &&($t744, $t745) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t746 := $And($t744, $t745);

    // $t747 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t747 := $IsParentMutation($t12, 5, $t13);

    // $t748 := &&($t746, $t747) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t748 := $And($t746, $t747);

    // if ($t748) goto L291 else goto L292 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t748) { goto L291; } else { goto L292; }

    // label L291 at .\sources\ConditionalBorrowChain.move:106:9+25
L291:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L292 at .\sources\ConditionalBorrowChain.move:106:9+25
L292:

    // $t749 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t749 := $IsParentMutation($t14, 2, $t15);

    // $t750 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t750 := $IsParentMutation($t13, 6, $t14);

    // $t751 := &&($t749, $t750) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t751 := $And($t749, $t750);

    // $t752 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t752 := $IsParentMutation($t12, 6, $t13);

    // $t753 := &&($t751, $t752) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t753 := $And($t751, $t752);

    // if ($t753) goto L293 else goto L294 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t753) { goto L293; } else { goto L294; }

    // label L293 at .\sources\ConditionalBorrowChain.move:106:9+25
L293:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L294 at .\sources\ConditionalBorrowChain.move:106:9+25
L294:

    // $t754 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t754 := $IsParentMutation($t14, 3, $t15);

    // $t755 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t755 := $IsParentMutation($t13, 0, $t14);

    // $t756 := &&($t754, $t755) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t756 := $And($t754, $t755);

    // $t757 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t757 := $IsParentMutation($t12, 0, $t13);

    // $t758 := &&($t756, $t757) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t758 := $And($t756, $t757);

    // if ($t758) goto L295 else goto L296 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t758) { goto L295; } else { goto L296; }

    // label L295 at .\sources\ConditionalBorrowChain.move:106:9+25
L295:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L296 at .\sources\ConditionalBorrowChain.move:106:9+25
L296:

    // $t759 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t759 := $IsParentMutation($t14, 3, $t15);

    // $t760 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t760 := $IsParentMutation($t13, 0, $t14);

    // $t761 := &&($t759, $t760) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t761 := $And($t759, $t760);

    // $t762 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t762 := $IsParentMutation($t12, 1, $t13);

    // $t763 := &&($t761, $t762) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t763 := $And($t761, $t762);

    // if ($t763) goto L297 else goto L298 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t763) { goto L297; } else { goto L298; }

    // label L297 at .\sources\ConditionalBorrowChain.move:106:9+25
L297:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L298 at .\sources\ConditionalBorrowChain.move:106:9+25
L298:

    // $t764 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t764 := $IsParentMutation($t14, 3, $t15);

    // $t765 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t765 := $IsParentMutation($t13, 0, $t14);

    // $t766 := &&($t764, $t765) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t766 := $And($t764, $t765);

    // $t767 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t767 := $IsParentMutation($t12, 2, $t13);

    // $t768 := &&($t766, $t767) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t768 := $And($t766, $t767);

    // if ($t768) goto L299 else goto L300 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t768) { goto L299; } else { goto L300; }

    // label L299 at .\sources\ConditionalBorrowChain.move:106:9+25
L299:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L300 at .\sources\ConditionalBorrowChain.move:106:9+25
L300:

    // $t769 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t769 := $IsParentMutation($t14, 3, $t15);

    // $t770 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t770 := $IsParentMutation($t13, 0, $t14);

    // $t771 := &&($t769, $t770) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t771 := $And($t769, $t770);

    // $t772 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t772 := $IsParentMutation($t12, 3, $t13);

    // $t773 := &&($t771, $t772) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t773 := $And($t771, $t772);

    // if ($t773) goto L301 else goto L302 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t773) { goto L301; } else { goto L302; }

    // label L301 at .\sources\ConditionalBorrowChain.move:106:9+25
L301:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L302 at .\sources\ConditionalBorrowChain.move:106:9+25
L302:

    // $t774 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t774 := $IsParentMutation($t14, 3, $t15);

    // $t775 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t775 := $IsParentMutation($t13, 0, $t14);

    // $t776 := &&($t774, $t775) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t776 := $And($t774, $t775);

    // $t777 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t777 := $IsParentMutation($t12, 4, $t13);

    // $t778 := &&($t776, $t777) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t778 := $And($t776, $t777);

    // if ($t778) goto L303 else goto L304 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t778) { goto L303; } else { goto L304; }

    // label L303 at .\sources\ConditionalBorrowChain.move:106:9+25
L303:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L304 at .\sources\ConditionalBorrowChain.move:106:9+25
L304:

    // $t779 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t779 := $IsParentMutation($t14, 3, $t15);

    // $t780 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t780 := $IsParentMutation($t13, 0, $t14);

    // $t781 := &&($t779, $t780) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t781 := $And($t779, $t780);

    // $t782 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t782 := $IsParentMutation($t12, 5, $t13);

    // $t783 := &&($t781, $t782) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t783 := $And($t781, $t782);

    // if ($t783) goto L305 else goto L306 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t783) { goto L305; } else { goto L306; }

    // label L305 at .\sources\ConditionalBorrowChain.move:106:9+25
L305:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L306 at .\sources\ConditionalBorrowChain.move:106:9+25
L306:

    // $t784 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t784 := $IsParentMutation($t14, 3, $t15);

    // $t785 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t785 := $IsParentMutation($t13, 0, $t14);

    // $t786 := &&($t784, $t785) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t786 := $And($t784, $t785);

    // $t787 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t787 := $IsParentMutation($t12, 6, $t13);

    // $t788 := &&($t786, $t787) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t788 := $And($t786, $t787);

    // if ($t788) goto L307 else goto L308 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t788) { goto L307; } else { goto L308; }

    // label L307 at .\sources\ConditionalBorrowChain.move:106:9+25
L307:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L308 at .\sources\ConditionalBorrowChain.move:106:9+25
L308:

    // $t789 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t789 := $IsParentMutation($t14, 3, $t15);

    // $t790 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t790 := $IsParentMutation($t13, 1, $t14);

    // $t791 := &&($t789, $t790) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t791 := $And($t789, $t790);

    // $t792 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t792 := $IsParentMutation($t12, 0, $t13);

    // $t793 := &&($t791, $t792) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t793 := $And($t791, $t792);

    // if ($t793) goto L309 else goto L310 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t793) { goto L309; } else { goto L310; }

    // label L309 at .\sources\ConditionalBorrowChain.move:106:9+25
L309:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L310 at .\sources\ConditionalBorrowChain.move:106:9+25
L310:

    // $t794 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t794 := $IsParentMutation($t14, 3, $t15);

    // $t795 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t795 := $IsParentMutation($t13, 1, $t14);

    // $t796 := &&($t794, $t795) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t796 := $And($t794, $t795);

    // $t797 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t797 := $IsParentMutation($t12, 1, $t13);

    // $t798 := &&($t796, $t797) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t798 := $And($t796, $t797);

    // if ($t798) goto L311 else goto L312 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t798) { goto L311; } else { goto L312; }

    // label L311 at .\sources\ConditionalBorrowChain.move:106:9+25
L311:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L312 at .\sources\ConditionalBorrowChain.move:106:9+25
L312:

    // $t799 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t799 := $IsParentMutation($t14, 3, $t15);

    // $t800 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t800 := $IsParentMutation($t13, 1, $t14);

    // $t801 := &&($t799, $t800) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t801 := $And($t799, $t800);

    // $t802 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t802 := $IsParentMutation($t12, 2, $t13);

    // $t803 := &&($t801, $t802) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t803 := $And($t801, $t802);

    // if ($t803) goto L313 else goto L314 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t803) { goto L313; } else { goto L314; }

    // label L313 at .\sources\ConditionalBorrowChain.move:106:9+25
L313:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L314 at .\sources\ConditionalBorrowChain.move:106:9+25
L314:

    // $t804 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t804 := $IsParentMutation($t14, 3, $t15);

    // $t805 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t805 := $IsParentMutation($t13, 1, $t14);

    // $t806 := &&($t804, $t805) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t806 := $And($t804, $t805);

    // $t807 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t807 := $IsParentMutation($t12, 3, $t13);

    // $t808 := &&($t806, $t807) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t808 := $And($t806, $t807);

    // if ($t808) goto L315 else goto L316 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t808) { goto L315; } else { goto L316; }

    // label L315 at .\sources\ConditionalBorrowChain.move:106:9+25
L315:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L316 at .\sources\ConditionalBorrowChain.move:106:9+25
L316:

    // $t809 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t809 := $IsParentMutation($t14, 3, $t15);

    // $t810 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t810 := $IsParentMutation($t13, 1, $t14);

    // $t811 := &&($t809, $t810) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t811 := $And($t809, $t810);

    // $t812 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t812 := $IsParentMutation($t12, 4, $t13);

    // $t813 := &&($t811, $t812) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t813 := $And($t811, $t812);

    // if ($t813) goto L317 else goto L318 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t813) { goto L317; } else { goto L318; }

    // label L317 at .\sources\ConditionalBorrowChain.move:106:9+25
L317:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L318 at .\sources\ConditionalBorrowChain.move:106:9+25
L318:

    // $t814 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t814 := $IsParentMutation($t14, 3, $t15);

    // $t815 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t815 := $IsParentMutation($t13, 1, $t14);

    // $t816 := &&($t814, $t815) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t816 := $And($t814, $t815);

    // $t817 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t817 := $IsParentMutation($t12, 5, $t13);

    // $t818 := &&($t816, $t817) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t818 := $And($t816, $t817);

    // if ($t818) goto L319 else goto L320 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t818) { goto L319; } else { goto L320; }

    // label L319 at .\sources\ConditionalBorrowChain.move:106:9+25
L319:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L320 at .\sources\ConditionalBorrowChain.move:106:9+25
L320:

    // $t819 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t819 := $IsParentMutation($t14, 3, $t15);

    // $t820 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t820 := $IsParentMutation($t13, 1, $t14);

    // $t821 := &&($t819, $t820) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t821 := $And($t819, $t820);

    // $t822 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t822 := $IsParentMutation($t12, 6, $t13);

    // $t823 := &&($t821, $t822) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t823 := $And($t821, $t822);

    // if ($t823) goto L321 else goto L322 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t823) { goto L321; } else { goto L322; }

    // label L321 at .\sources\ConditionalBorrowChain.move:106:9+25
L321:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L322 at .\sources\ConditionalBorrowChain.move:106:9+25
L322:

    // $t824 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t824 := $IsParentMutation($t14, 3, $t15);

    // $t825 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t825 := $IsParentMutation($t13, 2, $t14);

    // $t826 := &&($t824, $t825) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t826 := $And($t824, $t825);

    // $t827 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t827 := $IsParentMutation($t12, 0, $t13);

    // $t828 := &&($t826, $t827) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t828 := $And($t826, $t827);

    // if ($t828) goto L323 else goto L324 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t828) { goto L323; } else { goto L324; }

    // label L323 at .\sources\ConditionalBorrowChain.move:106:9+25
L323:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L324 at .\sources\ConditionalBorrowChain.move:106:9+25
L324:

    // $t829 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t829 := $IsParentMutation($t14, 3, $t15);

    // $t830 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t830 := $IsParentMutation($t13, 2, $t14);

    // $t831 := &&($t829, $t830) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t831 := $And($t829, $t830);

    // $t832 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t832 := $IsParentMutation($t12, 1, $t13);

    // $t833 := &&($t831, $t832) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t833 := $And($t831, $t832);

    // if ($t833) goto L325 else goto L326 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t833) { goto L325; } else { goto L326; }

    // label L325 at .\sources\ConditionalBorrowChain.move:106:9+25
L325:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L326 at .\sources\ConditionalBorrowChain.move:106:9+25
L326:

    // $t834 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t834 := $IsParentMutation($t14, 3, $t15);

    // $t835 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t835 := $IsParentMutation($t13, 2, $t14);

    // $t836 := &&($t834, $t835) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t836 := $And($t834, $t835);

    // $t837 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t837 := $IsParentMutation($t12, 2, $t13);

    // $t838 := &&($t836, $t837) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t838 := $And($t836, $t837);

    // if ($t838) goto L327 else goto L328 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t838) { goto L327; } else { goto L328; }

    // label L327 at .\sources\ConditionalBorrowChain.move:106:9+25
L327:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L328 at .\sources\ConditionalBorrowChain.move:106:9+25
L328:

    // $t839 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t839 := $IsParentMutation($t14, 3, $t15);

    // $t840 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t840 := $IsParentMutation($t13, 2, $t14);

    // $t841 := &&($t839, $t840) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t841 := $And($t839, $t840);

    // $t842 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t842 := $IsParentMutation($t12, 3, $t13);

    // $t843 := &&($t841, $t842) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t843 := $And($t841, $t842);

    // if ($t843) goto L329 else goto L330 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t843) { goto L329; } else { goto L330; }

    // label L329 at .\sources\ConditionalBorrowChain.move:106:9+25
L329:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L330 at .\sources\ConditionalBorrowChain.move:106:9+25
L330:

    // $t844 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t844 := $IsParentMutation($t14, 3, $t15);

    // $t845 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t845 := $IsParentMutation($t13, 2, $t14);

    // $t846 := &&($t844, $t845) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t846 := $And($t844, $t845);

    // $t847 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t847 := $IsParentMutation($t12, 4, $t13);

    // $t848 := &&($t846, $t847) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t848 := $And($t846, $t847);

    // if ($t848) goto L331 else goto L332 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t848) { goto L331; } else { goto L332; }

    // label L331 at .\sources\ConditionalBorrowChain.move:106:9+25
L331:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L332 at .\sources\ConditionalBorrowChain.move:106:9+25
L332:

    // $t849 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t849 := $IsParentMutation($t14, 3, $t15);

    // $t850 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t850 := $IsParentMutation($t13, 2, $t14);

    // $t851 := &&($t849, $t850) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t851 := $And($t849, $t850);

    // $t852 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t852 := $IsParentMutation($t12, 5, $t13);

    // $t853 := &&($t851, $t852) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t853 := $And($t851, $t852);

    // if ($t853) goto L333 else goto L334 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t853) { goto L333; } else { goto L334; }

    // label L333 at .\sources\ConditionalBorrowChain.move:106:9+25
L333:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L334 at .\sources\ConditionalBorrowChain.move:106:9+25
L334:

    // $t854 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t854 := $IsParentMutation($t14, 3, $t15);

    // $t855 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t855 := $IsParentMutation($t13, 2, $t14);

    // $t856 := &&($t854, $t855) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t856 := $And($t854, $t855);

    // $t857 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t857 := $IsParentMutation($t12, 6, $t13);

    // $t858 := &&($t856, $t857) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t858 := $And($t856, $t857);

    // if ($t858) goto L335 else goto L336 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t858) { goto L335; } else { goto L336; }

    // label L335 at .\sources\ConditionalBorrowChain.move:106:9+25
L335:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L336 at .\sources\ConditionalBorrowChain.move:106:9+25
L336:

    // $t859 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t859 := $IsParentMutation($t14, 3, $t15);

    // $t860 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t860 := $IsParentMutation($t13, 3, $t14);

    // $t861 := &&($t859, $t860) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t861 := $And($t859, $t860);

    // $t862 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t862 := $IsParentMutation($t12, 0, $t13);

    // $t863 := &&($t861, $t862) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t863 := $And($t861, $t862);

    // if ($t863) goto L337 else goto L338 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t863) { goto L337; } else { goto L338; }

    // label L337 at .\sources\ConditionalBorrowChain.move:106:9+25
L337:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L338 at .\sources\ConditionalBorrowChain.move:106:9+25
L338:

    // $t864 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t864 := $IsParentMutation($t14, 3, $t15);

    // $t865 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t865 := $IsParentMutation($t13, 3, $t14);

    // $t866 := &&($t864, $t865) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t866 := $And($t864, $t865);

    // $t867 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t867 := $IsParentMutation($t12, 1, $t13);

    // $t868 := &&($t866, $t867) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t868 := $And($t866, $t867);

    // if ($t868) goto L339 else goto L340 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t868) { goto L339; } else { goto L340; }

    // label L339 at .\sources\ConditionalBorrowChain.move:106:9+25
L339:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L340 at .\sources\ConditionalBorrowChain.move:106:9+25
L340:

    // $t869 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t869 := $IsParentMutation($t14, 3, $t15);

    // $t870 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t870 := $IsParentMutation($t13, 3, $t14);

    // $t871 := &&($t869, $t870) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t871 := $And($t869, $t870);

    // $t872 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t872 := $IsParentMutation($t12, 2, $t13);

    // $t873 := &&($t871, $t872) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t873 := $And($t871, $t872);

    // if ($t873) goto L341 else goto L342 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t873) { goto L341; } else { goto L342; }

    // label L341 at .\sources\ConditionalBorrowChain.move:106:9+25
L341:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L342 at .\sources\ConditionalBorrowChain.move:106:9+25
L342:

    // $t874 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t874 := $IsParentMutation($t14, 3, $t15);

    // $t875 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t875 := $IsParentMutation($t13, 3, $t14);

    // $t876 := &&($t874, $t875) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t876 := $And($t874, $t875);

    // $t877 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t877 := $IsParentMutation($t12, 3, $t13);

    // $t878 := &&($t876, $t877) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t878 := $And($t876, $t877);

    // if ($t878) goto L343 else goto L344 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t878) { goto L343; } else { goto L344; }

    // label L343 at .\sources\ConditionalBorrowChain.move:106:9+25
L343:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L344 at .\sources\ConditionalBorrowChain.move:106:9+25
L344:

    // $t879 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t879 := $IsParentMutation($t14, 3, $t15);

    // $t880 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t880 := $IsParentMutation($t13, 3, $t14);

    // $t881 := &&($t879, $t880) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t881 := $And($t879, $t880);

    // $t882 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t882 := $IsParentMutation($t12, 4, $t13);

    // $t883 := &&($t881, $t882) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t883 := $And($t881, $t882);

    // if ($t883) goto L345 else goto L346 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t883) { goto L345; } else { goto L346; }

    // label L345 at .\sources\ConditionalBorrowChain.move:106:9+25
L345:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L346 at .\sources\ConditionalBorrowChain.move:106:9+25
L346:

    // $t884 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t884 := $IsParentMutation($t14, 3, $t15);

    // $t885 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t885 := $IsParentMutation($t13, 3, $t14);

    // $t886 := &&($t884, $t885) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t886 := $And($t884, $t885);

    // $t887 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t887 := $IsParentMutation($t12, 5, $t13);

    // $t888 := &&($t886, $t887) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t888 := $And($t886, $t887);

    // if ($t888) goto L347 else goto L348 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t888) { goto L347; } else { goto L348; }

    // label L347 at .\sources\ConditionalBorrowChain.move:106:9+25
L347:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L348 at .\sources\ConditionalBorrowChain.move:106:9+25
L348:

    // $t889 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t889 := $IsParentMutation($t14, 3, $t15);

    // $t890 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t890 := $IsParentMutation($t13, 3, $t14);

    // $t891 := &&($t889, $t890) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t891 := $And($t889, $t890);

    // $t892 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t892 := $IsParentMutation($t12, 6, $t13);

    // $t893 := &&($t891, $t892) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t893 := $And($t891, $t892);

    // if ($t893) goto L349 else goto L350 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t893) { goto L349; } else { goto L350; }

    // label L349 at .\sources\ConditionalBorrowChain.move:106:9+25
L349:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L350 at .\sources\ConditionalBorrowChain.move:106:9+25
L350:

    // $t894 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t894 := $IsParentMutation($t14, 3, $t15);

    // $t895 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t895 := $IsParentMutation($t13, 4, $t14);

    // $t896 := &&($t894, $t895) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t896 := $And($t894, $t895);

    // $t897 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t897 := $IsParentMutation($t12, 0, $t13);

    // $t898 := &&($t896, $t897) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t898 := $And($t896, $t897);

    // if ($t898) goto L351 else goto L352 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t898) { goto L351; } else { goto L352; }

    // label L351 at .\sources\ConditionalBorrowChain.move:106:9+25
L351:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L352 at .\sources\ConditionalBorrowChain.move:106:9+25
L352:

    // $t899 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t899 := $IsParentMutation($t14, 3, $t15);

    // $t900 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t900 := $IsParentMutation($t13, 4, $t14);

    // $t901 := &&($t899, $t900) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t901 := $And($t899, $t900);

    // $t902 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t902 := $IsParentMutation($t12, 1, $t13);

    // $t903 := &&($t901, $t902) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t903 := $And($t901, $t902);

    // if ($t903) goto L353 else goto L354 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t903) { goto L353; } else { goto L354; }

    // label L353 at .\sources\ConditionalBorrowChain.move:106:9+25
L353:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L354 at .\sources\ConditionalBorrowChain.move:106:9+25
L354:

    // $t904 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t904 := $IsParentMutation($t14, 3, $t15);

    // $t905 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t905 := $IsParentMutation($t13, 4, $t14);

    // $t906 := &&($t904, $t905) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t906 := $And($t904, $t905);

    // $t907 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t907 := $IsParentMutation($t12, 2, $t13);

    // $t908 := &&($t906, $t907) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t908 := $And($t906, $t907);

    // if ($t908) goto L355 else goto L356 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t908) { goto L355; } else { goto L356; }

    // label L355 at .\sources\ConditionalBorrowChain.move:106:9+25
L355:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L356 at .\sources\ConditionalBorrowChain.move:106:9+25
L356:

    // $t909 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t909 := $IsParentMutation($t14, 3, $t15);

    // $t910 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t910 := $IsParentMutation($t13, 4, $t14);

    // $t911 := &&($t909, $t910) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t911 := $And($t909, $t910);

    // $t912 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t912 := $IsParentMutation($t12, 3, $t13);

    // $t913 := &&($t911, $t912) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t913 := $And($t911, $t912);

    // if ($t913) goto L357 else goto L358 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t913) { goto L357; } else { goto L358; }

    // label L357 at .\sources\ConditionalBorrowChain.move:106:9+25
L357:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L358 at .\sources\ConditionalBorrowChain.move:106:9+25
L358:

    // $t914 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t914 := $IsParentMutation($t14, 3, $t15);

    // $t915 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t915 := $IsParentMutation($t13, 4, $t14);

    // $t916 := &&($t914, $t915) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t916 := $And($t914, $t915);

    // $t917 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t917 := $IsParentMutation($t12, 4, $t13);

    // $t918 := &&($t916, $t917) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t918 := $And($t916, $t917);

    // if ($t918) goto L359 else goto L360 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t918) { goto L359; } else { goto L360; }

    // label L359 at .\sources\ConditionalBorrowChain.move:106:9+25
L359:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L360 at .\sources\ConditionalBorrowChain.move:106:9+25
L360:

    // $t919 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t919 := $IsParentMutation($t14, 3, $t15);

    // $t920 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t920 := $IsParentMutation($t13, 4, $t14);

    // $t921 := &&($t919, $t920) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t921 := $And($t919, $t920);

    // $t922 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t922 := $IsParentMutation($t12, 5, $t13);

    // $t923 := &&($t921, $t922) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t923 := $And($t921, $t922);

    // if ($t923) goto L361 else goto L362 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t923) { goto L361; } else { goto L362; }

    // label L361 at .\sources\ConditionalBorrowChain.move:106:9+25
L361:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L362 at .\sources\ConditionalBorrowChain.move:106:9+25
L362:

    // $t924 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t924 := $IsParentMutation($t14, 3, $t15);

    // $t925 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t925 := $IsParentMutation($t13, 4, $t14);

    // $t926 := &&($t924, $t925) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t926 := $And($t924, $t925);

    // $t927 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t927 := $IsParentMutation($t12, 6, $t13);

    // $t928 := &&($t926, $t927) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t928 := $And($t926, $t927);

    // if ($t928) goto L363 else goto L364 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t928) { goto L363; } else { goto L364; }

    // label L363 at .\sources\ConditionalBorrowChain.move:106:9+25
L363:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L364 at .\sources\ConditionalBorrowChain.move:106:9+25
L364:

    // $t929 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t929 := $IsParentMutation($t14, 3, $t15);

    // $t930 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t930 := $IsParentMutation($t13, 5, $t14);

    // $t931 := &&($t929, $t930) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t931 := $And($t929, $t930);

    // $t932 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t932 := $IsParentMutation($t12, 0, $t13);

    // $t933 := &&($t931, $t932) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t933 := $And($t931, $t932);

    // if ($t933) goto L365 else goto L366 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t933) { goto L365; } else { goto L366; }

    // label L365 at .\sources\ConditionalBorrowChain.move:106:9+25
L365:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L366 at .\sources\ConditionalBorrowChain.move:106:9+25
L366:

    // $t934 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t934 := $IsParentMutation($t14, 3, $t15);

    // $t935 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t935 := $IsParentMutation($t13, 5, $t14);

    // $t936 := &&($t934, $t935) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t936 := $And($t934, $t935);

    // $t937 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t937 := $IsParentMutation($t12, 1, $t13);

    // $t938 := &&($t936, $t937) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t938 := $And($t936, $t937);

    // if ($t938) goto L367 else goto L368 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t938) { goto L367; } else { goto L368; }

    // label L367 at .\sources\ConditionalBorrowChain.move:106:9+25
L367:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L368 at .\sources\ConditionalBorrowChain.move:106:9+25
L368:

    // $t939 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t939 := $IsParentMutation($t14, 3, $t15);

    // $t940 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t940 := $IsParentMutation($t13, 5, $t14);

    // $t941 := &&($t939, $t940) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t941 := $And($t939, $t940);

    // $t942 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t942 := $IsParentMutation($t12, 2, $t13);

    // $t943 := &&($t941, $t942) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t943 := $And($t941, $t942);

    // if ($t943) goto L369 else goto L370 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t943) { goto L369; } else { goto L370; }

    // label L369 at .\sources\ConditionalBorrowChain.move:106:9+25
L369:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L370 at .\sources\ConditionalBorrowChain.move:106:9+25
L370:

    // $t944 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t944 := $IsParentMutation($t14, 3, $t15);

    // $t945 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t945 := $IsParentMutation($t13, 5, $t14);

    // $t946 := &&($t944, $t945) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t946 := $And($t944, $t945);

    // $t947 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t947 := $IsParentMutation($t12, 3, $t13);

    // $t948 := &&($t946, $t947) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t948 := $And($t946, $t947);

    // if ($t948) goto L371 else goto L372 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t948) { goto L371; } else { goto L372; }

    // label L371 at .\sources\ConditionalBorrowChain.move:106:9+25
L371:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L372 at .\sources\ConditionalBorrowChain.move:106:9+25
L372:

    // $t949 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t949 := $IsParentMutation($t14, 3, $t15);

    // $t950 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t950 := $IsParentMutation($t13, 5, $t14);

    // $t951 := &&($t949, $t950) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t951 := $And($t949, $t950);

    // $t952 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t952 := $IsParentMutation($t12, 4, $t13);

    // $t953 := &&($t951, $t952) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t953 := $And($t951, $t952);

    // if ($t953) goto L373 else goto L374 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t953) { goto L373; } else { goto L374; }

    // label L373 at .\sources\ConditionalBorrowChain.move:106:9+25
L373:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L374 at .\sources\ConditionalBorrowChain.move:106:9+25
L374:

    // $t954 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t954 := $IsParentMutation($t14, 3, $t15);

    // $t955 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t955 := $IsParentMutation($t13, 5, $t14);

    // $t956 := &&($t954, $t955) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t956 := $And($t954, $t955);

    // $t957 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t957 := $IsParentMutation($t12, 5, $t13);

    // $t958 := &&($t956, $t957) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t958 := $And($t956, $t957);

    // if ($t958) goto L375 else goto L376 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t958) { goto L375; } else { goto L376; }

    // label L375 at .\sources\ConditionalBorrowChain.move:106:9+25
L375:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L376 at .\sources\ConditionalBorrowChain.move:106:9+25
L376:

    // $t959 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t959 := $IsParentMutation($t14, 3, $t15);

    // $t960 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t960 := $IsParentMutation($t13, 5, $t14);

    // $t961 := &&($t959, $t960) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t961 := $And($t959, $t960);

    // $t962 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t962 := $IsParentMutation($t12, 6, $t13);

    // $t963 := &&($t961, $t962) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t963 := $And($t961, $t962);

    // if ($t963) goto L377 else goto L378 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t963) { goto L377; } else { goto L378; }

    // label L377 at .\sources\ConditionalBorrowChain.move:106:9+25
L377:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L378 at .\sources\ConditionalBorrowChain.move:106:9+25
L378:

    // $t964 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t964 := $IsParentMutation($t14, 3, $t15);

    // $t965 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t965 := $IsParentMutation($t13, 6, $t14);

    // $t966 := &&($t964, $t965) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t966 := $And($t964, $t965);

    // $t967 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t967 := $IsParentMutation($t12, 0, $t13);

    // $t968 := &&($t966, $t967) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t968 := $And($t966, $t967);

    // if ($t968) goto L379 else goto L380 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t968) { goto L379; } else { goto L380; }

    // label L379 at .\sources\ConditionalBorrowChain.move:106:9+25
L379:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L380 at .\sources\ConditionalBorrowChain.move:106:9+25
L380:

    // $t969 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t969 := $IsParentMutation($t14, 3, $t15);

    // $t970 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t970 := $IsParentMutation($t13, 6, $t14);

    // $t971 := &&($t969, $t970) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t971 := $And($t969, $t970);

    // $t972 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t972 := $IsParentMutation($t12, 1, $t13);

    // $t973 := &&($t971, $t972) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t973 := $And($t971, $t972);

    // if ($t973) goto L381 else goto L382 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t973) { goto L381; } else { goto L382; }

    // label L381 at .\sources\ConditionalBorrowChain.move:106:9+25
L381:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L382 at .\sources\ConditionalBorrowChain.move:106:9+25
L382:

    // $t974 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t974 := $IsParentMutation($t14, 3, $t15);

    // $t975 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t975 := $IsParentMutation($t13, 6, $t14);

    // $t976 := &&($t974, $t975) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t976 := $And($t974, $t975);

    // $t977 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t977 := $IsParentMutation($t12, 2, $t13);

    // $t978 := &&($t976, $t977) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t978 := $And($t976, $t977);

    // if ($t978) goto L383 else goto L384 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t978) { goto L383; } else { goto L384; }

    // label L383 at .\sources\ConditionalBorrowChain.move:106:9+25
L383:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L384 at .\sources\ConditionalBorrowChain.move:106:9+25
L384:

    // $t979 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t979 := $IsParentMutation($t14, 3, $t15);

    // $t980 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t980 := $IsParentMutation($t13, 6, $t14);

    // $t981 := &&($t979, $t980) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t981 := $And($t979, $t980);

    // $t982 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t982 := $IsParentMutation($t12, 3, $t13);

    // $t983 := &&($t981, $t982) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t983 := $And($t981, $t982);

    // if ($t983) goto L385 else goto L386 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t983) { goto L385; } else { goto L386; }

    // label L385 at .\sources\ConditionalBorrowChain.move:106:9+25
L385:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L386 at .\sources\ConditionalBorrowChain.move:106:9+25
L386:

    // $t984 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t984 := $IsParentMutation($t14, 3, $t15);

    // $t985 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t985 := $IsParentMutation($t13, 6, $t14);

    // $t986 := &&($t984, $t985) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t986 := $And($t984, $t985);

    // $t987 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t987 := $IsParentMutation($t12, 4, $t13);

    // $t988 := &&($t986, $t987) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t988 := $And($t986, $t987);

    // if ($t988) goto L387 else goto L388 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t988) { goto L387; } else { goto L388; }

    // label L387 at .\sources\ConditionalBorrowChain.move:106:9+25
L387:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L388 at .\sources\ConditionalBorrowChain.move:106:9+25
L388:

    // $t989 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t989 := $IsParentMutation($t14, 3, $t15);

    // $t990 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t990 := $IsParentMutation($t13, 6, $t14);

    // $t991 := &&($t989, $t990) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t991 := $And($t989, $t990);

    // $t992 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t992 := $IsParentMutation($t12, 5, $t13);

    // $t993 := &&($t991, $t992) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t993 := $And($t991, $t992);

    // if ($t993) goto L389 else goto L390 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t993) { goto L389; } else { goto L390; }

    // label L389 at .\sources\ConditionalBorrowChain.move:106:9+25
L389:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L390 at .\sources\ConditionalBorrowChain.move:106:9+25
L390:

    // $t994 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t994 := $IsParentMutation($t14, 3, $t15);

    // $t995 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t995 := $IsParentMutation($t13, 6, $t14);

    // $t996 := &&($t994, $t995) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t996 := $And($t994, $t995);

    // $t997 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t997 := $IsParentMutation($t12, 6, $t13);

    // $t998 := &&($t996, $t997) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t998 := $And($t996, $t997);

    // if ($t998) goto L391 else goto L392 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t998) { goto L391; } else { goto L392; }

    // label L391 at .\sources\ConditionalBorrowChain.move:106:9+25
L391:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L392 at .\sources\ConditionalBorrowChain.move:106:9+25
L392:

    // $t999 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t999 := $IsParentMutation($t14, 4, $t15);

    // $t1000 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1000 := $IsParentMutation($t13, 0, $t14);

    // $t1001 := &&($t999, $t1000) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1001 := $And($t999, $t1000);

    // $t1002 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1002 := $IsParentMutation($t12, 0, $t13);

    // $t1003 := &&($t1001, $t1002) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1003 := $And($t1001, $t1002);

    // if ($t1003) goto L393 else goto L394 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1003) { goto L393; } else { goto L394; }

    // label L393 at .\sources\ConditionalBorrowChain.move:106:9+25
L393:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L394 at .\sources\ConditionalBorrowChain.move:106:9+25
L394:

    // $t1004 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1004 := $IsParentMutation($t14, 4, $t15);

    // $t1005 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1005 := $IsParentMutation($t13, 0, $t14);

    // $t1006 := &&($t1004, $t1005) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1006 := $And($t1004, $t1005);

    // $t1007 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1007 := $IsParentMutation($t12, 1, $t13);

    // $t1008 := &&($t1006, $t1007) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1008 := $And($t1006, $t1007);

    // if ($t1008) goto L395 else goto L396 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1008) { goto L395; } else { goto L396; }

    // label L395 at .\sources\ConditionalBorrowChain.move:106:9+25
L395:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L396 at .\sources\ConditionalBorrowChain.move:106:9+25
L396:

    // $t1009 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1009 := $IsParentMutation($t14, 4, $t15);

    // $t1010 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1010 := $IsParentMutation($t13, 0, $t14);

    // $t1011 := &&($t1009, $t1010) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1011 := $And($t1009, $t1010);

    // $t1012 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1012 := $IsParentMutation($t12, 2, $t13);

    // $t1013 := &&($t1011, $t1012) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1013 := $And($t1011, $t1012);

    // if ($t1013) goto L397 else goto L398 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1013) { goto L397; } else { goto L398; }

    // label L397 at .\sources\ConditionalBorrowChain.move:106:9+25
L397:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L398 at .\sources\ConditionalBorrowChain.move:106:9+25
L398:

    // $t1014 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1014 := $IsParentMutation($t14, 4, $t15);

    // $t1015 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1015 := $IsParentMutation($t13, 0, $t14);

    // $t1016 := &&($t1014, $t1015) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1016 := $And($t1014, $t1015);

    // $t1017 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1017 := $IsParentMutation($t12, 3, $t13);

    // $t1018 := &&($t1016, $t1017) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1018 := $And($t1016, $t1017);

    // if ($t1018) goto L399 else goto L400 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1018) { goto L399; } else { goto L400; }

    // label L399 at .\sources\ConditionalBorrowChain.move:106:9+25
L399:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L400 at .\sources\ConditionalBorrowChain.move:106:9+25
L400:

    // $t1019 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1019 := $IsParentMutation($t14, 4, $t15);

    // $t1020 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1020 := $IsParentMutation($t13, 0, $t14);

    // $t1021 := &&($t1019, $t1020) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1021 := $And($t1019, $t1020);

    // $t1022 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1022 := $IsParentMutation($t12, 4, $t13);

    // $t1023 := &&($t1021, $t1022) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1023 := $And($t1021, $t1022);

    // if ($t1023) goto L401 else goto L402 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1023) { goto L401; } else { goto L402; }

    // label L401 at .\sources\ConditionalBorrowChain.move:106:9+25
L401:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L402 at .\sources\ConditionalBorrowChain.move:106:9+25
L402:

    // $t1024 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1024 := $IsParentMutation($t14, 4, $t15);

    // $t1025 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1025 := $IsParentMutation($t13, 0, $t14);

    // $t1026 := &&($t1024, $t1025) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1026 := $And($t1024, $t1025);

    // $t1027 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1027 := $IsParentMutation($t12, 5, $t13);

    // $t1028 := &&($t1026, $t1027) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1028 := $And($t1026, $t1027);

    // if ($t1028) goto L403 else goto L404 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1028) { goto L403; } else { goto L404; }

    // label L403 at .\sources\ConditionalBorrowChain.move:106:9+25
L403:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L404 at .\sources\ConditionalBorrowChain.move:106:9+25
L404:

    // $t1029 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1029 := $IsParentMutation($t14, 4, $t15);

    // $t1030 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1030 := $IsParentMutation($t13, 0, $t14);

    // $t1031 := &&($t1029, $t1030) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1031 := $And($t1029, $t1030);

    // $t1032 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1032 := $IsParentMutation($t12, 6, $t13);

    // $t1033 := &&($t1031, $t1032) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1033 := $And($t1031, $t1032);

    // if ($t1033) goto L405 else goto L406 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1033) { goto L405; } else { goto L406; }

    // label L405 at .\sources\ConditionalBorrowChain.move:106:9+25
L405:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L406 at .\sources\ConditionalBorrowChain.move:106:9+25
L406:

    // $t1034 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1034 := $IsParentMutation($t14, 4, $t15);

    // $t1035 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1035 := $IsParentMutation($t13, 1, $t14);

    // $t1036 := &&($t1034, $t1035) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1036 := $And($t1034, $t1035);

    // $t1037 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1037 := $IsParentMutation($t12, 0, $t13);

    // $t1038 := &&($t1036, $t1037) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1038 := $And($t1036, $t1037);

    // if ($t1038) goto L407 else goto L408 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1038) { goto L407; } else { goto L408; }

    // label L407 at .\sources\ConditionalBorrowChain.move:106:9+25
L407:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L408 at .\sources\ConditionalBorrowChain.move:106:9+25
L408:

    // $t1039 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1039 := $IsParentMutation($t14, 4, $t15);

    // $t1040 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1040 := $IsParentMutation($t13, 1, $t14);

    // $t1041 := &&($t1039, $t1040) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1041 := $And($t1039, $t1040);

    // $t1042 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1042 := $IsParentMutation($t12, 1, $t13);

    // $t1043 := &&($t1041, $t1042) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1043 := $And($t1041, $t1042);

    // if ($t1043) goto L409 else goto L410 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1043) { goto L409; } else { goto L410; }

    // label L409 at .\sources\ConditionalBorrowChain.move:106:9+25
L409:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L410 at .\sources\ConditionalBorrowChain.move:106:9+25
L410:

    // $t1044 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1044 := $IsParentMutation($t14, 4, $t15);

    // $t1045 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1045 := $IsParentMutation($t13, 1, $t14);

    // $t1046 := &&($t1044, $t1045) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1046 := $And($t1044, $t1045);

    // $t1047 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1047 := $IsParentMutation($t12, 2, $t13);

    // $t1048 := &&($t1046, $t1047) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1048 := $And($t1046, $t1047);

    // if ($t1048) goto L411 else goto L412 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1048) { goto L411; } else { goto L412; }

    // label L411 at .\sources\ConditionalBorrowChain.move:106:9+25
L411:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L412 at .\sources\ConditionalBorrowChain.move:106:9+25
L412:

    // $t1049 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1049 := $IsParentMutation($t14, 4, $t15);

    // $t1050 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1050 := $IsParentMutation($t13, 1, $t14);

    // $t1051 := &&($t1049, $t1050) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1051 := $And($t1049, $t1050);

    // $t1052 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1052 := $IsParentMutation($t12, 3, $t13);

    // $t1053 := &&($t1051, $t1052) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1053 := $And($t1051, $t1052);

    // if ($t1053) goto L413 else goto L414 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1053) { goto L413; } else { goto L414; }

    // label L413 at .\sources\ConditionalBorrowChain.move:106:9+25
L413:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L414 at .\sources\ConditionalBorrowChain.move:106:9+25
L414:

    // $t1054 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1054 := $IsParentMutation($t14, 4, $t15);

    // $t1055 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1055 := $IsParentMutation($t13, 1, $t14);

    // $t1056 := &&($t1054, $t1055) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1056 := $And($t1054, $t1055);

    // $t1057 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1057 := $IsParentMutation($t12, 4, $t13);

    // $t1058 := &&($t1056, $t1057) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1058 := $And($t1056, $t1057);

    // if ($t1058) goto L415 else goto L416 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1058) { goto L415; } else { goto L416; }

    // label L415 at .\sources\ConditionalBorrowChain.move:106:9+25
L415:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L416 at .\sources\ConditionalBorrowChain.move:106:9+25
L416:

    // $t1059 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1059 := $IsParentMutation($t14, 4, $t15);

    // $t1060 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1060 := $IsParentMutation($t13, 1, $t14);

    // $t1061 := &&($t1059, $t1060) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1061 := $And($t1059, $t1060);

    // $t1062 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1062 := $IsParentMutation($t12, 5, $t13);

    // $t1063 := &&($t1061, $t1062) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1063 := $And($t1061, $t1062);

    // if ($t1063) goto L417 else goto L418 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1063) { goto L417; } else { goto L418; }

    // label L417 at .\sources\ConditionalBorrowChain.move:106:9+25
L417:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L418 at .\sources\ConditionalBorrowChain.move:106:9+25
L418:

    // $t1064 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1064 := $IsParentMutation($t14, 4, $t15);

    // $t1065 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1065 := $IsParentMutation($t13, 1, $t14);

    // $t1066 := &&($t1064, $t1065) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1066 := $And($t1064, $t1065);

    // $t1067 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1067 := $IsParentMutation($t12, 6, $t13);

    // $t1068 := &&($t1066, $t1067) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1068 := $And($t1066, $t1067);

    // if ($t1068) goto L419 else goto L420 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1068) { goto L419; } else { goto L420; }

    // label L419 at .\sources\ConditionalBorrowChain.move:106:9+25
L419:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L420 at .\sources\ConditionalBorrowChain.move:106:9+25
L420:

    // $t1069 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1069 := $IsParentMutation($t14, 4, $t15);

    // $t1070 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1070 := $IsParentMutation($t13, 2, $t14);

    // $t1071 := &&($t1069, $t1070) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1071 := $And($t1069, $t1070);

    // $t1072 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1072 := $IsParentMutation($t12, 0, $t13);

    // $t1073 := &&($t1071, $t1072) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1073 := $And($t1071, $t1072);

    // if ($t1073) goto L421 else goto L422 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1073) { goto L421; } else { goto L422; }

    // label L421 at .\sources\ConditionalBorrowChain.move:106:9+25
L421:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L422 at .\sources\ConditionalBorrowChain.move:106:9+25
L422:

    // $t1074 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1074 := $IsParentMutation($t14, 4, $t15);

    // $t1075 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1075 := $IsParentMutation($t13, 2, $t14);

    // $t1076 := &&($t1074, $t1075) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1076 := $And($t1074, $t1075);

    // $t1077 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1077 := $IsParentMutation($t12, 1, $t13);

    // $t1078 := &&($t1076, $t1077) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1078 := $And($t1076, $t1077);

    // if ($t1078) goto L423 else goto L424 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1078) { goto L423; } else { goto L424; }

    // label L423 at .\sources\ConditionalBorrowChain.move:106:9+25
L423:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L424 at .\sources\ConditionalBorrowChain.move:106:9+25
L424:

    // $t1079 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1079 := $IsParentMutation($t14, 4, $t15);

    // $t1080 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1080 := $IsParentMutation($t13, 2, $t14);

    // $t1081 := &&($t1079, $t1080) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1081 := $And($t1079, $t1080);

    // $t1082 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1082 := $IsParentMutation($t12, 2, $t13);

    // $t1083 := &&($t1081, $t1082) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1083 := $And($t1081, $t1082);

    // if ($t1083) goto L425 else goto L426 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1083) { goto L425; } else { goto L426; }

    // label L425 at .\sources\ConditionalBorrowChain.move:106:9+25
L425:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L426 at .\sources\ConditionalBorrowChain.move:106:9+25
L426:

    // $t1084 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1084 := $IsParentMutation($t14, 4, $t15);

    // $t1085 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1085 := $IsParentMutation($t13, 2, $t14);

    // $t1086 := &&($t1084, $t1085) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1086 := $And($t1084, $t1085);

    // $t1087 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1087 := $IsParentMutation($t12, 3, $t13);

    // $t1088 := &&($t1086, $t1087) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1088 := $And($t1086, $t1087);

    // if ($t1088) goto L427 else goto L428 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1088) { goto L427; } else { goto L428; }

    // label L427 at .\sources\ConditionalBorrowChain.move:106:9+25
L427:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L428 at .\sources\ConditionalBorrowChain.move:106:9+25
L428:

    // $t1089 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1089 := $IsParentMutation($t14, 4, $t15);

    // $t1090 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1090 := $IsParentMutation($t13, 2, $t14);

    // $t1091 := &&($t1089, $t1090) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1091 := $And($t1089, $t1090);

    // $t1092 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1092 := $IsParentMutation($t12, 4, $t13);

    // $t1093 := &&($t1091, $t1092) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1093 := $And($t1091, $t1092);

    // if ($t1093) goto L429 else goto L430 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1093) { goto L429; } else { goto L430; }

    // label L429 at .\sources\ConditionalBorrowChain.move:106:9+25
L429:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L430 at .\sources\ConditionalBorrowChain.move:106:9+25
L430:

    // $t1094 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1094 := $IsParentMutation($t14, 4, $t15);

    // $t1095 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1095 := $IsParentMutation($t13, 2, $t14);

    // $t1096 := &&($t1094, $t1095) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1096 := $And($t1094, $t1095);

    // $t1097 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1097 := $IsParentMutation($t12, 5, $t13);

    // $t1098 := &&($t1096, $t1097) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1098 := $And($t1096, $t1097);

    // if ($t1098) goto L431 else goto L432 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1098) { goto L431; } else { goto L432; }

    // label L431 at .\sources\ConditionalBorrowChain.move:106:9+25
L431:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L432 at .\sources\ConditionalBorrowChain.move:106:9+25
L432:

    // $t1099 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1099 := $IsParentMutation($t14, 4, $t15);

    // $t1100 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1100 := $IsParentMutation($t13, 2, $t14);

    // $t1101 := &&($t1099, $t1100) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1101 := $And($t1099, $t1100);

    // $t1102 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1102 := $IsParentMutation($t12, 6, $t13);

    // $t1103 := &&($t1101, $t1102) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1103 := $And($t1101, $t1102);

    // if ($t1103) goto L433 else goto L434 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1103) { goto L433; } else { goto L434; }

    // label L433 at .\sources\ConditionalBorrowChain.move:106:9+25
L433:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L434 at .\sources\ConditionalBorrowChain.move:106:9+25
L434:

    // $t1104 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1104 := $IsParentMutation($t14, 4, $t15);

    // $t1105 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1105 := $IsParentMutation($t13, 3, $t14);

    // $t1106 := &&($t1104, $t1105) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1106 := $And($t1104, $t1105);

    // $t1107 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1107 := $IsParentMutation($t12, 0, $t13);

    // $t1108 := &&($t1106, $t1107) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1108 := $And($t1106, $t1107);

    // if ($t1108) goto L435 else goto L436 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1108) { goto L435; } else { goto L436; }

    // label L435 at .\sources\ConditionalBorrowChain.move:106:9+25
L435:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L436 at .\sources\ConditionalBorrowChain.move:106:9+25
L436:

    // $t1109 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1109 := $IsParentMutation($t14, 4, $t15);

    // $t1110 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1110 := $IsParentMutation($t13, 3, $t14);

    // $t1111 := &&($t1109, $t1110) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1111 := $And($t1109, $t1110);

    // $t1112 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1112 := $IsParentMutation($t12, 1, $t13);

    // $t1113 := &&($t1111, $t1112) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1113 := $And($t1111, $t1112);

    // if ($t1113) goto L437 else goto L438 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1113) { goto L437; } else { goto L438; }

    // label L437 at .\sources\ConditionalBorrowChain.move:106:9+25
L437:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L438 at .\sources\ConditionalBorrowChain.move:106:9+25
L438:

    // $t1114 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1114 := $IsParentMutation($t14, 4, $t15);

    // $t1115 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1115 := $IsParentMutation($t13, 3, $t14);

    // $t1116 := &&($t1114, $t1115) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1116 := $And($t1114, $t1115);

    // $t1117 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1117 := $IsParentMutation($t12, 2, $t13);

    // $t1118 := &&($t1116, $t1117) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1118 := $And($t1116, $t1117);

    // if ($t1118) goto L439 else goto L440 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1118) { goto L439; } else { goto L440; }

    // label L439 at .\sources\ConditionalBorrowChain.move:106:9+25
L439:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L440 at .\sources\ConditionalBorrowChain.move:106:9+25
L440:

    // $t1119 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1119 := $IsParentMutation($t14, 4, $t15);

    // $t1120 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1120 := $IsParentMutation($t13, 3, $t14);

    // $t1121 := &&($t1119, $t1120) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1121 := $And($t1119, $t1120);

    // $t1122 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1122 := $IsParentMutation($t12, 3, $t13);

    // $t1123 := &&($t1121, $t1122) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1123 := $And($t1121, $t1122);

    // if ($t1123) goto L441 else goto L442 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1123) { goto L441; } else { goto L442; }

    // label L441 at .\sources\ConditionalBorrowChain.move:106:9+25
L441:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L442 at .\sources\ConditionalBorrowChain.move:106:9+25
L442:

    // $t1124 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1124 := $IsParentMutation($t14, 4, $t15);

    // $t1125 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1125 := $IsParentMutation($t13, 3, $t14);

    // $t1126 := &&($t1124, $t1125) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1126 := $And($t1124, $t1125);

    // $t1127 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1127 := $IsParentMutation($t12, 4, $t13);

    // $t1128 := &&($t1126, $t1127) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1128 := $And($t1126, $t1127);

    // if ($t1128) goto L443 else goto L444 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1128) { goto L443; } else { goto L444; }

    // label L443 at .\sources\ConditionalBorrowChain.move:106:9+25
L443:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L444 at .\sources\ConditionalBorrowChain.move:106:9+25
L444:

    // $t1129 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1129 := $IsParentMutation($t14, 4, $t15);

    // $t1130 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1130 := $IsParentMutation($t13, 3, $t14);

    // $t1131 := &&($t1129, $t1130) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1131 := $And($t1129, $t1130);

    // $t1132 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1132 := $IsParentMutation($t12, 5, $t13);

    // $t1133 := &&($t1131, $t1132) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1133 := $And($t1131, $t1132);

    // if ($t1133) goto L445 else goto L446 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1133) { goto L445; } else { goto L446; }

    // label L445 at .\sources\ConditionalBorrowChain.move:106:9+25
L445:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L446 at .\sources\ConditionalBorrowChain.move:106:9+25
L446:

    // $t1134 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1134 := $IsParentMutation($t14, 4, $t15);

    // $t1135 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1135 := $IsParentMutation($t13, 3, $t14);

    // $t1136 := &&($t1134, $t1135) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1136 := $And($t1134, $t1135);

    // $t1137 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1137 := $IsParentMutation($t12, 6, $t13);

    // $t1138 := &&($t1136, $t1137) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1138 := $And($t1136, $t1137);

    // if ($t1138) goto L447 else goto L448 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1138) { goto L447; } else { goto L448; }

    // label L447 at .\sources\ConditionalBorrowChain.move:106:9+25
L447:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L448 at .\sources\ConditionalBorrowChain.move:106:9+25
L448:

    // $t1139 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1139 := $IsParentMutation($t14, 4, $t15);

    // $t1140 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1140 := $IsParentMutation($t13, 4, $t14);

    // $t1141 := &&($t1139, $t1140) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1141 := $And($t1139, $t1140);

    // $t1142 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1142 := $IsParentMutation($t12, 0, $t13);

    // $t1143 := &&($t1141, $t1142) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1143 := $And($t1141, $t1142);

    // if ($t1143) goto L449 else goto L450 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1143) { goto L449; } else { goto L450; }

    // label L449 at .\sources\ConditionalBorrowChain.move:106:9+25
L449:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L450 at .\sources\ConditionalBorrowChain.move:106:9+25
L450:

    // $t1144 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1144 := $IsParentMutation($t14, 4, $t15);

    // $t1145 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1145 := $IsParentMutation($t13, 4, $t14);

    // $t1146 := &&($t1144, $t1145) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1146 := $And($t1144, $t1145);

    // $t1147 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1147 := $IsParentMutation($t12, 1, $t13);

    // $t1148 := &&($t1146, $t1147) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1148 := $And($t1146, $t1147);

    // if ($t1148) goto L451 else goto L452 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1148) { goto L451; } else { goto L452; }

    // label L451 at .\sources\ConditionalBorrowChain.move:106:9+25
L451:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L452 at .\sources\ConditionalBorrowChain.move:106:9+25
L452:

    // $t1149 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1149 := $IsParentMutation($t14, 4, $t15);

    // $t1150 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1150 := $IsParentMutation($t13, 4, $t14);

    // $t1151 := &&($t1149, $t1150) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1151 := $And($t1149, $t1150);

    // $t1152 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1152 := $IsParentMutation($t12, 2, $t13);

    // $t1153 := &&($t1151, $t1152) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1153 := $And($t1151, $t1152);

    // if ($t1153) goto L453 else goto L454 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1153) { goto L453; } else { goto L454; }

    // label L453 at .\sources\ConditionalBorrowChain.move:106:9+25
L453:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L454 at .\sources\ConditionalBorrowChain.move:106:9+25
L454:

    // $t1154 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1154 := $IsParentMutation($t14, 4, $t15);

    // $t1155 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1155 := $IsParentMutation($t13, 4, $t14);

    // $t1156 := &&($t1154, $t1155) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1156 := $And($t1154, $t1155);

    // $t1157 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1157 := $IsParentMutation($t12, 3, $t13);

    // $t1158 := &&($t1156, $t1157) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1158 := $And($t1156, $t1157);

    // if ($t1158) goto L455 else goto L456 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1158) { goto L455; } else { goto L456; }

    // label L455 at .\sources\ConditionalBorrowChain.move:106:9+25
L455:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L456 at .\sources\ConditionalBorrowChain.move:106:9+25
L456:

    // $t1159 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1159 := $IsParentMutation($t14, 4, $t15);

    // $t1160 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1160 := $IsParentMutation($t13, 4, $t14);

    // $t1161 := &&($t1159, $t1160) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1161 := $And($t1159, $t1160);

    // $t1162 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1162 := $IsParentMutation($t12, 4, $t13);

    // $t1163 := &&($t1161, $t1162) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1163 := $And($t1161, $t1162);

    // if ($t1163) goto L457 else goto L458 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1163) { goto L457; } else { goto L458; }

    // label L457 at .\sources\ConditionalBorrowChain.move:106:9+25
L457:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L458 at .\sources\ConditionalBorrowChain.move:106:9+25
L458:

    // $t1164 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1164 := $IsParentMutation($t14, 4, $t15);

    // $t1165 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1165 := $IsParentMutation($t13, 4, $t14);

    // $t1166 := &&($t1164, $t1165) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1166 := $And($t1164, $t1165);

    // $t1167 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1167 := $IsParentMutation($t12, 5, $t13);

    // $t1168 := &&($t1166, $t1167) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1168 := $And($t1166, $t1167);

    // if ($t1168) goto L459 else goto L460 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1168) { goto L459; } else { goto L460; }

    // label L459 at .\sources\ConditionalBorrowChain.move:106:9+25
L459:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L460 at .\sources\ConditionalBorrowChain.move:106:9+25
L460:

    // $t1169 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1169 := $IsParentMutation($t14, 4, $t15);

    // $t1170 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1170 := $IsParentMutation($t13, 4, $t14);

    // $t1171 := &&($t1169, $t1170) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1171 := $And($t1169, $t1170);

    // $t1172 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1172 := $IsParentMutation($t12, 6, $t13);

    // $t1173 := &&($t1171, $t1172) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1173 := $And($t1171, $t1172);

    // if ($t1173) goto L461 else goto L462 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1173) { goto L461; } else { goto L462; }

    // label L461 at .\sources\ConditionalBorrowChain.move:106:9+25
L461:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L462 at .\sources\ConditionalBorrowChain.move:106:9+25
L462:

    // $t1174 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1174 := $IsParentMutation($t14, 4, $t15);

    // $t1175 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1175 := $IsParentMutation($t13, 5, $t14);

    // $t1176 := &&($t1174, $t1175) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1176 := $And($t1174, $t1175);

    // $t1177 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1177 := $IsParentMutation($t12, 0, $t13);

    // $t1178 := &&($t1176, $t1177) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1178 := $And($t1176, $t1177);

    // if ($t1178) goto L463 else goto L464 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1178) { goto L463; } else { goto L464; }

    // label L463 at .\sources\ConditionalBorrowChain.move:106:9+25
L463:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L464 at .\sources\ConditionalBorrowChain.move:106:9+25
L464:

    // $t1179 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1179 := $IsParentMutation($t14, 4, $t15);

    // $t1180 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1180 := $IsParentMutation($t13, 5, $t14);

    // $t1181 := &&($t1179, $t1180) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1181 := $And($t1179, $t1180);

    // $t1182 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1182 := $IsParentMutation($t12, 1, $t13);

    // $t1183 := &&($t1181, $t1182) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1183 := $And($t1181, $t1182);

    // if ($t1183) goto L465 else goto L466 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1183) { goto L465; } else { goto L466; }

    // label L465 at .\sources\ConditionalBorrowChain.move:106:9+25
L465:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L466 at .\sources\ConditionalBorrowChain.move:106:9+25
L466:

    // $t1184 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1184 := $IsParentMutation($t14, 4, $t15);

    // $t1185 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1185 := $IsParentMutation($t13, 5, $t14);

    // $t1186 := &&($t1184, $t1185) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1186 := $And($t1184, $t1185);

    // $t1187 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1187 := $IsParentMutation($t12, 2, $t13);

    // $t1188 := &&($t1186, $t1187) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1188 := $And($t1186, $t1187);

    // if ($t1188) goto L467 else goto L468 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1188) { goto L467; } else { goto L468; }

    // label L467 at .\sources\ConditionalBorrowChain.move:106:9+25
L467:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L468 at .\sources\ConditionalBorrowChain.move:106:9+25
L468:

    // $t1189 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1189 := $IsParentMutation($t14, 4, $t15);

    // $t1190 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1190 := $IsParentMutation($t13, 5, $t14);

    // $t1191 := &&($t1189, $t1190) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1191 := $And($t1189, $t1190);

    // $t1192 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1192 := $IsParentMutation($t12, 3, $t13);

    // $t1193 := &&($t1191, $t1192) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1193 := $And($t1191, $t1192);

    // if ($t1193) goto L469 else goto L470 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1193) { goto L469; } else { goto L470; }

    // label L469 at .\sources\ConditionalBorrowChain.move:106:9+25
L469:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L470 at .\sources\ConditionalBorrowChain.move:106:9+25
L470:

    // $t1194 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1194 := $IsParentMutation($t14, 4, $t15);

    // $t1195 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1195 := $IsParentMutation($t13, 5, $t14);

    // $t1196 := &&($t1194, $t1195) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1196 := $And($t1194, $t1195);

    // $t1197 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1197 := $IsParentMutation($t12, 4, $t13);

    // $t1198 := &&($t1196, $t1197) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1198 := $And($t1196, $t1197);

    // if ($t1198) goto L471 else goto L472 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1198) { goto L471; } else { goto L472; }

    // label L471 at .\sources\ConditionalBorrowChain.move:106:9+25
L471:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L472 at .\sources\ConditionalBorrowChain.move:106:9+25
L472:

    // $t1199 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1199 := $IsParentMutation($t14, 4, $t15);

    // $t1200 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1200 := $IsParentMutation($t13, 5, $t14);

    // $t1201 := &&($t1199, $t1200) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1201 := $And($t1199, $t1200);

    // $t1202 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1202 := $IsParentMutation($t12, 5, $t13);

    // $t1203 := &&($t1201, $t1202) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1203 := $And($t1201, $t1202);

    // if ($t1203) goto L473 else goto L474 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1203) { goto L473; } else { goto L474; }

    // label L473 at .\sources\ConditionalBorrowChain.move:106:9+25
L473:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L474 at .\sources\ConditionalBorrowChain.move:106:9+25
L474:

    // $t1204 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1204 := $IsParentMutation($t14, 4, $t15);

    // $t1205 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1205 := $IsParentMutation($t13, 5, $t14);

    // $t1206 := &&($t1204, $t1205) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1206 := $And($t1204, $t1205);

    // $t1207 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1207 := $IsParentMutation($t12, 6, $t13);

    // $t1208 := &&($t1206, $t1207) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1208 := $And($t1206, $t1207);

    // if ($t1208) goto L475 else goto L476 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1208) { goto L475; } else { goto L476; }

    // label L475 at .\sources\ConditionalBorrowChain.move:106:9+25
L475:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L476 at .\sources\ConditionalBorrowChain.move:106:9+25
L476:

    // $t1209 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1209 := $IsParentMutation($t14, 4, $t15);

    // $t1210 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1210 := $IsParentMutation($t13, 6, $t14);

    // $t1211 := &&($t1209, $t1210) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1211 := $And($t1209, $t1210);

    // $t1212 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1212 := $IsParentMutation($t12, 0, $t13);

    // $t1213 := &&($t1211, $t1212) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1213 := $And($t1211, $t1212);

    // if ($t1213) goto L477 else goto L478 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1213) { goto L477; } else { goto L478; }

    // label L477 at .\sources\ConditionalBorrowChain.move:106:9+25
L477:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L478 at .\sources\ConditionalBorrowChain.move:106:9+25
L478:

    // $t1214 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1214 := $IsParentMutation($t14, 4, $t15);

    // $t1215 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1215 := $IsParentMutation($t13, 6, $t14);

    // $t1216 := &&($t1214, $t1215) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1216 := $And($t1214, $t1215);

    // $t1217 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1217 := $IsParentMutation($t12, 1, $t13);

    // $t1218 := &&($t1216, $t1217) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1218 := $And($t1216, $t1217);

    // if ($t1218) goto L479 else goto L480 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1218) { goto L479; } else { goto L480; }

    // label L479 at .\sources\ConditionalBorrowChain.move:106:9+25
L479:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L480 at .\sources\ConditionalBorrowChain.move:106:9+25
L480:

    // $t1219 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1219 := $IsParentMutation($t14, 4, $t15);

    // $t1220 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1220 := $IsParentMutation($t13, 6, $t14);

    // $t1221 := &&($t1219, $t1220) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1221 := $And($t1219, $t1220);

    // $t1222 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1222 := $IsParentMutation($t12, 2, $t13);

    // $t1223 := &&($t1221, $t1222) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1223 := $And($t1221, $t1222);

    // if ($t1223) goto L481 else goto L482 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1223) { goto L481; } else { goto L482; }

    // label L481 at .\sources\ConditionalBorrowChain.move:106:9+25
L481:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L482 at .\sources\ConditionalBorrowChain.move:106:9+25
L482:

    // $t1224 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1224 := $IsParentMutation($t14, 4, $t15);

    // $t1225 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1225 := $IsParentMutation($t13, 6, $t14);

    // $t1226 := &&($t1224, $t1225) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1226 := $And($t1224, $t1225);

    // $t1227 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1227 := $IsParentMutation($t12, 3, $t13);

    // $t1228 := &&($t1226, $t1227) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1228 := $And($t1226, $t1227);

    // if ($t1228) goto L483 else goto L484 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1228) { goto L483; } else { goto L484; }

    // label L483 at .\sources\ConditionalBorrowChain.move:106:9+25
L483:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L484 at .\sources\ConditionalBorrowChain.move:106:9+25
L484:

    // $t1229 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1229 := $IsParentMutation($t14, 4, $t15);

    // $t1230 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1230 := $IsParentMutation($t13, 6, $t14);

    // $t1231 := &&($t1229, $t1230) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1231 := $And($t1229, $t1230);

    // $t1232 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1232 := $IsParentMutation($t12, 4, $t13);

    // $t1233 := &&($t1231, $t1232) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1233 := $And($t1231, $t1232);

    // if ($t1233) goto L485 else goto L486 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1233) { goto L485; } else { goto L486; }

    // label L485 at .\sources\ConditionalBorrowChain.move:106:9+25
L485:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L486 at .\sources\ConditionalBorrowChain.move:106:9+25
L486:

    // $t1234 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1234 := $IsParentMutation($t14, 4, $t15);

    // $t1235 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1235 := $IsParentMutation($t13, 6, $t14);

    // $t1236 := &&($t1234, $t1235) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1236 := $And($t1234, $t1235);

    // $t1237 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1237 := $IsParentMutation($t12, 5, $t13);

    // $t1238 := &&($t1236, $t1237) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1238 := $And($t1236, $t1237);

    // if ($t1238) goto L487 else goto L488 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1238) { goto L487; } else { goto L488; }

    // label L487 at .\sources\ConditionalBorrowChain.move:106:9+25
L487:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L488 at .\sources\ConditionalBorrowChain.move:106:9+25
L488:

    // $t1239 := is_parent[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1239 := $IsParentMutation($t14, 4, $t15);

    // $t1240 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1240 := $IsParentMutation($t13, 6, $t14);

    // $t1241 := &&($t1239, $t1240) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1241 := $And($t1239, $t1240);

    // $t1242 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1242 := $IsParentMutation($t12, 6, $t13);

    // $t1243 := &&($t1241, $t1242) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1243 := $And($t1241, $t1242);

    // if ($t1243) goto L489 else goto L490 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1243) { goto L489; } else { goto L490; }

    // label L489 at .\sources\ConditionalBorrowChain.move:106:9+25
L489:

    // write_back[Reference($t14).v4 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v4($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L490 at .\sources\ConditionalBorrowChain.move:106:9+25
L490:

    // $t1244 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1244 := $IsParentMutation($t14, 5, $t15);

    // $t1245 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1245 := $IsParentMutation($t13, 0, $t14);

    // $t1246 := &&($t1244, $t1245) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1246 := $And($t1244, $t1245);

    // $t1247 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1247 := $IsParentMutation($t12, 0, $t13);

    // $t1248 := &&($t1246, $t1247) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1248 := $And($t1246, $t1247);

    // if ($t1248) goto L491 else goto L492 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1248) { goto L491; } else { goto L492; }

    // label L491 at .\sources\ConditionalBorrowChain.move:106:9+25
L491:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L492 at .\sources\ConditionalBorrowChain.move:106:9+25
L492:

    // $t1249 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1249 := $IsParentMutation($t14, 5, $t15);

    // $t1250 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1250 := $IsParentMutation($t13, 0, $t14);

    // $t1251 := &&($t1249, $t1250) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1251 := $And($t1249, $t1250);

    // $t1252 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1252 := $IsParentMutation($t12, 1, $t13);

    // $t1253 := &&($t1251, $t1252) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1253 := $And($t1251, $t1252);

    // if ($t1253) goto L493 else goto L494 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1253) { goto L493; } else { goto L494; }

    // label L493 at .\sources\ConditionalBorrowChain.move:106:9+25
L493:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L494 at .\sources\ConditionalBorrowChain.move:106:9+25
L494:

    // $t1254 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1254 := $IsParentMutation($t14, 5, $t15);

    // $t1255 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1255 := $IsParentMutation($t13, 0, $t14);

    // $t1256 := &&($t1254, $t1255) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1256 := $And($t1254, $t1255);

    // $t1257 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1257 := $IsParentMutation($t12, 2, $t13);

    // $t1258 := &&($t1256, $t1257) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1258 := $And($t1256, $t1257);

    // if ($t1258) goto L495 else goto L496 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1258) { goto L495; } else { goto L496; }

    // label L495 at .\sources\ConditionalBorrowChain.move:106:9+25
L495:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L496 at .\sources\ConditionalBorrowChain.move:106:9+25
L496:

    // $t1259 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1259 := $IsParentMutation($t14, 5, $t15);

    // $t1260 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1260 := $IsParentMutation($t13, 0, $t14);

    // $t1261 := &&($t1259, $t1260) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1261 := $And($t1259, $t1260);

    // $t1262 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1262 := $IsParentMutation($t12, 3, $t13);

    // $t1263 := &&($t1261, $t1262) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1263 := $And($t1261, $t1262);

    // if ($t1263) goto L497 else goto L498 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1263) { goto L497; } else { goto L498; }

    // label L497 at .\sources\ConditionalBorrowChain.move:106:9+25
L497:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L498 at .\sources\ConditionalBorrowChain.move:106:9+25
L498:

    // $t1264 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1264 := $IsParentMutation($t14, 5, $t15);

    // $t1265 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1265 := $IsParentMutation($t13, 0, $t14);

    // $t1266 := &&($t1264, $t1265) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1266 := $And($t1264, $t1265);

    // $t1267 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1267 := $IsParentMutation($t12, 4, $t13);

    // $t1268 := &&($t1266, $t1267) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1268 := $And($t1266, $t1267);

    // if ($t1268) goto L499 else goto L500 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1268) { goto L499; } else { goto L500; }

    // label L499 at .\sources\ConditionalBorrowChain.move:106:9+25
L499:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L500 at .\sources\ConditionalBorrowChain.move:106:9+25
L500:

    // $t1269 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1269 := $IsParentMutation($t14, 5, $t15);

    // $t1270 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1270 := $IsParentMutation($t13, 0, $t14);

    // $t1271 := &&($t1269, $t1270) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1271 := $And($t1269, $t1270);

    // $t1272 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1272 := $IsParentMutation($t12, 5, $t13);

    // $t1273 := &&($t1271, $t1272) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1273 := $And($t1271, $t1272);

    // if ($t1273) goto L501 else goto L502 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1273) { goto L501; } else { goto L502; }

    // label L501 at .\sources\ConditionalBorrowChain.move:106:9+25
L501:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L502 at .\sources\ConditionalBorrowChain.move:106:9+25
L502:

    // $t1274 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1274 := $IsParentMutation($t14, 5, $t15);

    // $t1275 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1275 := $IsParentMutation($t13, 0, $t14);

    // $t1276 := &&($t1274, $t1275) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1276 := $And($t1274, $t1275);

    // $t1277 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1277 := $IsParentMutation($t12, 6, $t13);

    // $t1278 := &&($t1276, $t1277) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1278 := $And($t1276, $t1277);

    // if ($t1278) goto L503 else goto L504 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1278) { goto L503; } else { goto L504; }

    // label L503 at .\sources\ConditionalBorrowChain.move:106:9+25
L503:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L504 at .\sources\ConditionalBorrowChain.move:106:9+25
L504:

    // $t1279 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1279 := $IsParentMutation($t14, 5, $t15);

    // $t1280 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1280 := $IsParentMutation($t13, 1, $t14);

    // $t1281 := &&($t1279, $t1280) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1281 := $And($t1279, $t1280);

    // $t1282 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1282 := $IsParentMutation($t12, 0, $t13);

    // $t1283 := &&($t1281, $t1282) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1283 := $And($t1281, $t1282);

    // if ($t1283) goto L505 else goto L506 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1283) { goto L505; } else { goto L506; }

    // label L505 at .\sources\ConditionalBorrowChain.move:106:9+25
L505:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L506 at .\sources\ConditionalBorrowChain.move:106:9+25
L506:

    // $t1284 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1284 := $IsParentMutation($t14, 5, $t15);

    // $t1285 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1285 := $IsParentMutation($t13, 1, $t14);

    // $t1286 := &&($t1284, $t1285) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1286 := $And($t1284, $t1285);

    // $t1287 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1287 := $IsParentMutation($t12, 1, $t13);

    // $t1288 := &&($t1286, $t1287) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1288 := $And($t1286, $t1287);

    // if ($t1288) goto L507 else goto L508 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1288) { goto L507; } else { goto L508; }

    // label L507 at .\sources\ConditionalBorrowChain.move:106:9+25
L507:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L508 at .\sources\ConditionalBorrowChain.move:106:9+25
L508:

    // $t1289 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1289 := $IsParentMutation($t14, 5, $t15);

    // $t1290 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1290 := $IsParentMutation($t13, 1, $t14);

    // $t1291 := &&($t1289, $t1290) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1291 := $And($t1289, $t1290);

    // $t1292 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1292 := $IsParentMutation($t12, 2, $t13);

    // $t1293 := &&($t1291, $t1292) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1293 := $And($t1291, $t1292);

    // if ($t1293) goto L509 else goto L510 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1293) { goto L509; } else { goto L510; }

    // label L509 at .\sources\ConditionalBorrowChain.move:106:9+25
L509:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L510 at .\sources\ConditionalBorrowChain.move:106:9+25
L510:

    // $t1294 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1294 := $IsParentMutation($t14, 5, $t15);

    // $t1295 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1295 := $IsParentMutation($t13, 1, $t14);

    // $t1296 := &&($t1294, $t1295) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1296 := $And($t1294, $t1295);

    // $t1297 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1297 := $IsParentMutation($t12, 3, $t13);

    // $t1298 := &&($t1296, $t1297) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1298 := $And($t1296, $t1297);

    // if ($t1298) goto L511 else goto L512 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1298) { goto L511; } else { goto L512; }

    // label L511 at .\sources\ConditionalBorrowChain.move:106:9+25
L511:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L512 at .\sources\ConditionalBorrowChain.move:106:9+25
L512:

    // $t1299 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1299 := $IsParentMutation($t14, 5, $t15);

    // $t1300 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1300 := $IsParentMutation($t13, 1, $t14);

    // $t1301 := &&($t1299, $t1300) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1301 := $And($t1299, $t1300);

    // $t1302 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1302 := $IsParentMutation($t12, 4, $t13);

    // $t1303 := &&($t1301, $t1302) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1303 := $And($t1301, $t1302);

    // if ($t1303) goto L513 else goto L514 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1303) { goto L513; } else { goto L514; }

    // label L513 at .\sources\ConditionalBorrowChain.move:106:9+25
L513:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L514 at .\sources\ConditionalBorrowChain.move:106:9+25
L514:

    // $t1304 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1304 := $IsParentMutation($t14, 5, $t15);

    // $t1305 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1305 := $IsParentMutation($t13, 1, $t14);

    // $t1306 := &&($t1304, $t1305) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1306 := $And($t1304, $t1305);

    // $t1307 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1307 := $IsParentMutation($t12, 5, $t13);

    // $t1308 := &&($t1306, $t1307) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1308 := $And($t1306, $t1307);

    // if ($t1308) goto L515 else goto L516 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1308) { goto L515; } else { goto L516; }

    // label L515 at .\sources\ConditionalBorrowChain.move:106:9+25
L515:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L516 at .\sources\ConditionalBorrowChain.move:106:9+25
L516:

    // $t1309 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1309 := $IsParentMutation($t14, 5, $t15);

    // $t1310 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1310 := $IsParentMutation($t13, 1, $t14);

    // $t1311 := &&($t1309, $t1310) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1311 := $And($t1309, $t1310);

    // $t1312 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1312 := $IsParentMutation($t12, 6, $t13);

    // $t1313 := &&($t1311, $t1312) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1313 := $And($t1311, $t1312);

    // if ($t1313) goto L517 else goto L518 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1313) { goto L517; } else { goto L518; }

    // label L517 at .\sources\ConditionalBorrowChain.move:106:9+25
L517:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L518 at .\sources\ConditionalBorrowChain.move:106:9+25
L518:

    // $t1314 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1314 := $IsParentMutation($t14, 5, $t15);

    // $t1315 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1315 := $IsParentMutation($t13, 2, $t14);

    // $t1316 := &&($t1314, $t1315) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1316 := $And($t1314, $t1315);

    // $t1317 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1317 := $IsParentMutation($t12, 0, $t13);

    // $t1318 := &&($t1316, $t1317) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1318 := $And($t1316, $t1317);

    // if ($t1318) goto L519 else goto L520 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1318) { goto L519; } else { goto L520; }

    // label L519 at .\sources\ConditionalBorrowChain.move:106:9+25
L519:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L520 at .\sources\ConditionalBorrowChain.move:106:9+25
L520:

    // $t1319 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1319 := $IsParentMutation($t14, 5, $t15);

    // $t1320 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1320 := $IsParentMutation($t13, 2, $t14);

    // $t1321 := &&($t1319, $t1320) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1321 := $And($t1319, $t1320);

    // $t1322 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1322 := $IsParentMutation($t12, 1, $t13);

    // $t1323 := &&($t1321, $t1322) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1323 := $And($t1321, $t1322);

    // if ($t1323) goto L521 else goto L522 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1323) { goto L521; } else { goto L522; }

    // label L521 at .\sources\ConditionalBorrowChain.move:106:9+25
L521:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L522 at .\sources\ConditionalBorrowChain.move:106:9+25
L522:

    // $t1324 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1324 := $IsParentMutation($t14, 5, $t15);

    // $t1325 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1325 := $IsParentMutation($t13, 2, $t14);

    // $t1326 := &&($t1324, $t1325) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1326 := $And($t1324, $t1325);

    // $t1327 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1327 := $IsParentMutation($t12, 2, $t13);

    // $t1328 := &&($t1326, $t1327) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1328 := $And($t1326, $t1327);

    // if ($t1328) goto L523 else goto L524 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1328) { goto L523; } else { goto L524; }

    // label L523 at .\sources\ConditionalBorrowChain.move:106:9+25
L523:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L524 at .\sources\ConditionalBorrowChain.move:106:9+25
L524:

    // $t1329 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1329 := $IsParentMutation($t14, 5, $t15);

    // $t1330 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1330 := $IsParentMutation($t13, 2, $t14);

    // $t1331 := &&($t1329, $t1330) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1331 := $And($t1329, $t1330);

    // $t1332 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1332 := $IsParentMutation($t12, 3, $t13);

    // $t1333 := &&($t1331, $t1332) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1333 := $And($t1331, $t1332);

    // if ($t1333) goto L525 else goto L526 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1333) { goto L525; } else { goto L526; }

    // label L525 at .\sources\ConditionalBorrowChain.move:106:9+25
L525:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L526 at .\sources\ConditionalBorrowChain.move:106:9+25
L526:

    // $t1334 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1334 := $IsParentMutation($t14, 5, $t15);

    // $t1335 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1335 := $IsParentMutation($t13, 2, $t14);

    // $t1336 := &&($t1334, $t1335) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1336 := $And($t1334, $t1335);

    // $t1337 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1337 := $IsParentMutation($t12, 4, $t13);

    // $t1338 := &&($t1336, $t1337) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1338 := $And($t1336, $t1337);

    // if ($t1338) goto L527 else goto L528 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1338) { goto L527; } else { goto L528; }

    // label L527 at .\sources\ConditionalBorrowChain.move:106:9+25
L527:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L528 at .\sources\ConditionalBorrowChain.move:106:9+25
L528:

    // $t1339 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1339 := $IsParentMutation($t14, 5, $t15);

    // $t1340 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1340 := $IsParentMutation($t13, 2, $t14);

    // $t1341 := &&($t1339, $t1340) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1341 := $And($t1339, $t1340);

    // $t1342 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1342 := $IsParentMutation($t12, 5, $t13);

    // $t1343 := &&($t1341, $t1342) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1343 := $And($t1341, $t1342);

    // if ($t1343) goto L529 else goto L530 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1343) { goto L529; } else { goto L530; }

    // label L529 at .\sources\ConditionalBorrowChain.move:106:9+25
L529:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L530 at .\sources\ConditionalBorrowChain.move:106:9+25
L530:

    // $t1344 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1344 := $IsParentMutation($t14, 5, $t15);

    // $t1345 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1345 := $IsParentMutation($t13, 2, $t14);

    // $t1346 := &&($t1344, $t1345) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1346 := $And($t1344, $t1345);

    // $t1347 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1347 := $IsParentMutation($t12, 6, $t13);

    // $t1348 := &&($t1346, $t1347) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1348 := $And($t1346, $t1347);

    // if ($t1348) goto L531 else goto L532 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1348) { goto L531; } else { goto L532; }

    // label L531 at .\sources\ConditionalBorrowChain.move:106:9+25
L531:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L532 at .\sources\ConditionalBorrowChain.move:106:9+25
L532:

    // $t1349 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1349 := $IsParentMutation($t14, 5, $t15);

    // $t1350 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1350 := $IsParentMutation($t13, 3, $t14);

    // $t1351 := &&($t1349, $t1350) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1351 := $And($t1349, $t1350);

    // $t1352 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1352 := $IsParentMutation($t12, 0, $t13);

    // $t1353 := &&($t1351, $t1352) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1353 := $And($t1351, $t1352);

    // if ($t1353) goto L533 else goto L534 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1353) { goto L533; } else { goto L534; }

    // label L533 at .\sources\ConditionalBorrowChain.move:106:9+25
L533:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L534 at .\sources\ConditionalBorrowChain.move:106:9+25
L534:

    // $t1354 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1354 := $IsParentMutation($t14, 5, $t15);

    // $t1355 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1355 := $IsParentMutation($t13, 3, $t14);

    // $t1356 := &&($t1354, $t1355) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1356 := $And($t1354, $t1355);

    // $t1357 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1357 := $IsParentMutation($t12, 1, $t13);

    // $t1358 := &&($t1356, $t1357) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1358 := $And($t1356, $t1357);

    // if ($t1358) goto L535 else goto L536 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1358) { goto L535; } else { goto L536; }

    // label L535 at .\sources\ConditionalBorrowChain.move:106:9+25
L535:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L536 at .\sources\ConditionalBorrowChain.move:106:9+25
L536:

    // $t1359 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1359 := $IsParentMutation($t14, 5, $t15);

    // $t1360 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1360 := $IsParentMutation($t13, 3, $t14);

    // $t1361 := &&($t1359, $t1360) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1361 := $And($t1359, $t1360);

    // $t1362 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1362 := $IsParentMutation($t12, 2, $t13);

    // $t1363 := &&($t1361, $t1362) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1363 := $And($t1361, $t1362);

    // if ($t1363) goto L537 else goto L538 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1363) { goto L537; } else { goto L538; }

    // label L537 at .\sources\ConditionalBorrowChain.move:106:9+25
L537:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L538 at .\sources\ConditionalBorrowChain.move:106:9+25
L538:

    // $t1364 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1364 := $IsParentMutation($t14, 5, $t15);

    // $t1365 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1365 := $IsParentMutation($t13, 3, $t14);

    // $t1366 := &&($t1364, $t1365) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1366 := $And($t1364, $t1365);

    // $t1367 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1367 := $IsParentMutation($t12, 3, $t13);

    // $t1368 := &&($t1366, $t1367) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1368 := $And($t1366, $t1367);

    // if ($t1368) goto L539 else goto L540 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1368) { goto L539; } else { goto L540; }

    // label L539 at .\sources\ConditionalBorrowChain.move:106:9+25
L539:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L540 at .\sources\ConditionalBorrowChain.move:106:9+25
L540:

    // $t1369 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1369 := $IsParentMutation($t14, 5, $t15);

    // $t1370 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1370 := $IsParentMutation($t13, 3, $t14);

    // $t1371 := &&($t1369, $t1370) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1371 := $And($t1369, $t1370);

    // $t1372 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1372 := $IsParentMutation($t12, 4, $t13);

    // $t1373 := &&($t1371, $t1372) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1373 := $And($t1371, $t1372);

    // if ($t1373) goto L541 else goto L542 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1373) { goto L541; } else { goto L542; }

    // label L541 at .\sources\ConditionalBorrowChain.move:106:9+25
L541:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L542 at .\sources\ConditionalBorrowChain.move:106:9+25
L542:

    // $t1374 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1374 := $IsParentMutation($t14, 5, $t15);

    // $t1375 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1375 := $IsParentMutation($t13, 3, $t14);

    // $t1376 := &&($t1374, $t1375) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1376 := $And($t1374, $t1375);

    // $t1377 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1377 := $IsParentMutation($t12, 5, $t13);

    // $t1378 := &&($t1376, $t1377) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1378 := $And($t1376, $t1377);

    // if ($t1378) goto L543 else goto L544 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1378) { goto L543; } else { goto L544; }

    // label L543 at .\sources\ConditionalBorrowChain.move:106:9+25
L543:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L544 at .\sources\ConditionalBorrowChain.move:106:9+25
L544:

    // $t1379 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1379 := $IsParentMutation($t14, 5, $t15);

    // $t1380 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1380 := $IsParentMutation($t13, 3, $t14);

    // $t1381 := &&($t1379, $t1380) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1381 := $And($t1379, $t1380);

    // $t1382 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1382 := $IsParentMutation($t12, 6, $t13);

    // $t1383 := &&($t1381, $t1382) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1383 := $And($t1381, $t1382);

    // if ($t1383) goto L545 else goto L546 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1383) { goto L545; } else { goto L546; }

    // label L545 at .\sources\ConditionalBorrowChain.move:106:9+25
L545:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L546 at .\sources\ConditionalBorrowChain.move:106:9+25
L546:

    // $t1384 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1384 := $IsParentMutation($t14, 5, $t15);

    // $t1385 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1385 := $IsParentMutation($t13, 4, $t14);

    // $t1386 := &&($t1384, $t1385) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1386 := $And($t1384, $t1385);

    // $t1387 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1387 := $IsParentMutation($t12, 0, $t13);

    // $t1388 := &&($t1386, $t1387) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1388 := $And($t1386, $t1387);

    // if ($t1388) goto L547 else goto L548 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1388) { goto L547; } else { goto L548; }

    // label L547 at .\sources\ConditionalBorrowChain.move:106:9+25
L547:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L548 at .\sources\ConditionalBorrowChain.move:106:9+25
L548:

    // $t1389 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1389 := $IsParentMutation($t14, 5, $t15);

    // $t1390 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1390 := $IsParentMutation($t13, 4, $t14);

    // $t1391 := &&($t1389, $t1390) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1391 := $And($t1389, $t1390);

    // $t1392 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1392 := $IsParentMutation($t12, 1, $t13);

    // $t1393 := &&($t1391, $t1392) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1393 := $And($t1391, $t1392);

    // if ($t1393) goto L549 else goto L550 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1393) { goto L549; } else { goto L550; }

    // label L549 at .\sources\ConditionalBorrowChain.move:106:9+25
L549:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L550 at .\sources\ConditionalBorrowChain.move:106:9+25
L550:

    // $t1394 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1394 := $IsParentMutation($t14, 5, $t15);

    // $t1395 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1395 := $IsParentMutation($t13, 4, $t14);

    // $t1396 := &&($t1394, $t1395) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1396 := $And($t1394, $t1395);

    // $t1397 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1397 := $IsParentMutation($t12, 2, $t13);

    // $t1398 := &&($t1396, $t1397) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1398 := $And($t1396, $t1397);

    // if ($t1398) goto L551 else goto L552 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1398) { goto L551; } else { goto L552; }

    // label L551 at .\sources\ConditionalBorrowChain.move:106:9+25
L551:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L552 at .\sources\ConditionalBorrowChain.move:106:9+25
L552:

    // $t1399 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1399 := $IsParentMutation($t14, 5, $t15);

    // $t1400 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1400 := $IsParentMutation($t13, 4, $t14);

    // $t1401 := &&($t1399, $t1400) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1401 := $And($t1399, $t1400);

    // $t1402 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1402 := $IsParentMutation($t12, 3, $t13);

    // $t1403 := &&($t1401, $t1402) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1403 := $And($t1401, $t1402);

    // if ($t1403) goto L553 else goto L554 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1403) { goto L553; } else { goto L554; }

    // label L553 at .\sources\ConditionalBorrowChain.move:106:9+25
L553:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L554 at .\sources\ConditionalBorrowChain.move:106:9+25
L554:

    // $t1404 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1404 := $IsParentMutation($t14, 5, $t15);

    // $t1405 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1405 := $IsParentMutation($t13, 4, $t14);

    // $t1406 := &&($t1404, $t1405) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1406 := $And($t1404, $t1405);

    // $t1407 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1407 := $IsParentMutation($t12, 4, $t13);

    // $t1408 := &&($t1406, $t1407) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1408 := $And($t1406, $t1407);

    // if ($t1408) goto L555 else goto L556 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1408) { goto L555; } else { goto L556; }

    // label L555 at .\sources\ConditionalBorrowChain.move:106:9+25
L555:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L556 at .\sources\ConditionalBorrowChain.move:106:9+25
L556:

    // $t1409 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1409 := $IsParentMutation($t14, 5, $t15);

    // $t1410 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1410 := $IsParentMutation($t13, 4, $t14);

    // $t1411 := &&($t1409, $t1410) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1411 := $And($t1409, $t1410);

    // $t1412 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1412 := $IsParentMutation($t12, 5, $t13);

    // $t1413 := &&($t1411, $t1412) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1413 := $And($t1411, $t1412);

    // if ($t1413) goto L557 else goto L558 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1413) { goto L557; } else { goto L558; }

    // label L557 at .\sources\ConditionalBorrowChain.move:106:9+25
L557:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L558 at .\sources\ConditionalBorrowChain.move:106:9+25
L558:

    // $t1414 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1414 := $IsParentMutation($t14, 5, $t15);

    // $t1415 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1415 := $IsParentMutation($t13, 4, $t14);

    // $t1416 := &&($t1414, $t1415) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1416 := $And($t1414, $t1415);

    // $t1417 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1417 := $IsParentMutation($t12, 6, $t13);

    // $t1418 := &&($t1416, $t1417) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1418 := $And($t1416, $t1417);

    // if ($t1418) goto L559 else goto L560 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1418) { goto L559; } else { goto L560; }

    // label L559 at .\sources\ConditionalBorrowChain.move:106:9+25
L559:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L560 at .\sources\ConditionalBorrowChain.move:106:9+25
L560:

    // $t1419 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1419 := $IsParentMutation($t14, 5, $t15);

    // $t1420 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1420 := $IsParentMutation($t13, 5, $t14);

    // $t1421 := &&($t1419, $t1420) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1421 := $And($t1419, $t1420);

    // $t1422 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1422 := $IsParentMutation($t12, 0, $t13);

    // $t1423 := &&($t1421, $t1422) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1423 := $And($t1421, $t1422);

    // if ($t1423) goto L561 else goto L562 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1423) { goto L561; } else { goto L562; }

    // label L561 at .\sources\ConditionalBorrowChain.move:106:9+25
L561:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L562 at .\sources\ConditionalBorrowChain.move:106:9+25
L562:

    // $t1424 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1424 := $IsParentMutation($t14, 5, $t15);

    // $t1425 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1425 := $IsParentMutation($t13, 5, $t14);

    // $t1426 := &&($t1424, $t1425) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1426 := $And($t1424, $t1425);

    // $t1427 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1427 := $IsParentMutation($t12, 1, $t13);

    // $t1428 := &&($t1426, $t1427) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1428 := $And($t1426, $t1427);

    // if ($t1428) goto L563 else goto L564 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1428) { goto L563; } else { goto L564; }

    // label L563 at .\sources\ConditionalBorrowChain.move:106:9+25
L563:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L564 at .\sources\ConditionalBorrowChain.move:106:9+25
L564:

    // $t1429 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1429 := $IsParentMutation($t14, 5, $t15);

    // $t1430 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1430 := $IsParentMutation($t13, 5, $t14);

    // $t1431 := &&($t1429, $t1430) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1431 := $And($t1429, $t1430);

    // $t1432 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1432 := $IsParentMutation($t12, 2, $t13);

    // $t1433 := &&($t1431, $t1432) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1433 := $And($t1431, $t1432);

    // if ($t1433) goto L565 else goto L566 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1433) { goto L565; } else { goto L566; }

    // label L565 at .\sources\ConditionalBorrowChain.move:106:9+25
L565:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L566 at .\sources\ConditionalBorrowChain.move:106:9+25
L566:

    // $t1434 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1434 := $IsParentMutation($t14, 5, $t15);

    // $t1435 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1435 := $IsParentMutation($t13, 5, $t14);

    // $t1436 := &&($t1434, $t1435) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1436 := $And($t1434, $t1435);

    // $t1437 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1437 := $IsParentMutation($t12, 3, $t13);

    // $t1438 := &&($t1436, $t1437) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1438 := $And($t1436, $t1437);

    // if ($t1438) goto L567 else goto L568 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1438) { goto L567; } else { goto L568; }

    // label L567 at .\sources\ConditionalBorrowChain.move:106:9+25
L567:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L568 at .\sources\ConditionalBorrowChain.move:106:9+25
L568:

    // $t1439 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1439 := $IsParentMutation($t14, 5, $t15);

    // $t1440 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1440 := $IsParentMutation($t13, 5, $t14);

    // $t1441 := &&($t1439, $t1440) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1441 := $And($t1439, $t1440);

    // $t1442 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1442 := $IsParentMutation($t12, 4, $t13);

    // $t1443 := &&($t1441, $t1442) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1443 := $And($t1441, $t1442);

    // if ($t1443) goto L569 else goto L570 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1443) { goto L569; } else { goto L570; }

    // label L569 at .\sources\ConditionalBorrowChain.move:106:9+25
L569:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L570 at .\sources\ConditionalBorrowChain.move:106:9+25
L570:

    // $t1444 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1444 := $IsParentMutation($t14, 5, $t15);

    // $t1445 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1445 := $IsParentMutation($t13, 5, $t14);

    // $t1446 := &&($t1444, $t1445) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1446 := $And($t1444, $t1445);

    // $t1447 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1447 := $IsParentMutation($t12, 5, $t13);

    // $t1448 := &&($t1446, $t1447) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1448 := $And($t1446, $t1447);

    // if ($t1448) goto L571 else goto L572 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1448) { goto L571; } else { goto L572; }

    // label L571 at .\sources\ConditionalBorrowChain.move:106:9+25
L571:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L572 at .\sources\ConditionalBorrowChain.move:106:9+25
L572:

    // $t1449 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1449 := $IsParentMutation($t14, 5, $t15);

    // $t1450 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1450 := $IsParentMutation($t13, 5, $t14);

    // $t1451 := &&($t1449, $t1450) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1451 := $And($t1449, $t1450);

    // $t1452 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1452 := $IsParentMutation($t12, 6, $t13);

    // $t1453 := &&($t1451, $t1452) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1453 := $And($t1451, $t1452);

    // if ($t1453) goto L573 else goto L574 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1453) { goto L573; } else { goto L574; }

    // label L573 at .\sources\ConditionalBorrowChain.move:106:9+25
L573:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L574 at .\sources\ConditionalBorrowChain.move:106:9+25
L574:

    // $t1454 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1454 := $IsParentMutation($t14, 5, $t15);

    // $t1455 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1455 := $IsParentMutation($t13, 6, $t14);

    // $t1456 := &&($t1454, $t1455) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1456 := $And($t1454, $t1455);

    // $t1457 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1457 := $IsParentMutation($t12, 0, $t13);

    // $t1458 := &&($t1456, $t1457) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1458 := $And($t1456, $t1457);

    // if ($t1458) goto L575 else goto L576 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1458) { goto L575; } else { goto L576; }

    // label L575 at .\sources\ConditionalBorrowChain.move:106:9+25
L575:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L576 at .\sources\ConditionalBorrowChain.move:106:9+25
L576:

    // $t1459 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1459 := $IsParentMutation($t14, 5, $t15);

    // $t1460 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1460 := $IsParentMutation($t13, 6, $t14);

    // $t1461 := &&($t1459, $t1460) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1461 := $And($t1459, $t1460);

    // $t1462 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1462 := $IsParentMutation($t12, 1, $t13);

    // $t1463 := &&($t1461, $t1462) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1463 := $And($t1461, $t1462);

    // if ($t1463) goto L577 else goto L578 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1463) { goto L577; } else { goto L578; }

    // label L577 at .\sources\ConditionalBorrowChain.move:106:9+25
L577:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L578 at .\sources\ConditionalBorrowChain.move:106:9+25
L578:

    // $t1464 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1464 := $IsParentMutation($t14, 5, $t15);

    // $t1465 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1465 := $IsParentMutation($t13, 6, $t14);

    // $t1466 := &&($t1464, $t1465) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1466 := $And($t1464, $t1465);

    // $t1467 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1467 := $IsParentMutation($t12, 2, $t13);

    // $t1468 := &&($t1466, $t1467) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1468 := $And($t1466, $t1467);

    // if ($t1468) goto L579 else goto L580 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1468) { goto L579; } else { goto L580; }

    // label L579 at .\sources\ConditionalBorrowChain.move:106:9+25
L579:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L580 at .\sources\ConditionalBorrowChain.move:106:9+25
L580:

    // $t1469 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1469 := $IsParentMutation($t14, 5, $t15);

    // $t1470 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1470 := $IsParentMutation($t13, 6, $t14);

    // $t1471 := &&($t1469, $t1470) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1471 := $And($t1469, $t1470);

    // $t1472 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1472 := $IsParentMutation($t12, 3, $t13);

    // $t1473 := &&($t1471, $t1472) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1473 := $And($t1471, $t1472);

    // if ($t1473) goto L581 else goto L582 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1473) { goto L581; } else { goto L582; }

    // label L581 at .\sources\ConditionalBorrowChain.move:106:9+25
L581:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L582 at .\sources\ConditionalBorrowChain.move:106:9+25
L582:

    // $t1474 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1474 := $IsParentMutation($t14, 5, $t15);

    // $t1475 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1475 := $IsParentMutation($t13, 6, $t14);

    // $t1476 := &&($t1474, $t1475) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1476 := $And($t1474, $t1475);

    // $t1477 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1477 := $IsParentMutation($t12, 4, $t13);

    // $t1478 := &&($t1476, $t1477) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1478 := $And($t1476, $t1477);

    // if ($t1478) goto L583 else goto L584 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1478) { goto L583; } else { goto L584; }

    // label L583 at .\sources\ConditionalBorrowChain.move:106:9+25
L583:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L584 at .\sources\ConditionalBorrowChain.move:106:9+25
L584:

    // $t1479 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1479 := $IsParentMutation($t14, 5, $t15);

    // $t1480 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1480 := $IsParentMutation($t13, 6, $t14);

    // $t1481 := &&($t1479, $t1480) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1481 := $And($t1479, $t1480);

    // $t1482 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1482 := $IsParentMutation($t12, 5, $t13);

    // $t1483 := &&($t1481, $t1482) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1483 := $And($t1481, $t1482);

    // if ($t1483) goto L585 else goto L586 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1483) { goto L585; } else { goto L586; }

    // label L585 at .\sources\ConditionalBorrowChain.move:106:9+25
L585:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L586 at .\sources\ConditionalBorrowChain.move:106:9+25
L586:

    // $t1484 := is_parent[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1484 := $IsParentMutation($t14, 5, $t15);

    // $t1485 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1485 := $IsParentMutation($t13, 6, $t14);

    // $t1486 := &&($t1484, $t1485) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1486 := $And($t1484, $t1485);

    // $t1487 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1487 := $IsParentMutation($t12, 6, $t13);

    // $t1488 := &&($t1486, $t1487) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1488 := $And($t1486, $t1487);

    // if ($t1488) goto L587 else goto L588 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1488) { goto L587; } else { goto L588; }

    // label L587 at .\sources\ConditionalBorrowChain.move:106:9+25
L587:

    // write_back[Reference($t14).v5 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v5($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L588 at .\sources\ConditionalBorrowChain.move:106:9+25
L588:

    // $t1489 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1489 := $IsParentMutation($t14, 6, $t15);

    // $t1490 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1490 := $IsParentMutation($t13, 0, $t14);

    // $t1491 := &&($t1489, $t1490) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1491 := $And($t1489, $t1490);

    // $t1492 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1492 := $IsParentMutation($t12, 0, $t13);

    // $t1493 := &&($t1491, $t1492) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1493 := $And($t1491, $t1492);

    // if ($t1493) goto L589 else goto L590 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1493) { goto L589; } else { goto L590; }

    // label L589 at .\sources\ConditionalBorrowChain.move:106:9+25
L589:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L590 at .\sources\ConditionalBorrowChain.move:106:9+25
L590:

    // $t1494 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1494 := $IsParentMutation($t14, 6, $t15);

    // $t1495 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1495 := $IsParentMutation($t13, 0, $t14);

    // $t1496 := &&($t1494, $t1495) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1496 := $And($t1494, $t1495);

    // $t1497 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1497 := $IsParentMutation($t12, 1, $t13);

    // $t1498 := &&($t1496, $t1497) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1498 := $And($t1496, $t1497);

    // if ($t1498) goto L591 else goto L592 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1498) { goto L591; } else { goto L592; }

    // label L591 at .\sources\ConditionalBorrowChain.move:106:9+25
L591:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L592 at .\sources\ConditionalBorrowChain.move:106:9+25
L592:

    // $t1499 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1499 := $IsParentMutation($t14, 6, $t15);

    // $t1500 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1500 := $IsParentMutation($t13, 0, $t14);

    // $t1501 := &&($t1499, $t1500) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1501 := $And($t1499, $t1500);

    // $t1502 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1502 := $IsParentMutation($t12, 2, $t13);

    // $t1503 := &&($t1501, $t1502) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1503 := $And($t1501, $t1502);

    // if ($t1503) goto L593 else goto L594 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1503) { goto L593; } else { goto L594; }

    // label L593 at .\sources\ConditionalBorrowChain.move:106:9+25
L593:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L594 at .\sources\ConditionalBorrowChain.move:106:9+25
L594:

    // $t1504 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1504 := $IsParentMutation($t14, 6, $t15);

    // $t1505 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1505 := $IsParentMutation($t13, 0, $t14);

    // $t1506 := &&($t1504, $t1505) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1506 := $And($t1504, $t1505);

    // $t1507 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1507 := $IsParentMutation($t12, 3, $t13);

    // $t1508 := &&($t1506, $t1507) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1508 := $And($t1506, $t1507);

    // if ($t1508) goto L595 else goto L596 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1508) { goto L595; } else { goto L596; }

    // label L595 at .\sources\ConditionalBorrowChain.move:106:9+25
L595:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L596 at .\sources\ConditionalBorrowChain.move:106:9+25
L596:

    // $t1509 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1509 := $IsParentMutation($t14, 6, $t15);

    // $t1510 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1510 := $IsParentMutation($t13, 0, $t14);

    // $t1511 := &&($t1509, $t1510) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1511 := $And($t1509, $t1510);

    // $t1512 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1512 := $IsParentMutation($t12, 4, $t13);

    // $t1513 := &&($t1511, $t1512) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1513 := $And($t1511, $t1512);

    // if ($t1513) goto L597 else goto L598 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1513) { goto L597; } else { goto L598; }

    // label L597 at .\sources\ConditionalBorrowChain.move:106:9+25
L597:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L598 at .\sources\ConditionalBorrowChain.move:106:9+25
L598:

    // $t1514 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1514 := $IsParentMutation($t14, 6, $t15);

    // $t1515 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1515 := $IsParentMutation($t13, 0, $t14);

    // $t1516 := &&($t1514, $t1515) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1516 := $And($t1514, $t1515);

    // $t1517 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1517 := $IsParentMutation($t12, 5, $t13);

    // $t1518 := &&($t1516, $t1517) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1518 := $And($t1516, $t1517);

    // if ($t1518) goto L599 else goto L600 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1518) { goto L599; } else { goto L600; }

    // label L599 at .\sources\ConditionalBorrowChain.move:106:9+25
L599:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L600 at .\sources\ConditionalBorrowChain.move:106:9+25
L600:

    // $t1519 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1519 := $IsParentMutation($t14, 6, $t15);

    // $t1520 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1520 := $IsParentMutation($t13, 0, $t14);

    // $t1521 := &&($t1519, $t1520) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1521 := $And($t1519, $t1520);

    // $t1522 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1522 := $IsParentMutation($t12, 6, $t13);

    // $t1523 := &&($t1521, $t1522) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1523 := $And($t1521, $t1522);

    // if ($t1523) goto L601 else goto L602 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1523) { goto L601; } else { goto L602; }

    // label L601 at .\sources\ConditionalBorrowChain.move:106:9+25
L601:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L602 at .\sources\ConditionalBorrowChain.move:106:9+25
L602:

    // $t1524 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1524 := $IsParentMutation($t14, 6, $t15);

    // $t1525 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1525 := $IsParentMutation($t13, 1, $t14);

    // $t1526 := &&($t1524, $t1525) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1526 := $And($t1524, $t1525);

    // $t1527 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1527 := $IsParentMutation($t12, 0, $t13);

    // $t1528 := &&($t1526, $t1527) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1528 := $And($t1526, $t1527);

    // if ($t1528) goto L603 else goto L604 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1528) { goto L603; } else { goto L604; }

    // label L603 at .\sources\ConditionalBorrowChain.move:106:9+25
L603:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L604 at .\sources\ConditionalBorrowChain.move:106:9+25
L604:

    // $t1529 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1529 := $IsParentMutation($t14, 6, $t15);

    // $t1530 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1530 := $IsParentMutation($t13, 1, $t14);

    // $t1531 := &&($t1529, $t1530) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1531 := $And($t1529, $t1530);

    // $t1532 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1532 := $IsParentMutation($t12, 1, $t13);

    // $t1533 := &&($t1531, $t1532) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1533 := $And($t1531, $t1532);

    // if ($t1533) goto L605 else goto L606 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1533) { goto L605; } else { goto L606; }

    // label L605 at .\sources\ConditionalBorrowChain.move:106:9+25
L605:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L606 at .\sources\ConditionalBorrowChain.move:106:9+25
L606:

    // $t1534 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1534 := $IsParentMutation($t14, 6, $t15);

    // $t1535 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1535 := $IsParentMutation($t13, 1, $t14);

    // $t1536 := &&($t1534, $t1535) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1536 := $And($t1534, $t1535);

    // $t1537 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1537 := $IsParentMutation($t12, 2, $t13);

    // $t1538 := &&($t1536, $t1537) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1538 := $And($t1536, $t1537);

    // if ($t1538) goto L607 else goto L608 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1538) { goto L607; } else { goto L608; }

    // label L607 at .\sources\ConditionalBorrowChain.move:106:9+25
L607:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L608 at .\sources\ConditionalBorrowChain.move:106:9+25
L608:

    // $t1539 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1539 := $IsParentMutation($t14, 6, $t15);

    // $t1540 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1540 := $IsParentMutation($t13, 1, $t14);

    // $t1541 := &&($t1539, $t1540) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1541 := $And($t1539, $t1540);

    // $t1542 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1542 := $IsParentMutation($t12, 3, $t13);

    // $t1543 := &&($t1541, $t1542) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1543 := $And($t1541, $t1542);

    // if ($t1543) goto L609 else goto L610 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1543) { goto L609; } else { goto L610; }

    // label L609 at .\sources\ConditionalBorrowChain.move:106:9+25
L609:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L610 at .\sources\ConditionalBorrowChain.move:106:9+25
L610:

    // $t1544 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1544 := $IsParentMutation($t14, 6, $t15);

    // $t1545 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1545 := $IsParentMutation($t13, 1, $t14);

    // $t1546 := &&($t1544, $t1545) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1546 := $And($t1544, $t1545);

    // $t1547 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1547 := $IsParentMutation($t12, 4, $t13);

    // $t1548 := &&($t1546, $t1547) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1548 := $And($t1546, $t1547);

    // if ($t1548) goto L611 else goto L612 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1548) { goto L611; } else { goto L612; }

    // label L611 at .\sources\ConditionalBorrowChain.move:106:9+25
L611:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L612 at .\sources\ConditionalBorrowChain.move:106:9+25
L612:

    // $t1549 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1549 := $IsParentMutation($t14, 6, $t15);

    // $t1550 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1550 := $IsParentMutation($t13, 1, $t14);

    // $t1551 := &&($t1549, $t1550) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1551 := $And($t1549, $t1550);

    // $t1552 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1552 := $IsParentMutation($t12, 5, $t13);

    // $t1553 := &&($t1551, $t1552) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1553 := $And($t1551, $t1552);

    // if ($t1553) goto L613 else goto L614 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1553) { goto L613; } else { goto L614; }

    // label L613 at .\sources\ConditionalBorrowChain.move:106:9+25
L613:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L614 at .\sources\ConditionalBorrowChain.move:106:9+25
L614:

    // $t1554 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1554 := $IsParentMutation($t14, 6, $t15);

    // $t1555 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1555 := $IsParentMutation($t13, 1, $t14);

    // $t1556 := &&($t1554, $t1555) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1556 := $And($t1554, $t1555);

    // $t1557 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1557 := $IsParentMutation($t12, 6, $t13);

    // $t1558 := &&($t1556, $t1557) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1558 := $And($t1556, $t1557);

    // if ($t1558) goto L615 else goto L616 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1558) { goto L615; } else { goto L616; }

    // label L615 at .\sources\ConditionalBorrowChain.move:106:9+25
L615:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L616 at .\sources\ConditionalBorrowChain.move:106:9+25
L616:

    // $t1559 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1559 := $IsParentMutation($t14, 6, $t15);

    // $t1560 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1560 := $IsParentMutation($t13, 2, $t14);

    // $t1561 := &&($t1559, $t1560) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1561 := $And($t1559, $t1560);

    // $t1562 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1562 := $IsParentMutation($t12, 0, $t13);

    // $t1563 := &&($t1561, $t1562) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1563 := $And($t1561, $t1562);

    // if ($t1563) goto L617 else goto L618 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1563) { goto L617; } else { goto L618; }

    // label L617 at .\sources\ConditionalBorrowChain.move:106:9+25
L617:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L618 at .\sources\ConditionalBorrowChain.move:106:9+25
L618:

    // $t1564 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1564 := $IsParentMutation($t14, 6, $t15);

    // $t1565 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1565 := $IsParentMutation($t13, 2, $t14);

    // $t1566 := &&($t1564, $t1565) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1566 := $And($t1564, $t1565);

    // $t1567 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1567 := $IsParentMutation($t12, 1, $t13);

    // $t1568 := &&($t1566, $t1567) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1568 := $And($t1566, $t1567);

    // if ($t1568) goto L619 else goto L620 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1568) { goto L619; } else { goto L620; }

    // label L619 at .\sources\ConditionalBorrowChain.move:106:9+25
L619:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L620 at .\sources\ConditionalBorrowChain.move:106:9+25
L620:

    // $t1569 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1569 := $IsParentMutation($t14, 6, $t15);

    // $t1570 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1570 := $IsParentMutation($t13, 2, $t14);

    // $t1571 := &&($t1569, $t1570) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1571 := $And($t1569, $t1570);

    // $t1572 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1572 := $IsParentMutation($t12, 2, $t13);

    // $t1573 := &&($t1571, $t1572) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1573 := $And($t1571, $t1572);

    // if ($t1573) goto L621 else goto L622 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1573) { goto L621; } else { goto L622; }

    // label L621 at .\sources\ConditionalBorrowChain.move:106:9+25
L621:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L622 at .\sources\ConditionalBorrowChain.move:106:9+25
L622:

    // $t1574 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1574 := $IsParentMutation($t14, 6, $t15);

    // $t1575 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1575 := $IsParentMutation($t13, 2, $t14);

    // $t1576 := &&($t1574, $t1575) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1576 := $And($t1574, $t1575);

    // $t1577 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1577 := $IsParentMutation($t12, 3, $t13);

    // $t1578 := &&($t1576, $t1577) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1578 := $And($t1576, $t1577);

    // if ($t1578) goto L623 else goto L624 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1578) { goto L623; } else { goto L624; }

    // label L623 at .\sources\ConditionalBorrowChain.move:106:9+25
L623:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L624 at .\sources\ConditionalBorrowChain.move:106:9+25
L624:

    // $t1579 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1579 := $IsParentMutation($t14, 6, $t15);

    // $t1580 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1580 := $IsParentMutation($t13, 2, $t14);

    // $t1581 := &&($t1579, $t1580) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1581 := $And($t1579, $t1580);

    // $t1582 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1582 := $IsParentMutation($t12, 4, $t13);

    // $t1583 := &&($t1581, $t1582) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1583 := $And($t1581, $t1582);

    // if ($t1583) goto L625 else goto L626 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1583) { goto L625; } else { goto L626; }

    // label L625 at .\sources\ConditionalBorrowChain.move:106:9+25
L625:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L626 at .\sources\ConditionalBorrowChain.move:106:9+25
L626:

    // $t1584 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1584 := $IsParentMutation($t14, 6, $t15);

    // $t1585 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1585 := $IsParentMutation($t13, 2, $t14);

    // $t1586 := &&($t1584, $t1585) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1586 := $And($t1584, $t1585);

    // $t1587 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1587 := $IsParentMutation($t12, 5, $t13);

    // $t1588 := &&($t1586, $t1587) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1588 := $And($t1586, $t1587);

    // if ($t1588) goto L627 else goto L628 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1588) { goto L627; } else { goto L628; }

    // label L627 at .\sources\ConditionalBorrowChain.move:106:9+25
L627:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L628 at .\sources\ConditionalBorrowChain.move:106:9+25
L628:

    // $t1589 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1589 := $IsParentMutation($t14, 6, $t15);

    // $t1590 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1590 := $IsParentMutation($t13, 2, $t14);

    // $t1591 := &&($t1589, $t1590) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1591 := $And($t1589, $t1590);

    // $t1592 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1592 := $IsParentMutation($t12, 6, $t13);

    // $t1593 := &&($t1591, $t1592) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1593 := $And($t1591, $t1592);

    // if ($t1593) goto L629 else goto L630 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1593) { goto L629; } else { goto L630; }

    // label L629 at .\sources\ConditionalBorrowChain.move:106:9+25
L629:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L630 at .\sources\ConditionalBorrowChain.move:106:9+25
L630:

    // $t1594 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1594 := $IsParentMutation($t14, 6, $t15);

    // $t1595 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1595 := $IsParentMutation($t13, 3, $t14);

    // $t1596 := &&($t1594, $t1595) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1596 := $And($t1594, $t1595);

    // $t1597 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1597 := $IsParentMutation($t12, 0, $t13);

    // $t1598 := &&($t1596, $t1597) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1598 := $And($t1596, $t1597);

    // if ($t1598) goto L631 else goto L632 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1598) { goto L631; } else { goto L632; }

    // label L631 at .\sources\ConditionalBorrowChain.move:106:9+25
L631:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L632 at .\sources\ConditionalBorrowChain.move:106:9+25
L632:

    // $t1599 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1599 := $IsParentMutation($t14, 6, $t15);

    // $t1600 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1600 := $IsParentMutation($t13, 3, $t14);

    // $t1601 := &&($t1599, $t1600) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1601 := $And($t1599, $t1600);

    // $t1602 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1602 := $IsParentMutation($t12, 1, $t13);

    // $t1603 := &&($t1601, $t1602) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1603 := $And($t1601, $t1602);

    // if ($t1603) goto L633 else goto L634 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1603) { goto L633; } else { goto L634; }

    // label L633 at .\sources\ConditionalBorrowChain.move:106:9+25
L633:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L634 at .\sources\ConditionalBorrowChain.move:106:9+25
L634:

    // $t1604 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1604 := $IsParentMutation($t14, 6, $t15);

    // $t1605 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1605 := $IsParentMutation($t13, 3, $t14);

    // $t1606 := &&($t1604, $t1605) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1606 := $And($t1604, $t1605);

    // $t1607 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1607 := $IsParentMutation($t12, 2, $t13);

    // $t1608 := &&($t1606, $t1607) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1608 := $And($t1606, $t1607);

    // if ($t1608) goto L635 else goto L636 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1608) { goto L635; } else { goto L636; }

    // label L635 at .\sources\ConditionalBorrowChain.move:106:9+25
L635:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L636 at .\sources\ConditionalBorrowChain.move:106:9+25
L636:

    // $t1609 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1609 := $IsParentMutation($t14, 6, $t15);

    // $t1610 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1610 := $IsParentMutation($t13, 3, $t14);

    // $t1611 := &&($t1609, $t1610) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1611 := $And($t1609, $t1610);

    // $t1612 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1612 := $IsParentMutation($t12, 3, $t13);

    // $t1613 := &&($t1611, $t1612) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1613 := $And($t1611, $t1612);

    // if ($t1613) goto L637 else goto L638 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1613) { goto L637; } else { goto L638; }

    // label L637 at .\sources\ConditionalBorrowChain.move:106:9+25
L637:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L638 at .\sources\ConditionalBorrowChain.move:106:9+25
L638:

    // $t1614 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1614 := $IsParentMutation($t14, 6, $t15);

    // $t1615 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1615 := $IsParentMutation($t13, 3, $t14);

    // $t1616 := &&($t1614, $t1615) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1616 := $And($t1614, $t1615);

    // $t1617 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1617 := $IsParentMutation($t12, 4, $t13);

    // $t1618 := &&($t1616, $t1617) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1618 := $And($t1616, $t1617);

    // if ($t1618) goto L639 else goto L640 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1618) { goto L639; } else { goto L640; }

    // label L639 at .\sources\ConditionalBorrowChain.move:106:9+25
L639:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L640 at .\sources\ConditionalBorrowChain.move:106:9+25
L640:

    // $t1619 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1619 := $IsParentMutation($t14, 6, $t15);

    // $t1620 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1620 := $IsParentMutation($t13, 3, $t14);

    // $t1621 := &&($t1619, $t1620) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1621 := $And($t1619, $t1620);

    // $t1622 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1622 := $IsParentMutation($t12, 5, $t13);

    // $t1623 := &&($t1621, $t1622) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1623 := $And($t1621, $t1622);

    // if ($t1623) goto L641 else goto L642 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1623) { goto L641; } else { goto L642; }

    // label L641 at .\sources\ConditionalBorrowChain.move:106:9+25
L641:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L642 at .\sources\ConditionalBorrowChain.move:106:9+25
L642:

    // $t1624 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1624 := $IsParentMutation($t14, 6, $t15);

    // $t1625 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1625 := $IsParentMutation($t13, 3, $t14);

    // $t1626 := &&($t1624, $t1625) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1626 := $And($t1624, $t1625);

    // $t1627 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1627 := $IsParentMutation($t12, 6, $t13);

    // $t1628 := &&($t1626, $t1627) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1628 := $And($t1626, $t1627);

    // if ($t1628) goto L643 else goto L644 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1628) { goto L643; } else { goto L644; }

    // label L643 at .\sources\ConditionalBorrowChain.move:106:9+25
L643:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L644 at .\sources\ConditionalBorrowChain.move:106:9+25
L644:

    // $t1629 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1629 := $IsParentMutation($t14, 6, $t15);

    // $t1630 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1630 := $IsParentMutation($t13, 4, $t14);

    // $t1631 := &&($t1629, $t1630) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1631 := $And($t1629, $t1630);

    // $t1632 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1632 := $IsParentMutation($t12, 0, $t13);

    // $t1633 := &&($t1631, $t1632) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1633 := $And($t1631, $t1632);

    // if ($t1633) goto L645 else goto L646 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1633) { goto L645; } else { goto L646; }

    // label L645 at .\sources\ConditionalBorrowChain.move:106:9+25
L645:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L646 at .\sources\ConditionalBorrowChain.move:106:9+25
L646:

    // $t1634 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1634 := $IsParentMutation($t14, 6, $t15);

    // $t1635 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1635 := $IsParentMutation($t13, 4, $t14);

    // $t1636 := &&($t1634, $t1635) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1636 := $And($t1634, $t1635);

    // $t1637 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1637 := $IsParentMutation($t12, 1, $t13);

    // $t1638 := &&($t1636, $t1637) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1638 := $And($t1636, $t1637);

    // if ($t1638) goto L647 else goto L648 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1638) { goto L647; } else { goto L648; }

    // label L647 at .\sources\ConditionalBorrowChain.move:106:9+25
L647:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L648 at .\sources\ConditionalBorrowChain.move:106:9+25
L648:

    // $t1639 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1639 := $IsParentMutation($t14, 6, $t15);

    // $t1640 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1640 := $IsParentMutation($t13, 4, $t14);

    // $t1641 := &&($t1639, $t1640) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1641 := $And($t1639, $t1640);

    // $t1642 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1642 := $IsParentMutation($t12, 2, $t13);

    // $t1643 := &&($t1641, $t1642) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1643 := $And($t1641, $t1642);

    // if ($t1643) goto L649 else goto L650 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1643) { goto L649; } else { goto L650; }

    // label L649 at .\sources\ConditionalBorrowChain.move:106:9+25
L649:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L650 at .\sources\ConditionalBorrowChain.move:106:9+25
L650:

    // $t1644 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1644 := $IsParentMutation($t14, 6, $t15);

    // $t1645 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1645 := $IsParentMutation($t13, 4, $t14);

    // $t1646 := &&($t1644, $t1645) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1646 := $And($t1644, $t1645);

    // $t1647 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1647 := $IsParentMutation($t12, 3, $t13);

    // $t1648 := &&($t1646, $t1647) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1648 := $And($t1646, $t1647);

    // if ($t1648) goto L651 else goto L652 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1648) { goto L651; } else { goto L652; }

    // label L651 at .\sources\ConditionalBorrowChain.move:106:9+25
L651:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L652 at .\sources\ConditionalBorrowChain.move:106:9+25
L652:

    // $t1649 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1649 := $IsParentMutation($t14, 6, $t15);

    // $t1650 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1650 := $IsParentMutation($t13, 4, $t14);

    // $t1651 := &&($t1649, $t1650) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1651 := $And($t1649, $t1650);

    // $t1652 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1652 := $IsParentMutation($t12, 4, $t13);

    // $t1653 := &&($t1651, $t1652) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1653 := $And($t1651, $t1652);

    // if ($t1653) goto L653 else goto L654 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1653) { goto L653; } else { goto L654; }

    // label L653 at .\sources\ConditionalBorrowChain.move:106:9+25
L653:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L654 at .\sources\ConditionalBorrowChain.move:106:9+25
L654:

    // $t1654 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1654 := $IsParentMutation($t14, 6, $t15);

    // $t1655 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1655 := $IsParentMutation($t13, 4, $t14);

    // $t1656 := &&($t1654, $t1655) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1656 := $And($t1654, $t1655);

    // $t1657 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1657 := $IsParentMutation($t12, 5, $t13);

    // $t1658 := &&($t1656, $t1657) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1658 := $And($t1656, $t1657);

    // if ($t1658) goto L655 else goto L656 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1658) { goto L655; } else { goto L656; }

    // label L655 at .\sources\ConditionalBorrowChain.move:106:9+25
L655:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L656 at .\sources\ConditionalBorrowChain.move:106:9+25
L656:

    // $t1659 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1659 := $IsParentMutation($t14, 6, $t15);

    // $t1660 := is_parent[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1660 := $IsParentMutation($t13, 4, $t14);

    // $t1661 := &&($t1659, $t1660) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1661 := $And($t1659, $t1660);

    // $t1662 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1662 := $IsParentMutation($t12, 6, $t13);

    // $t1663 := &&($t1661, $t1662) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1663 := $And($t1661, $t1662);

    // if ($t1663) goto L657 else goto L658 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1663) { goto L657; } else { goto L658; }

    // label L657 at .\sources\ConditionalBorrowChain.move:106:9+25
L657:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v4 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v4($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L658 at .\sources\ConditionalBorrowChain.move:106:9+25
L658:

    // $t1664 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1664 := $IsParentMutation($t14, 6, $t15);

    // $t1665 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1665 := $IsParentMutation($t13, 5, $t14);

    // $t1666 := &&($t1664, $t1665) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1666 := $And($t1664, $t1665);

    // $t1667 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1667 := $IsParentMutation($t12, 0, $t13);

    // $t1668 := &&($t1666, $t1667) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1668 := $And($t1666, $t1667);

    // if ($t1668) goto L659 else goto L660 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1668) { goto L659; } else { goto L660; }

    // label L659 at .\sources\ConditionalBorrowChain.move:106:9+25
L659:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L660 at .\sources\ConditionalBorrowChain.move:106:9+25
L660:

    // $t1669 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1669 := $IsParentMutation($t14, 6, $t15);

    // $t1670 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1670 := $IsParentMutation($t13, 5, $t14);

    // $t1671 := &&($t1669, $t1670) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1671 := $And($t1669, $t1670);

    // $t1672 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1672 := $IsParentMutation($t12, 1, $t13);

    // $t1673 := &&($t1671, $t1672) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1673 := $And($t1671, $t1672);

    // if ($t1673) goto L661 else goto L662 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1673) { goto L661; } else { goto L662; }

    // label L661 at .\sources\ConditionalBorrowChain.move:106:9+25
L661:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L662 at .\sources\ConditionalBorrowChain.move:106:9+25
L662:

    // $t1674 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1674 := $IsParentMutation($t14, 6, $t15);

    // $t1675 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1675 := $IsParentMutation($t13, 5, $t14);

    // $t1676 := &&($t1674, $t1675) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1676 := $And($t1674, $t1675);

    // $t1677 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1677 := $IsParentMutation($t12, 2, $t13);

    // $t1678 := &&($t1676, $t1677) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1678 := $And($t1676, $t1677);

    // if ($t1678) goto L663 else goto L664 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1678) { goto L663; } else { goto L664; }

    // label L663 at .\sources\ConditionalBorrowChain.move:106:9+25
L663:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L664 at .\sources\ConditionalBorrowChain.move:106:9+25
L664:

    // $t1679 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1679 := $IsParentMutation($t14, 6, $t15);

    // $t1680 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1680 := $IsParentMutation($t13, 5, $t14);

    // $t1681 := &&($t1679, $t1680) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1681 := $And($t1679, $t1680);

    // $t1682 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1682 := $IsParentMutation($t12, 3, $t13);

    // $t1683 := &&($t1681, $t1682) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1683 := $And($t1681, $t1682);

    // if ($t1683) goto L665 else goto L666 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1683) { goto L665; } else { goto L666; }

    // label L665 at .\sources\ConditionalBorrowChain.move:106:9+25
L665:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L666 at .\sources\ConditionalBorrowChain.move:106:9+25
L666:

    // $t1684 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1684 := $IsParentMutation($t14, 6, $t15);

    // $t1685 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1685 := $IsParentMutation($t13, 5, $t14);

    // $t1686 := &&($t1684, $t1685) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1686 := $And($t1684, $t1685);

    // $t1687 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1687 := $IsParentMutation($t12, 4, $t13);

    // $t1688 := &&($t1686, $t1687) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1688 := $And($t1686, $t1687);

    // if ($t1688) goto L667 else goto L668 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1688) { goto L667; } else { goto L668; }

    // label L667 at .\sources\ConditionalBorrowChain.move:106:9+25
L667:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L668 at .\sources\ConditionalBorrowChain.move:106:9+25
L668:

    // $t1689 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1689 := $IsParentMutation($t14, 6, $t15);

    // $t1690 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1690 := $IsParentMutation($t13, 5, $t14);

    // $t1691 := &&($t1689, $t1690) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1691 := $And($t1689, $t1690);

    // $t1692 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1692 := $IsParentMutation($t12, 5, $t13);

    // $t1693 := &&($t1691, $t1692) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1693 := $And($t1691, $t1692);

    // if ($t1693) goto L669 else goto L670 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1693) { goto L669; } else { goto L670; }

    // label L669 at .\sources\ConditionalBorrowChain.move:106:9+25
L669:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L670 at .\sources\ConditionalBorrowChain.move:106:9+25
L670:

    // $t1694 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1694 := $IsParentMutation($t14, 6, $t15);

    // $t1695 := is_parent[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1695 := $IsParentMutation($t13, 5, $t14);

    // $t1696 := &&($t1694, $t1695) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1696 := $And($t1694, $t1695);

    // $t1697 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1697 := $IsParentMutation($t12, 6, $t13);

    // $t1698 := &&($t1696, $t1697) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1698 := $And($t1696, $t1697);

    // if ($t1698) goto L671 else goto L672 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1698) { goto L671; } else { goto L672; }

    // label L671 at .\sources\ConditionalBorrowChain.move:106:9+25
L671:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v5 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v5($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L672 at .\sources\ConditionalBorrowChain.move:106:9+25
L672:

    // $t1699 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1699 := $IsParentMutation($t14, 6, $t15);

    // $t1700 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1700 := $IsParentMutation($t13, 6, $t14);

    // $t1701 := &&($t1699, $t1700) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1701 := $And($t1699, $t1700);

    // $t1702 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1702 := $IsParentMutation($t12, 0, $t13);

    // $t1703 := &&($t1701, $t1702) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1703 := $And($t1701, $t1702);

    // if ($t1703) goto L673 else goto L674 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1703) { goto L673; } else { goto L674; }

    // label L673 at .\sources\ConditionalBorrowChain.move:106:9+25
L673:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L674 at .\sources\ConditionalBorrowChain.move:106:9+25
L674:

    // $t1704 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1704 := $IsParentMutation($t14, 6, $t15);

    // $t1705 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1705 := $IsParentMutation($t13, 6, $t14);

    // $t1706 := &&($t1704, $t1705) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1706 := $And($t1704, $t1705);

    // $t1707 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1707 := $IsParentMutation($t12, 1, $t13);

    // $t1708 := &&($t1706, $t1707) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1708 := $And($t1706, $t1707);

    // if ($t1708) goto L675 else goto L676 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1708) { goto L675; } else { goto L676; }

    // label L675 at .\sources\ConditionalBorrowChain.move:106:9+25
L675:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L676 at .\sources\ConditionalBorrowChain.move:106:9+25
L676:

    // $t1709 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1709 := $IsParentMutation($t14, 6, $t15);

    // $t1710 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1710 := $IsParentMutation($t13, 6, $t14);

    // $t1711 := &&($t1709, $t1710) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1711 := $And($t1709, $t1710);

    // $t1712 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1712 := $IsParentMutation($t12, 2, $t13);

    // $t1713 := &&($t1711, $t1712) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1713 := $And($t1711, $t1712);

    // if ($t1713) goto L677 else goto L678 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1713) { goto L677; } else { goto L678; }

    // label L677 at .\sources\ConditionalBorrowChain.move:106:9+25
L677:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L678 at .\sources\ConditionalBorrowChain.move:106:9+25
L678:

    // $t1714 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1714 := $IsParentMutation($t14, 6, $t15);

    // $t1715 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1715 := $IsParentMutation($t13, 6, $t14);

    // $t1716 := &&($t1714, $t1715) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1716 := $And($t1714, $t1715);

    // $t1717 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1717 := $IsParentMutation($t12, 3, $t13);

    // $t1718 := &&($t1716, $t1717) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1718 := $And($t1716, $t1717);

    // if ($t1718) goto L679 else goto L680 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1718) { goto L679; } else { goto L680; }

    // label L679 at .\sources\ConditionalBorrowChain.move:106:9+25
L679:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L680 at .\sources\ConditionalBorrowChain.move:106:9+25
L680:

    // $t1719 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1719 := $IsParentMutation($t14, 6, $t15);

    // $t1720 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1720 := $IsParentMutation($t13, 6, $t14);

    // $t1721 := &&($t1719, $t1720) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1721 := $And($t1719, $t1720);

    // $t1722 := is_parent[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1722 := $IsParentMutation($t12, 4, $t13);

    // $t1723 := &&($t1721, $t1722) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1723 := $And($t1721, $t1722);

    // if ($t1723) goto L681 else goto L682 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1723) { goto L681; } else { goto L682; }

    // label L681 at .\sources\ConditionalBorrowChain.move:106:9+25
L681:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v4 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v4($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L682 at .\sources\ConditionalBorrowChain.move:106:9+25
L682:

    // $t1724 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1724 := $IsParentMutation($t14, 6, $t15);

    // $t1725 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1725 := $IsParentMutation($t13, 6, $t14);

    // $t1726 := &&($t1724, $t1725) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1726 := $And($t1724, $t1725);

    // $t1727 := is_parent[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1727 := $IsParentMutation($t12, 5, $t13);

    // $t1728 := &&($t1726, $t1727) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1728 := $And($t1726, $t1727);

    // if ($t1728) goto L683 else goto L684 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1728) { goto L683; } else { goto L684; }

    // label L683 at .\sources\ConditionalBorrowChain.move:106:9+25
L683:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v5 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v5($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L684 at .\sources\ConditionalBorrowChain.move:106:9+25
L684:

    // $t1729 := is_parent[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t1729 := $IsParentMutation($t14, 6, $t15);

    // $t1730 := is_parent[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1730 := $IsParentMutation($t13, 6, $t14);

    // $t1731 := &&($t1729, $t1730) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1731 := $And($t1729, $t1730);

    // $t1732 := is_parent[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t1732 := $IsParentMutation($t12, 6, $t13);

    // $t1733 := &&($t1731, $t1732) at .\sources\ConditionalBorrowChain.move:106:9+25
    call $t1733 := $And($t1731, $t1732);

    // if ($t1733) goto L685 else goto L689 at .\sources\ConditionalBorrowChain.move:106:9+25
    if ($t1733) { goto L685; } else { goto L689; }

    // label L685 at .\sources\ConditionalBorrowChain.move:106:9+25
L685:

    // write_back[Reference($t14).v6 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$at(3,3526,3551)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels_Node1'_v6($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v6 (0xbc::ProphecyBenchmark3Levels::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels_Node2'_v6($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v6 (0xbc::ProphecyBenchmark3Levels::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels_Node3'_v6($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:106:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:106:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L686 at .\sources\ConditionalBorrowChain.move:106:9+25
L686:

    // $t1734 := move($t3) at .\sources\ConditionalBorrowChain.move:108:9+4
    assume {:print "$at(3,3562,3566)"} true;
    $t1734 := $t3;

    // trace_return[0]($t1734) at .\sources\ConditionalBorrowChain.move:93:14+418
    assume {:print "$at(3,3154,3572)"} true;
    assume {:print "$track_return(2,0,0):", $t1734} $t1734 == $t1734;

    // label L687 at .\sources\ConditionalBorrowChain.move:109:5+1
    assume {:print "$at(3,3571,3572)"} true;
L687:

    // assert Implies(And(And(Eq<u64>($t0, 0), Eq<u64>($t1, 0)), Eq<u64>($t2, 0)), Eq<u64>(select ProphecyBenchmark3Levels::Node1.v0<0xbc::ProphecyBenchmark3Levels::Node1>(select ProphecyBenchmark3Levels::Node2.v0<0xbc::ProphecyBenchmark3Levels::Node2>(select ProphecyBenchmark3Levels::Node3.v0<0xbc::ProphecyBenchmark3Levels::Node3>($t1734))), 1)) at .\sources\ConditionalBorrowChain.move:125:9+72
    assume {:print "$at(3,3907,3979)"} true;
    assert {:msg "assert_failed(3,3907,3979): post-condition does not hold"}
      ((($IsEqual'u64'($t0, 0) && $IsEqual'u64'($t1, 0)) && $IsEqual'u64'($t2, 0)) ==> $IsEqual'u64'($t1734->$v0->$v0->$v0, 1));

    // assert Le(select ProphecyBenchmark3Levels::Node1.v0<0xbc::ProphecyBenchmark3Levels::Node1>(select ProphecyBenchmark3Levels::Node2.v0<0xbc::ProphecyBenchmark3Levels::Node2>(select ProphecyBenchmark3Levels::Node3.v0<0xbc::ProphecyBenchmark3Levels::Node3>($t1734))), 1) at .\sources\ConditionalBorrowChain.move:133:9+29
    assume {:print "$at(3,4179,4208)"} true;
    assert {:msg "assert_failed(3,4179,4208): post-condition does not hold"}
      ($t1734->$v0->$v0->$v0 <= 1);

    // return $t1734 at .\sources\ConditionalBorrowChain.move:133:9+29
    $ret0 := $t1734;
    return;

    // label L688 at .\sources\ConditionalBorrowChain.move:109:5+1
    assume {:print "$at(3,3571,3572)"} true;
L688:

    // abort($t5) at .\sources\ConditionalBorrowChain.move:109:5+1
    assume {:print "$at(3,3571,3572)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

    // label L689 at <internal>:1:1+10
    assume {:print "$at(1,0,10)"} true;
L689:

    // drop($t12) at <internal>:1:1+10
    assume {:print "$at(1,0,10)"} true;

    // drop($t13) at <internal>:1:1+10

    // drop($t14) at <internal>:1:1+10

    // drop($t15) at <internal>:1:1+10

    // goto L686 at <internal>:1:1+10
    goto L686;

}

// fun ProphecyBenchmark3Levels::new_node1 [baseline] at .\sources\ConditionalBorrowChain.move:29:5+110
procedure {:inline 1} $bc_ProphecyBenchmark3Levels_new_node1() returns ($ret0: $bc_ProphecyBenchmark3Levels_Node1)
{
    // declare local variables
    var $t0: int;
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: $bc_ProphecyBenchmark3Levels_Node1;
    var $temp_0'$bc_ProphecyBenchmark3Levels_Node1': $bc_ProphecyBenchmark3Levels_Node1;

    // bytecode translation starts here
    // $t0 := 0 at .\sources\ConditionalBorrowChain.move:30:21+1
    assume {:print "$at(3,924,925)"} true;
    $t0 := 0;
    assume $IsValid'u64'($t0);

    // $t1 := 0 at .\sources\ConditionalBorrowChain.move:30:28+1
    $t1 := 0;
    assume $IsValid'u64'($t1);

    // $t2 := 0 at .\sources\ConditionalBorrowChain.move:30:35+1
    $t2 := 0;
    assume $IsValid'u64'($t2);

    // $t3 := 0 at .\sources\ConditionalBorrowChain.move:30:42+1
    $t3 := 0;
    assume $IsValid'u64'($t3);

    // $t4 := 0 at .\sources\ConditionalBorrowChain.move:30:49+1
    $t4 := 0;
    assume $IsValid'u64'($t4);

    // $t5 := 0 at .\sources\ConditionalBorrowChain.move:30:56+1
    $t5 := 0;
    assume $IsValid'u64'($t5);

    // $t6 := 0 at .\sources\ConditionalBorrowChain.move:30:63+1
    $t6 := 0;
    assume $IsValid'u64'($t6);

    // $t7 := 0 at .\sources\ConditionalBorrowChain.move:30:70+1
    $t7 := 0;
    assume $IsValid'u64'($t7);

    // $t8 := pack 0xbc::ProphecyBenchmark3Levels::Node1($t0, $t1, $t2, $t3, $t4, $t5, $t6, $t7) at .\sources\ConditionalBorrowChain.move:30:9+64
    $t8 := $bc_ProphecyBenchmark3Levels_Node1($t0, $t1, $t2, $t3, $t4, $t5, $t6, $t7);

    // trace_return[0]($t8) at .\sources\ConditionalBorrowChain.move:30:9+64
    assume {:print "$track_return(2,1,0):", $t8} $t8 == $t8;

    // label L1 at .\sources\ConditionalBorrowChain.move:31:5+1
    assume {:print "$at(3,981,982)"} true;
L1:

    // return $t8 at .\sources\ConditionalBorrowChain.move:31:5+1
    assume {:print "$at(3,981,982)"} true;
    $ret0 := $t8;
    return;

}

// fun ProphecyBenchmark3Levels::new_node1 [verification] at .\sources\ConditionalBorrowChain.move:29:5+110
procedure {:timeLimit 40} $bc_ProphecyBenchmark3Levels_new_node1$verify() returns ($ret0: $bc_ProphecyBenchmark3Levels_Node1)
{
    // declare local variables
    var $t0: int;
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: $bc_ProphecyBenchmark3Levels_Node1;
    var $temp_0'$bc_ProphecyBenchmark3Levels_Node1': $bc_ProphecyBenchmark3Levels_Node1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t0 := 0 at .\sources\ConditionalBorrowChain.move:30:21+1
    assume {:print "$at(3,924,925)"} true;
    $t0 := 0;
    assume $IsValid'u64'($t0);

    // $t1 := 0 at .\sources\ConditionalBorrowChain.move:30:28+1
    $t1 := 0;
    assume $IsValid'u64'($t1);

    // $t2 := 0 at .\sources\ConditionalBorrowChain.move:30:35+1
    $t2 := 0;
    assume $IsValid'u64'($t2);

    // $t3 := 0 at .\sources\ConditionalBorrowChain.move:30:42+1
    $t3 := 0;
    assume $IsValid'u64'($t3);

    // $t4 := 0 at .\sources\ConditionalBorrowChain.move:30:49+1
    $t4 := 0;
    assume $IsValid'u64'($t4);

    // $t5 := 0 at .\sources\ConditionalBorrowChain.move:30:56+1
    $t5 := 0;
    assume $IsValid'u64'($t5);

    // $t6 := 0 at .\sources\ConditionalBorrowChain.move:30:63+1
    $t6 := 0;
    assume $IsValid'u64'($t6);

    // $t7 := 0 at .\sources\ConditionalBorrowChain.move:30:70+1
    $t7 := 0;
    assume $IsValid'u64'($t7);

    // $t8 := pack 0xbc::ProphecyBenchmark3Levels::Node1($t0, $t1, $t2, $t3, $t4, $t5, $t6, $t7) at .\sources\ConditionalBorrowChain.move:30:9+64
    $t8 := $bc_ProphecyBenchmark3Levels_Node1($t0, $t1, $t2, $t3, $t4, $t5, $t6, $t7);

    // trace_return[0]($t8) at .\sources\ConditionalBorrowChain.move:30:9+64
    assume {:print "$track_return(2,1,0):", $t8} $t8 == $t8;

    // label L1 at .\sources\ConditionalBorrowChain.move:31:5+1
    assume {:print "$at(3,981,982)"} true;
L1:

    // return $t8 at .\sources\ConditionalBorrowChain.move:31:5+1
    assume {:print "$at(3,981,982)"} true;
    $ret0 := $t8;
    return;

}

// fun ProphecyBenchmark3Levels::new_node2 [baseline] at .\sources\ConditionalBorrowChain.move:33:5+225
procedure {:inline 1} $bc_ProphecyBenchmark3Levels_new_node2() returns ($ret0: $bc_ProphecyBenchmark3Levels_Node2)
{
    // declare local variables
    var $t0: $bc_ProphecyBenchmark3Levels_Node1;
    var $t1: int;
    var $t2: $bc_ProphecyBenchmark3Levels_Node1;
    var $t3: $bc_ProphecyBenchmark3Levels_Node1;
    var $t4: $bc_ProphecyBenchmark3Levels_Node1;
    var $t5: $bc_ProphecyBenchmark3Levels_Node1;
    var $t6: $bc_ProphecyBenchmark3Levels_Node1;
    var $t7: $bc_ProphecyBenchmark3Levels_Node1;
    var $t8: $bc_ProphecyBenchmark3Levels_Node1;
    var $t9: $bc_ProphecyBenchmark3Levels_Node2;
    var $temp_0'$bc_ProphecyBenchmark3Levels_Node2': $bc_ProphecyBenchmark3Levels_Node2;

    // bytecode translation starts here
    // $t0 := ProphecyBenchmark3Levels::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:35:17+11
    assume {:print "$at(3,1053,1064)"} true;
    call $t0 := $bc_ProphecyBenchmark3Levels_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1053,1064)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t2 := ProphecyBenchmark3Levels::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:35:34+11
    call $t2 := $bc_ProphecyBenchmark3Levels_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1070,1081)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t3 := ProphecyBenchmark3Levels::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:35:51+11
    call $t3 := $bc_ProphecyBenchmark3Levels_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1087,1098)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t4 := ProphecyBenchmark3Levels::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:35:68+11
    call $t4 := $bc_ProphecyBenchmark3Levels_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1104,1115)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t5 := ProphecyBenchmark3Levels::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:36:17+11
    assume {:print "$at(3,1134,1145)"} true;
    call $t5 := $bc_ProphecyBenchmark3Levels_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1134,1145)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t6 := ProphecyBenchmark3Levels::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:36:34+11
    call $t6 := $bc_ProphecyBenchmark3Levels_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1151,1162)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t7 := ProphecyBenchmark3Levels::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:36:51+11
    call $t7 := $bc_ProphecyBenchmark3Levels_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1168,1179)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t8 := ProphecyBenchmark3Levels::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:36:68+11
    call $t8 := $bc_ProphecyBenchmark3Levels_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1185,1196)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t9 := pack 0xbc::ProphecyBenchmark3Levels::Node2($t0, $t2, $t3, $t4, $t5, $t6, $t7, $t8) at .\sources\ConditionalBorrowChain.move:34:9+179
    assume {:print "$at(3,1028,1207)"} true;
    $t9 := $bc_ProphecyBenchmark3Levels_Node2($t0, $t2, $t3, $t4, $t5, $t6, $t7, $t8);

    // trace_return[0]($t9) at .\sources\ConditionalBorrowChain.move:34:9+179
    assume {:print "$track_return(2,2,0):", $t9} $t9 == $t9;

    // label L1 at .\sources\ConditionalBorrowChain.move:38:5+1
    assume {:print "$at(3,1212,1213)"} true;
L1:

    // return $t9 at .\sources\ConditionalBorrowChain.move:38:5+1
    assume {:print "$at(3,1212,1213)"} true;
    $ret0 := $t9;
    return;

    // label L2 at .\sources\ConditionalBorrowChain.move:38:5+1
L2:

    // abort($t1) at .\sources\ConditionalBorrowChain.move:38:5+1
    assume {:print "$at(3,1212,1213)"} true;
    $abort_code := $t1;
    $abort_flag := true;
    return;

}

// fun ProphecyBenchmark3Levels::new_node2 [verification] at .\sources\ConditionalBorrowChain.move:33:5+225
procedure {:timeLimit 40} $bc_ProphecyBenchmark3Levels_new_node2$verify() returns ($ret0: $bc_ProphecyBenchmark3Levels_Node2)
{
    // declare local variables
    var $t0: $bc_ProphecyBenchmark3Levels_Node1;
    var $t1: int;
    var $t2: $bc_ProphecyBenchmark3Levels_Node1;
    var $t3: $bc_ProphecyBenchmark3Levels_Node1;
    var $t4: $bc_ProphecyBenchmark3Levels_Node1;
    var $t5: $bc_ProphecyBenchmark3Levels_Node1;
    var $t6: $bc_ProphecyBenchmark3Levels_Node1;
    var $t7: $bc_ProphecyBenchmark3Levels_Node1;
    var $t8: $bc_ProphecyBenchmark3Levels_Node1;
    var $t9: $bc_ProphecyBenchmark3Levels_Node2;
    var $temp_0'$bc_ProphecyBenchmark3Levels_Node2': $bc_ProphecyBenchmark3Levels_Node2;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t0 := ProphecyBenchmark3Levels::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:35:17+11
    assume {:print "$at(3,1053,1064)"} true;
    call $t0 := $bc_ProphecyBenchmark3Levels_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1053,1064)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t2 := ProphecyBenchmark3Levels::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:35:34+11
    call $t2 := $bc_ProphecyBenchmark3Levels_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1070,1081)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t3 := ProphecyBenchmark3Levels::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:35:51+11
    call $t3 := $bc_ProphecyBenchmark3Levels_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1087,1098)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t4 := ProphecyBenchmark3Levels::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:35:68+11
    call $t4 := $bc_ProphecyBenchmark3Levels_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1104,1115)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t5 := ProphecyBenchmark3Levels::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:36:17+11
    assume {:print "$at(3,1134,1145)"} true;
    call $t5 := $bc_ProphecyBenchmark3Levels_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1134,1145)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t6 := ProphecyBenchmark3Levels::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:36:34+11
    call $t6 := $bc_ProphecyBenchmark3Levels_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1151,1162)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t7 := ProphecyBenchmark3Levels::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:36:51+11
    call $t7 := $bc_ProphecyBenchmark3Levels_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1168,1179)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t8 := ProphecyBenchmark3Levels::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:36:68+11
    call $t8 := $bc_ProphecyBenchmark3Levels_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1185,1196)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t9 := pack 0xbc::ProphecyBenchmark3Levels::Node2($t0, $t2, $t3, $t4, $t5, $t6, $t7, $t8) at .\sources\ConditionalBorrowChain.move:34:9+179
    assume {:print "$at(3,1028,1207)"} true;
    $t9 := $bc_ProphecyBenchmark3Levels_Node2($t0, $t2, $t3, $t4, $t5, $t6, $t7, $t8);

    // trace_return[0]($t9) at .\sources\ConditionalBorrowChain.move:34:9+179
    assume {:print "$track_return(2,2,0):", $t9} $t9 == $t9;

    // label L1 at .\sources\ConditionalBorrowChain.move:38:5+1
    assume {:print "$at(3,1212,1213)"} true;
L1:

    // return $t9 at .\sources\ConditionalBorrowChain.move:38:5+1
    assume {:print "$at(3,1212,1213)"} true;
    $ret0 := $t9;
    return;

    // label L2 at .\sources\ConditionalBorrowChain.move:38:5+1
L2:

    // abort($t1) at .\sources\ConditionalBorrowChain.move:38:5+1
    assume {:print "$at(3,1212,1213)"} true;
    $abort_code := $t1;
    $abort_flag := true;
    return;

}

// fun ProphecyBenchmark3Levels::new_node3 [baseline] at .\sources\ConditionalBorrowChain.move:40:5+225
procedure {:inline 1} $bc_ProphecyBenchmark3Levels_new_node3() returns ($ret0: $bc_ProphecyBenchmark3Levels_Node3)
{
    // declare local variables
    var $t0: $bc_ProphecyBenchmark3Levels_Node2;
    var $t1: int;
    var $t2: $bc_ProphecyBenchmark3Levels_Node2;
    var $t3: $bc_ProphecyBenchmark3Levels_Node2;
    var $t4: $bc_ProphecyBenchmark3Levels_Node2;
    var $t5: $bc_ProphecyBenchmark3Levels_Node2;
    var $t6: $bc_ProphecyBenchmark3Levels_Node2;
    var $t7: $bc_ProphecyBenchmark3Levels_Node2;
    var $t8: $bc_ProphecyBenchmark3Levels_Node2;
    var $t9: $bc_ProphecyBenchmark3Levels_Node3;
    var $temp_0'$bc_ProphecyBenchmark3Levels_Node3': $bc_ProphecyBenchmark3Levels_Node3;

    // bytecode translation starts here
    // $t0 := ProphecyBenchmark3Levels::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:42:17+11
    assume {:print "$at(3,1284,1295)"} true;
    call $t0 := $bc_ProphecyBenchmark3Levels_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1284,1295)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t2 := ProphecyBenchmark3Levels::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:42:34+11
    call $t2 := $bc_ProphecyBenchmark3Levels_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1301,1312)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t3 := ProphecyBenchmark3Levels::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:42:51+11
    call $t3 := $bc_ProphecyBenchmark3Levels_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1318,1329)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t4 := ProphecyBenchmark3Levels::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:42:68+11
    call $t4 := $bc_ProphecyBenchmark3Levels_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1335,1346)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t5 := ProphecyBenchmark3Levels::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:43:17+11
    assume {:print "$at(3,1365,1376)"} true;
    call $t5 := $bc_ProphecyBenchmark3Levels_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1365,1376)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t6 := ProphecyBenchmark3Levels::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:43:34+11
    call $t6 := $bc_ProphecyBenchmark3Levels_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1382,1393)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t7 := ProphecyBenchmark3Levels::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:43:51+11
    call $t7 := $bc_ProphecyBenchmark3Levels_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1399,1410)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t8 := ProphecyBenchmark3Levels::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:43:68+11
    call $t8 := $bc_ProphecyBenchmark3Levels_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1416,1427)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t9 := pack 0xbc::ProphecyBenchmark3Levels::Node3($t0, $t2, $t3, $t4, $t5, $t6, $t7, $t8) at .\sources\ConditionalBorrowChain.move:41:9+179
    assume {:print "$at(3,1259,1438)"} true;
    $t9 := $bc_ProphecyBenchmark3Levels_Node3($t0, $t2, $t3, $t4, $t5, $t6, $t7, $t8);

    // trace_return[0]($t9) at .\sources\ConditionalBorrowChain.move:41:9+179
    assume {:print "$track_return(2,3,0):", $t9} $t9 == $t9;

    // label L1 at .\sources\ConditionalBorrowChain.move:45:5+1
    assume {:print "$at(3,1443,1444)"} true;
L1:

    // return $t9 at .\sources\ConditionalBorrowChain.move:45:5+1
    assume {:print "$at(3,1443,1444)"} true;
    $ret0 := $t9;
    return;

    // label L2 at .\sources\ConditionalBorrowChain.move:45:5+1
L2:

    // abort($t1) at .\sources\ConditionalBorrowChain.move:45:5+1
    assume {:print "$at(3,1443,1444)"} true;
    $abort_code := $t1;
    $abort_flag := true;
    return;

}

// fun ProphecyBenchmark3Levels::new_node3 [verification] at .\sources\ConditionalBorrowChain.move:40:5+225
procedure {:timeLimit 40} $bc_ProphecyBenchmark3Levels_new_node3$verify() returns ($ret0: $bc_ProphecyBenchmark3Levels_Node3)
{
    // declare local variables
    var $t0: $bc_ProphecyBenchmark3Levels_Node2;
    var $t1: int;
    var $t2: $bc_ProphecyBenchmark3Levels_Node2;
    var $t3: $bc_ProphecyBenchmark3Levels_Node2;
    var $t4: $bc_ProphecyBenchmark3Levels_Node2;
    var $t5: $bc_ProphecyBenchmark3Levels_Node2;
    var $t6: $bc_ProphecyBenchmark3Levels_Node2;
    var $t7: $bc_ProphecyBenchmark3Levels_Node2;
    var $t8: $bc_ProphecyBenchmark3Levels_Node2;
    var $t9: $bc_ProphecyBenchmark3Levels_Node3;
    var $temp_0'$bc_ProphecyBenchmark3Levels_Node3': $bc_ProphecyBenchmark3Levels_Node3;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t0 := ProphecyBenchmark3Levels::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:42:17+11
    assume {:print "$at(3,1284,1295)"} true;
    call $t0 := $bc_ProphecyBenchmark3Levels_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1284,1295)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t2 := ProphecyBenchmark3Levels::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:42:34+11
    call $t2 := $bc_ProphecyBenchmark3Levels_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1301,1312)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t3 := ProphecyBenchmark3Levels::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:42:51+11
    call $t3 := $bc_ProphecyBenchmark3Levels_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1318,1329)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t4 := ProphecyBenchmark3Levels::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:42:68+11
    call $t4 := $bc_ProphecyBenchmark3Levels_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1335,1346)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t5 := ProphecyBenchmark3Levels::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:43:17+11
    assume {:print "$at(3,1365,1376)"} true;
    call $t5 := $bc_ProphecyBenchmark3Levels_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1365,1376)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t6 := ProphecyBenchmark3Levels::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:43:34+11
    call $t6 := $bc_ProphecyBenchmark3Levels_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1382,1393)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t7 := ProphecyBenchmark3Levels::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:43:51+11
    call $t7 := $bc_ProphecyBenchmark3Levels_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1399,1410)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t8 := ProphecyBenchmark3Levels::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:43:68+11
    call $t8 := $bc_ProphecyBenchmark3Levels_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1416,1427)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t9 := pack 0xbc::ProphecyBenchmark3Levels::Node3($t0, $t2, $t3, $t4, $t5, $t6, $t7, $t8) at .\sources\ConditionalBorrowChain.move:41:9+179
    assume {:print "$at(3,1259,1438)"} true;
    $t9 := $bc_ProphecyBenchmark3Levels_Node3($t0, $t2, $t3, $t4, $t5, $t6, $t7, $t8);

    // trace_return[0]($t9) at .\sources\ConditionalBorrowChain.move:41:9+179
    assume {:print "$track_return(2,3,0):", $t9} $t9 == $t9;

    // label L1 at .\sources\ConditionalBorrowChain.move:45:5+1
    assume {:print "$at(3,1443,1444)"} true;
L1:

    // return $t9 at .\sources\ConditionalBorrowChain.move:45:5+1
    assume {:print "$at(3,1443,1444)"} true;
    $ret0 := $t9;
    return;

    // label L2 at .\sources\ConditionalBorrowChain.move:45:5+1
L2:

    // abort($t1) at .\sources\ConditionalBorrowChain.move:45:5+1
    assume {:print "$at(3,1443,1444)"} true;
    $abort_code := $t1;
    $abort_flag := true;
    return;

}

// fun ProphecyBenchmark3Levels::select_leaf [baseline] at .\sources\ConditionalBorrowChain.move:76:5+302
procedure {:inline 1} $bc_ProphecyBenchmark3Levels_select_leaf(_$t0: $Mutation ($bc_ProphecyBenchmark3Levels_Node1), _$t1: int) returns ($ret0: $Mutation (int), $ret1: $Mutation ($bc_ProphecyBenchmark3Levels_Node1))
{
    // declare local variables
    var $t2: int;
    var $t3: bool;
    var $t4: $Mutation (int);
    var $t5: $Mutation (int);
    var $t6: int;
    var $t7: bool;
    var $t8: $Mutation (int);
    var $t9: int;
    var $t10: bool;
    var $t11: $Mutation (int);
    var $t12: int;
    var $t13: bool;
    var $t14: $Mutation (int);
    var $t15: int;
    var $t16: bool;
    var $t17: $Mutation (int);
    var $t18: int;
    var $t19: bool;
    var $t20: $Mutation (int);
    var $t21: $Mutation (int);
    var $t0: $Mutation ($bc_ProphecyBenchmark3Levels_Node1);
    var $t1: int;
    var $temp_0'$bc_ProphecyBenchmark3Levels_Node1': $bc_ProphecyBenchmark3Levels_Node1;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:76:5+1
    assume {:print "$at(3,2535,2536)"} true;
    $temp_0'$bc_ProphecyBenchmark3Levels_Node1' := $Dereference($t0);
    assume {:print "$track_local(2,4,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels_Node1';

    // trace_local[idx]($t1) at .\sources\ConditionalBorrowChain.move:76:5+1
    assume {:print "$track_local(2,4,1):", $t1} $t1 == $t1;

    // $t2 := 0 at .\sources\ConditionalBorrowChain.move:77:20+1
    assume {:print "$at(3,2607,2608)"} true;
    $t2 := 0;
    assume $IsValid'u64'($t2);

    // $t3 := ==($t1, $t2) at .\sources\ConditionalBorrowChain.move:77:13+8
    $t3 := $IsEqual'u64'($t1, $t2);

    // if ($t3) goto L1 else goto L0 at .\sources\ConditionalBorrowChain.move:77:9+235
    if ($t3) { goto L1; } else { goto L0; }

    // label L1 at .\sources\ConditionalBorrowChain.move:77:25+9
L1:

    // $t4 := borrow_field<0xbc::ProphecyBenchmark3Levels::Node1>.v0($t0) at .\sources\ConditionalBorrowChain.move:77:25+9
    assume {:print "$at(3,2612,2621)"} true;
    $t4 := $ChildMutation($t0, 0, $Dereference($t0)->$v0);

    // trace_return[0]($t4) at .\sources\ConditionalBorrowChain.move:77:9+235
    $temp_0'u64' := $Dereference($t4);
    assume {:print "$track_return(2,4,0):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:77:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node1' := $Dereference($t0);
    assume {:print "$track_local(2,4,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels_Node1';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:77:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node1' := $Dereference($t0);
    assume {:print "$track_local(2,4,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels_Node1';

    // $t5 := move($t4) at .\sources\ConditionalBorrowChain.move:77:9+235
    $t5 := $t4;

    // goto L12 at .\sources\ConditionalBorrowChain.move:77:9+235
    goto L12;

    // label L0 at .\sources\ConditionalBorrowChain.move:77:46+3
L0:

    // $t6 := 1 at .\sources\ConditionalBorrowChain.move:77:53+1
    assume {:print "$at(3,2640,2641)"} true;
    $t6 := 1;
    assume $IsValid'u64'($t6);

    // $t7 := ==($t1, $t6) at .\sources\ConditionalBorrowChain.move:77:46+8
    $t7 := $IsEqual'u64'($t1, $t6);

    // if ($t7) goto L3 else goto L2 at .\sources\ConditionalBorrowChain.move:77:42+202
    if ($t7) { goto L3; } else { goto L2; }

    // label L3 at .\sources\ConditionalBorrowChain.move:77:58+9
L3:

    // $t8 := borrow_field<0xbc::ProphecyBenchmark3Levels::Node1>.v1($t0) at .\sources\ConditionalBorrowChain.move:77:58+9
    assume {:print "$at(3,2645,2654)"} true;
    $t8 := $ChildMutation($t0, 1, $Dereference($t0)->$v1);

    // trace_return[0]($t8) at .\sources\ConditionalBorrowChain.move:77:9+235
    $temp_0'u64' := $Dereference($t8);
    assume {:print "$track_return(2,4,0):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:77:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node1' := $Dereference($t0);
    assume {:print "$track_local(2,4,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels_Node1';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:77:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node1' := $Dereference($t0);
    assume {:print "$track_local(2,4,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels_Node1';

    // $t5 := move($t8) at .\sources\ConditionalBorrowChain.move:77:9+235
    $t5 := $t8;

    // goto L12 at .\sources\ConditionalBorrowChain.move:77:9+235
    goto L12;

    // label L2 at .\sources\ConditionalBorrowChain.move:78:18+3
    assume {:print "$at(3,2674,2677)"} true;
L2:

    // $t9 := 2 at .\sources\ConditionalBorrowChain.move:78:25+1
    assume {:print "$at(3,2681,2682)"} true;
    $t9 := 2;
    assume $IsValid'u64'($t9);

    // $t10 := ==($t1, $t9) at .\sources\ConditionalBorrowChain.move:78:18+8
    $t10 := $IsEqual'u64'($t1, $t9);

    // if ($t10) goto L5 else goto L4 at .\sources\ConditionalBorrowChain.move:78:14+161
    if ($t10) { goto L5; } else { goto L4; }

    // label L5 at .\sources\ConditionalBorrowChain.move:78:30+9
L5:

    // $t11 := borrow_field<0xbc::ProphecyBenchmark3Levels::Node1>.v2($t0) at .\sources\ConditionalBorrowChain.move:78:30+9
    assume {:print "$at(3,2686,2695)"} true;
    $t11 := $ChildMutation($t0, 2, $Dereference($t0)->$v2);

    // trace_return[0]($t11) at .\sources\ConditionalBorrowChain.move:77:9+235
    assume {:print "$at(3,2596,2831)"} true;
    $temp_0'u64' := $Dereference($t11);
    assume {:print "$track_return(2,4,0):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:77:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node1' := $Dereference($t0);
    assume {:print "$track_local(2,4,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels_Node1';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:77:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node1' := $Dereference($t0);
    assume {:print "$track_local(2,4,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels_Node1';

    // $t5 := move($t11) at .\sources\ConditionalBorrowChain.move:77:9+235
    $t5 := $t11;

    // goto L12 at .\sources\ConditionalBorrowChain.move:77:9+235
    goto L12;

    // label L4 at .\sources\ConditionalBorrowChain.move:78:51+3
    assume {:print "$at(3,2707,2710)"} true;
L4:

    // $t12 := 3 at .\sources\ConditionalBorrowChain.move:78:58+1
    assume {:print "$at(3,2714,2715)"} true;
    $t12 := 3;
    assume $IsValid'u64'($t12);

    // $t13 := ==($t1, $t12) at .\sources\ConditionalBorrowChain.move:78:51+8
    $t13 := $IsEqual'u64'($t1, $t12);

    // if ($t13) goto L7 else goto L6 at .\sources\ConditionalBorrowChain.move:78:47+128
    if ($t13) { goto L7; } else { goto L6; }

    // label L7 at .\sources\ConditionalBorrowChain.move:78:63+9
L7:

    // $t14 := borrow_field<0xbc::ProphecyBenchmark3Levels::Node1>.v3($t0) at .\sources\ConditionalBorrowChain.move:78:63+9
    assume {:print "$at(3,2719,2728)"} true;
    $t14 := $ChildMutation($t0, 3, $Dereference($t0)->$v3);

    // trace_return[0]($t14) at .\sources\ConditionalBorrowChain.move:77:9+235
    assume {:print "$at(3,2596,2831)"} true;
    $temp_0'u64' := $Dereference($t14);
    assume {:print "$track_return(2,4,0):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:77:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node1' := $Dereference($t0);
    assume {:print "$track_local(2,4,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels_Node1';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:77:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node1' := $Dereference($t0);
    assume {:print "$track_local(2,4,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels_Node1';

    // $t5 := move($t14) at .\sources\ConditionalBorrowChain.move:77:9+235
    $t5 := $t14;

    // goto L12 at .\sources\ConditionalBorrowChain.move:77:9+235
    goto L12;

    // label L6 at .\sources\ConditionalBorrowChain.move:79:18+3
    assume {:print "$at(3,2748,2751)"} true;
L6:

    // $t15 := 4 at .\sources\ConditionalBorrowChain.move:79:25+1
    assume {:print "$at(3,2755,2756)"} true;
    $t15 := 4;
    assume $IsValid'u64'($t15);

    // $t16 := ==($t1, $t15) at .\sources\ConditionalBorrowChain.move:79:18+8
    $t16 := $IsEqual'u64'($t1, $t15);

    // if ($t16) goto L9 else goto L8 at .\sources\ConditionalBorrowChain.move:79:14+87
    if ($t16) { goto L9; } else { goto L8; }

    // label L9 at .\sources\ConditionalBorrowChain.move:79:30+9
L9:

    // $t17 := borrow_field<0xbc::ProphecyBenchmark3Levels::Node1>.v4($t0) at .\sources\ConditionalBorrowChain.move:79:30+9
    assume {:print "$at(3,2760,2769)"} true;
    $t17 := $ChildMutation($t0, 4, $Dereference($t0)->$v4);

    // trace_return[0]($t17) at .\sources\ConditionalBorrowChain.move:77:9+235
    assume {:print "$at(3,2596,2831)"} true;
    $temp_0'u64' := $Dereference($t17);
    assume {:print "$track_return(2,4,0):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:77:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node1' := $Dereference($t0);
    assume {:print "$track_local(2,4,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels_Node1';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:77:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node1' := $Dereference($t0);
    assume {:print "$track_local(2,4,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels_Node1';

    // $t5 := move($t17) at .\sources\ConditionalBorrowChain.move:77:9+235
    $t5 := $t17;

    // goto L12 at .\sources\ConditionalBorrowChain.move:77:9+235
    goto L12;

    // label L8 at .\sources\ConditionalBorrowChain.move:79:51+3
    assume {:print "$at(3,2781,2784)"} true;
L8:

    // $t18 := 5 at .\sources\ConditionalBorrowChain.move:79:58+1
    assume {:print "$at(3,2788,2789)"} true;
    $t18 := 5;
    assume $IsValid'u64'($t18);

    // $t19 := ==($t1, $t18) at .\sources\ConditionalBorrowChain.move:79:51+8
    $t19 := $IsEqual'u64'($t1, $t18);

    // if ($t19) goto L11 else goto L10 at .\sources\ConditionalBorrowChain.move:79:47+54
    if ($t19) { goto L11; } else { goto L10; }

    // label L11 at .\sources\ConditionalBorrowChain.move:79:63+9
L11:

    // $t20 := borrow_field<0xbc::ProphecyBenchmark3Levels::Node1>.v5($t0) at .\sources\ConditionalBorrowChain.move:79:63+9
    assume {:print "$at(3,2793,2802)"} true;
    $t20 := $ChildMutation($t0, 5, $Dereference($t0)->$v5);

    // trace_return[0]($t20) at .\sources\ConditionalBorrowChain.move:77:9+235
    assume {:print "$at(3,2596,2831)"} true;
    $temp_0'u64' := $Dereference($t20);
    assume {:print "$track_return(2,4,0):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:77:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node1' := $Dereference($t0);
    assume {:print "$track_local(2,4,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels_Node1';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:77:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node1' := $Dereference($t0);
    assume {:print "$track_local(2,4,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels_Node1';

    // $t5 := move($t20) at .\sources\ConditionalBorrowChain.move:77:9+235
    $t5 := $t20;

    // goto L12 at .\sources\ConditionalBorrowChain.move:77:9+235
    goto L12;

    // label L10 at .\sources\ConditionalBorrowChain.move:80:16+9
    assume {:print "$at(3,2820,2829)"} true;
L10:

    // $t21 := borrow_field<0xbc::ProphecyBenchmark3Levels::Node1>.v6($t0) at .\sources\ConditionalBorrowChain.move:80:16+9
    assume {:print "$at(3,2820,2829)"} true;
    $t21 := $ChildMutation($t0, 6, $Dereference($t0)->$v6);

    // trace_return[0]($t21) at .\sources\ConditionalBorrowChain.move:77:9+235
    assume {:print "$at(3,2596,2831)"} true;
    $temp_0'u64' := $Dereference($t21);
    assume {:print "$track_return(2,4,0):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:77:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node1' := $Dereference($t0);
    assume {:print "$track_local(2,4,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels_Node1';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:77:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node1' := $Dereference($t0);
    assume {:print "$track_local(2,4,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels_Node1';

    // $t5 := move($t21) at .\sources\ConditionalBorrowChain.move:77:9+235
    $t5 := $t21;

    // label L12 at .\sources\ConditionalBorrowChain.move:81:5+1
    assume {:print "$at(3,2836,2837)"} true;
L12:

    // return $t5 at .\sources\ConditionalBorrowChain.move:81:5+1
    assume {:print "$at(3,2836,2837)"} true;
    $ret0 := $t5;
    $ret1 := $t0;
    return;

}

// fun ProphecyBenchmark3Levels::select_n1 [baseline] at .\sources\ConditionalBorrowChain.move:64:5+302
procedure {:inline 1} $bc_ProphecyBenchmark3Levels_select_n1(_$t0: $Mutation ($bc_ProphecyBenchmark3Levels_Node2), _$t1: int) returns ($ret0: $Mutation ($bc_ProphecyBenchmark3Levels_Node1), $ret1: $Mutation ($bc_ProphecyBenchmark3Levels_Node2))
{
    // declare local variables
    var $t2: int;
    var $t3: bool;
    var $t4: $Mutation ($bc_ProphecyBenchmark3Levels_Node1);
    var $t5: $Mutation ($bc_ProphecyBenchmark3Levels_Node1);
    var $t6: int;
    var $t7: bool;
    var $t8: $Mutation ($bc_ProphecyBenchmark3Levels_Node1);
    var $t9: int;
    var $t10: bool;
    var $t11: $Mutation ($bc_ProphecyBenchmark3Levels_Node1);
    var $t12: int;
    var $t13: bool;
    var $t14: $Mutation ($bc_ProphecyBenchmark3Levels_Node1);
    var $t15: int;
    var $t16: bool;
    var $t17: $Mutation ($bc_ProphecyBenchmark3Levels_Node1);
    var $t18: int;
    var $t19: bool;
    var $t20: $Mutation ($bc_ProphecyBenchmark3Levels_Node1);
    var $t21: $Mutation ($bc_ProphecyBenchmark3Levels_Node1);
    var $t0: $Mutation ($bc_ProphecyBenchmark3Levels_Node2);
    var $t1: int;
    var $temp_0'$bc_ProphecyBenchmark3Levels_Node1': $bc_ProphecyBenchmark3Levels_Node1;
    var $temp_0'$bc_ProphecyBenchmark3Levels_Node2': $bc_ProphecyBenchmark3Levels_Node2;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:64:5+1
    assume {:print "$at(3,2092,2093)"} true;
    $temp_0'$bc_ProphecyBenchmark3Levels_Node2' := $Dereference($t0);
    assume {:print "$track_local(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels_Node2';

    // trace_local[idx]($t1) at .\sources\ConditionalBorrowChain.move:64:5+1
    assume {:print "$track_local(2,5,1):", $t1} $t1 == $t1;

    // $t2 := 0 at .\sources\ConditionalBorrowChain.move:65:20+1
    assume {:print "$at(3,2164,2165)"} true;
    $t2 := 0;
    assume $IsValid'u64'($t2);

    // $t3 := ==($t1, $t2) at .\sources\ConditionalBorrowChain.move:65:13+8
    $t3 := $IsEqual'u64'($t1, $t2);

    // if ($t3) goto L1 else goto L0 at .\sources\ConditionalBorrowChain.move:65:9+235
    if ($t3) { goto L1; } else { goto L0; }

    // label L1 at .\sources\ConditionalBorrowChain.move:65:25+9
L1:

    // $t4 := borrow_field<0xbc::ProphecyBenchmark3Levels::Node2>.v0($t0) at .\sources\ConditionalBorrowChain.move:65:25+9
    assume {:print "$at(3,2169,2178)"} true;
    $t4 := $ChildMutation($t0, 0, $Dereference($t0)->$v0);

    // trace_return[0]($t4) at .\sources\ConditionalBorrowChain.move:65:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node1' := $Dereference($t4);
    assume {:print "$track_return(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels_Node1';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:65:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node2' := $Dereference($t0);
    assume {:print "$track_local(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels_Node2';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:65:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node2' := $Dereference($t0);
    assume {:print "$track_local(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels_Node2';

    // $t5 := move($t4) at .\sources\ConditionalBorrowChain.move:65:9+235
    $t5 := $t4;

    // goto L12 at .\sources\ConditionalBorrowChain.move:65:9+235
    goto L12;

    // label L0 at .\sources\ConditionalBorrowChain.move:65:46+3
L0:

    // $t6 := 1 at .\sources\ConditionalBorrowChain.move:65:53+1
    assume {:print "$at(3,2197,2198)"} true;
    $t6 := 1;
    assume $IsValid'u64'($t6);

    // $t7 := ==($t1, $t6) at .\sources\ConditionalBorrowChain.move:65:46+8
    $t7 := $IsEqual'u64'($t1, $t6);

    // if ($t7) goto L3 else goto L2 at .\sources\ConditionalBorrowChain.move:65:42+202
    if ($t7) { goto L3; } else { goto L2; }

    // label L3 at .\sources\ConditionalBorrowChain.move:65:58+9
L3:

    // $t8 := borrow_field<0xbc::ProphecyBenchmark3Levels::Node2>.v1($t0) at .\sources\ConditionalBorrowChain.move:65:58+9
    assume {:print "$at(3,2202,2211)"} true;
    $t8 := $ChildMutation($t0, 1, $Dereference($t0)->$v1);

    // trace_return[0]($t8) at .\sources\ConditionalBorrowChain.move:65:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node1' := $Dereference($t8);
    assume {:print "$track_return(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels_Node1';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:65:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node2' := $Dereference($t0);
    assume {:print "$track_local(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels_Node2';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:65:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node2' := $Dereference($t0);
    assume {:print "$track_local(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels_Node2';

    // $t5 := move($t8) at .\sources\ConditionalBorrowChain.move:65:9+235
    $t5 := $t8;

    // goto L12 at .\sources\ConditionalBorrowChain.move:65:9+235
    goto L12;

    // label L2 at .\sources\ConditionalBorrowChain.move:66:18+3
    assume {:print "$at(3,2231,2234)"} true;
L2:

    // $t9 := 2 at .\sources\ConditionalBorrowChain.move:66:25+1
    assume {:print "$at(3,2238,2239)"} true;
    $t9 := 2;
    assume $IsValid'u64'($t9);

    // $t10 := ==($t1, $t9) at .\sources\ConditionalBorrowChain.move:66:18+8
    $t10 := $IsEqual'u64'($t1, $t9);

    // if ($t10) goto L5 else goto L4 at .\sources\ConditionalBorrowChain.move:66:14+161
    if ($t10) { goto L5; } else { goto L4; }

    // label L5 at .\sources\ConditionalBorrowChain.move:66:30+9
L5:

    // $t11 := borrow_field<0xbc::ProphecyBenchmark3Levels::Node2>.v2($t0) at .\sources\ConditionalBorrowChain.move:66:30+9
    assume {:print "$at(3,2243,2252)"} true;
    $t11 := $ChildMutation($t0, 2, $Dereference($t0)->$v2);

    // trace_return[0]($t11) at .\sources\ConditionalBorrowChain.move:65:9+235
    assume {:print "$at(3,2153,2388)"} true;
    $temp_0'$bc_ProphecyBenchmark3Levels_Node1' := $Dereference($t11);
    assume {:print "$track_return(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels_Node1';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:65:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node2' := $Dereference($t0);
    assume {:print "$track_local(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels_Node2';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:65:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node2' := $Dereference($t0);
    assume {:print "$track_local(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels_Node2';

    // $t5 := move($t11) at .\sources\ConditionalBorrowChain.move:65:9+235
    $t5 := $t11;

    // goto L12 at .\sources\ConditionalBorrowChain.move:65:9+235
    goto L12;

    // label L4 at .\sources\ConditionalBorrowChain.move:66:51+3
    assume {:print "$at(3,2264,2267)"} true;
L4:

    // $t12 := 3 at .\sources\ConditionalBorrowChain.move:66:58+1
    assume {:print "$at(3,2271,2272)"} true;
    $t12 := 3;
    assume $IsValid'u64'($t12);

    // $t13 := ==($t1, $t12) at .\sources\ConditionalBorrowChain.move:66:51+8
    $t13 := $IsEqual'u64'($t1, $t12);

    // if ($t13) goto L7 else goto L6 at .\sources\ConditionalBorrowChain.move:66:47+128
    if ($t13) { goto L7; } else { goto L6; }

    // label L7 at .\sources\ConditionalBorrowChain.move:66:63+9
L7:

    // $t14 := borrow_field<0xbc::ProphecyBenchmark3Levels::Node2>.v3($t0) at .\sources\ConditionalBorrowChain.move:66:63+9
    assume {:print "$at(3,2276,2285)"} true;
    $t14 := $ChildMutation($t0, 3, $Dereference($t0)->$v3);

    // trace_return[0]($t14) at .\sources\ConditionalBorrowChain.move:65:9+235
    assume {:print "$at(3,2153,2388)"} true;
    $temp_0'$bc_ProphecyBenchmark3Levels_Node1' := $Dereference($t14);
    assume {:print "$track_return(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels_Node1';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:65:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node2' := $Dereference($t0);
    assume {:print "$track_local(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels_Node2';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:65:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node2' := $Dereference($t0);
    assume {:print "$track_local(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels_Node2';

    // $t5 := move($t14) at .\sources\ConditionalBorrowChain.move:65:9+235
    $t5 := $t14;

    // goto L12 at .\sources\ConditionalBorrowChain.move:65:9+235
    goto L12;

    // label L6 at .\sources\ConditionalBorrowChain.move:67:18+3
    assume {:print "$at(3,2305,2308)"} true;
L6:

    // $t15 := 4 at .\sources\ConditionalBorrowChain.move:67:25+1
    assume {:print "$at(3,2312,2313)"} true;
    $t15 := 4;
    assume $IsValid'u64'($t15);

    // $t16 := ==($t1, $t15) at .\sources\ConditionalBorrowChain.move:67:18+8
    $t16 := $IsEqual'u64'($t1, $t15);

    // if ($t16) goto L9 else goto L8 at .\sources\ConditionalBorrowChain.move:67:14+87
    if ($t16) { goto L9; } else { goto L8; }

    // label L9 at .\sources\ConditionalBorrowChain.move:67:30+9
L9:

    // $t17 := borrow_field<0xbc::ProphecyBenchmark3Levels::Node2>.v4($t0) at .\sources\ConditionalBorrowChain.move:67:30+9
    assume {:print "$at(3,2317,2326)"} true;
    $t17 := $ChildMutation($t0, 4, $Dereference($t0)->$v4);

    // trace_return[0]($t17) at .\sources\ConditionalBorrowChain.move:65:9+235
    assume {:print "$at(3,2153,2388)"} true;
    $temp_0'$bc_ProphecyBenchmark3Levels_Node1' := $Dereference($t17);
    assume {:print "$track_return(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels_Node1';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:65:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node2' := $Dereference($t0);
    assume {:print "$track_local(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels_Node2';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:65:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node2' := $Dereference($t0);
    assume {:print "$track_local(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels_Node2';

    // $t5 := move($t17) at .\sources\ConditionalBorrowChain.move:65:9+235
    $t5 := $t17;

    // goto L12 at .\sources\ConditionalBorrowChain.move:65:9+235
    goto L12;

    // label L8 at .\sources\ConditionalBorrowChain.move:67:51+3
    assume {:print "$at(3,2338,2341)"} true;
L8:

    // $t18 := 5 at .\sources\ConditionalBorrowChain.move:67:58+1
    assume {:print "$at(3,2345,2346)"} true;
    $t18 := 5;
    assume $IsValid'u64'($t18);

    // $t19 := ==($t1, $t18) at .\sources\ConditionalBorrowChain.move:67:51+8
    $t19 := $IsEqual'u64'($t1, $t18);

    // if ($t19) goto L11 else goto L10 at .\sources\ConditionalBorrowChain.move:67:47+54
    if ($t19) { goto L11; } else { goto L10; }

    // label L11 at .\sources\ConditionalBorrowChain.move:67:63+9
L11:

    // $t20 := borrow_field<0xbc::ProphecyBenchmark3Levels::Node2>.v5($t0) at .\sources\ConditionalBorrowChain.move:67:63+9
    assume {:print "$at(3,2350,2359)"} true;
    $t20 := $ChildMutation($t0, 5, $Dereference($t0)->$v5);

    // trace_return[0]($t20) at .\sources\ConditionalBorrowChain.move:65:9+235
    assume {:print "$at(3,2153,2388)"} true;
    $temp_0'$bc_ProphecyBenchmark3Levels_Node1' := $Dereference($t20);
    assume {:print "$track_return(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels_Node1';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:65:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node2' := $Dereference($t0);
    assume {:print "$track_local(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels_Node2';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:65:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node2' := $Dereference($t0);
    assume {:print "$track_local(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels_Node2';

    // $t5 := move($t20) at .\sources\ConditionalBorrowChain.move:65:9+235
    $t5 := $t20;

    // goto L12 at .\sources\ConditionalBorrowChain.move:65:9+235
    goto L12;

    // label L10 at .\sources\ConditionalBorrowChain.move:68:16+9
    assume {:print "$at(3,2377,2386)"} true;
L10:

    // $t21 := borrow_field<0xbc::ProphecyBenchmark3Levels::Node2>.v6($t0) at .\sources\ConditionalBorrowChain.move:68:16+9
    assume {:print "$at(3,2377,2386)"} true;
    $t21 := $ChildMutation($t0, 6, $Dereference($t0)->$v6);

    // trace_return[0]($t21) at .\sources\ConditionalBorrowChain.move:65:9+235
    assume {:print "$at(3,2153,2388)"} true;
    $temp_0'$bc_ProphecyBenchmark3Levels_Node1' := $Dereference($t21);
    assume {:print "$track_return(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels_Node1';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:65:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node2' := $Dereference($t0);
    assume {:print "$track_local(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels_Node2';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:65:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node2' := $Dereference($t0);
    assume {:print "$track_local(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels_Node2';

    // $t5 := move($t21) at .\sources\ConditionalBorrowChain.move:65:9+235
    $t5 := $t21;

    // label L12 at .\sources\ConditionalBorrowChain.move:69:5+1
    assume {:print "$at(3,2393,2394)"} true;
L12:

    // return $t5 at .\sources\ConditionalBorrowChain.move:69:5+1
    assume {:print "$at(3,2393,2394)"} true;
    $ret0 := $t5;
    $ret1 := $t0;
    return;

}

// fun ProphecyBenchmark3Levels::select_n2 [baseline] at .\sources\ConditionalBorrowChain.move:52:5+302
procedure {:inline 1} $bc_ProphecyBenchmark3Levels_select_n2(_$t0: $Mutation ($bc_ProphecyBenchmark3Levels_Node3), _$t1: int) returns ($ret0: $Mutation ($bc_ProphecyBenchmark3Levels_Node2), $ret1: $Mutation ($bc_ProphecyBenchmark3Levels_Node3))
{
    // declare local variables
    var $t2: int;
    var $t3: bool;
    var $t4: $Mutation ($bc_ProphecyBenchmark3Levels_Node2);
    var $t5: $Mutation ($bc_ProphecyBenchmark3Levels_Node2);
    var $t6: int;
    var $t7: bool;
    var $t8: $Mutation ($bc_ProphecyBenchmark3Levels_Node2);
    var $t9: int;
    var $t10: bool;
    var $t11: $Mutation ($bc_ProphecyBenchmark3Levels_Node2);
    var $t12: int;
    var $t13: bool;
    var $t14: $Mutation ($bc_ProphecyBenchmark3Levels_Node2);
    var $t15: int;
    var $t16: bool;
    var $t17: $Mutation ($bc_ProphecyBenchmark3Levels_Node2);
    var $t18: int;
    var $t19: bool;
    var $t20: $Mutation ($bc_ProphecyBenchmark3Levels_Node2);
    var $t21: $Mutation ($bc_ProphecyBenchmark3Levels_Node2);
    var $t0: $Mutation ($bc_ProphecyBenchmark3Levels_Node3);
    var $t1: int;
    var $temp_0'$bc_ProphecyBenchmark3Levels_Node2': $bc_ProphecyBenchmark3Levels_Node2;
    var $temp_0'$bc_ProphecyBenchmark3Levels_Node3': $bc_ProphecyBenchmark3Levels_Node3;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:52:5+1
    assume {:print "$at(3,1645,1646)"} true;
    $temp_0'$bc_ProphecyBenchmark3Levels_Node3' := $Dereference($t0);
    assume {:print "$track_local(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node3'} $temp_0'$bc_ProphecyBenchmark3Levels_Node3' == $temp_0'$bc_ProphecyBenchmark3Levels_Node3';

    // trace_local[idx]($t1) at .\sources\ConditionalBorrowChain.move:52:5+1
    assume {:print "$track_local(2,6,1):", $t1} $t1 == $t1;

    // $t2 := 0 at .\sources\ConditionalBorrowChain.move:53:20+1
    assume {:print "$at(3,1717,1718)"} true;
    $t2 := 0;
    assume $IsValid'u64'($t2);

    // $t3 := ==($t1, $t2) at .\sources\ConditionalBorrowChain.move:53:13+8
    $t3 := $IsEqual'u64'($t1, $t2);

    // if ($t3) goto L1 else goto L0 at .\sources\ConditionalBorrowChain.move:53:9+235
    if ($t3) { goto L1; } else { goto L0; }

    // label L1 at .\sources\ConditionalBorrowChain.move:53:25+9
L1:

    // $t4 := borrow_field<0xbc::ProphecyBenchmark3Levels::Node3>.v0($t0) at .\sources\ConditionalBorrowChain.move:53:25+9
    assume {:print "$at(3,1722,1731)"} true;
    $t4 := $ChildMutation($t0, 0, $Dereference($t0)->$v0);

    // trace_return[0]($t4) at .\sources\ConditionalBorrowChain.move:53:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node2' := $Dereference($t4);
    assume {:print "$track_return(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels_Node2';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:53:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node3' := $Dereference($t0);
    assume {:print "$track_local(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node3'} $temp_0'$bc_ProphecyBenchmark3Levels_Node3' == $temp_0'$bc_ProphecyBenchmark3Levels_Node3';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:53:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node3' := $Dereference($t0);
    assume {:print "$track_local(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node3'} $temp_0'$bc_ProphecyBenchmark3Levels_Node3' == $temp_0'$bc_ProphecyBenchmark3Levels_Node3';

    // $t5 := move($t4) at .\sources\ConditionalBorrowChain.move:53:9+235
    $t5 := $t4;

    // goto L12 at .\sources\ConditionalBorrowChain.move:53:9+235
    goto L12;

    // label L0 at .\sources\ConditionalBorrowChain.move:53:46+3
L0:

    // $t6 := 1 at .\sources\ConditionalBorrowChain.move:53:53+1
    assume {:print "$at(3,1750,1751)"} true;
    $t6 := 1;
    assume $IsValid'u64'($t6);

    // $t7 := ==($t1, $t6) at .\sources\ConditionalBorrowChain.move:53:46+8
    $t7 := $IsEqual'u64'($t1, $t6);

    // if ($t7) goto L3 else goto L2 at .\sources\ConditionalBorrowChain.move:53:42+202
    if ($t7) { goto L3; } else { goto L2; }

    // label L3 at .\sources\ConditionalBorrowChain.move:53:58+9
L3:

    // $t8 := borrow_field<0xbc::ProphecyBenchmark3Levels::Node3>.v1($t0) at .\sources\ConditionalBorrowChain.move:53:58+9
    assume {:print "$at(3,1755,1764)"} true;
    $t8 := $ChildMutation($t0, 1, $Dereference($t0)->$v1);

    // trace_return[0]($t8) at .\sources\ConditionalBorrowChain.move:53:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node2' := $Dereference($t8);
    assume {:print "$track_return(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels_Node2';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:53:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node3' := $Dereference($t0);
    assume {:print "$track_local(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node3'} $temp_0'$bc_ProphecyBenchmark3Levels_Node3' == $temp_0'$bc_ProphecyBenchmark3Levels_Node3';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:53:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node3' := $Dereference($t0);
    assume {:print "$track_local(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node3'} $temp_0'$bc_ProphecyBenchmark3Levels_Node3' == $temp_0'$bc_ProphecyBenchmark3Levels_Node3';

    // $t5 := move($t8) at .\sources\ConditionalBorrowChain.move:53:9+235
    $t5 := $t8;

    // goto L12 at .\sources\ConditionalBorrowChain.move:53:9+235
    goto L12;

    // label L2 at .\sources\ConditionalBorrowChain.move:54:18+3
    assume {:print "$at(3,1784,1787)"} true;
L2:

    // $t9 := 2 at .\sources\ConditionalBorrowChain.move:54:25+1
    assume {:print "$at(3,1791,1792)"} true;
    $t9 := 2;
    assume $IsValid'u64'($t9);

    // $t10 := ==($t1, $t9) at .\sources\ConditionalBorrowChain.move:54:18+8
    $t10 := $IsEqual'u64'($t1, $t9);

    // if ($t10) goto L5 else goto L4 at .\sources\ConditionalBorrowChain.move:54:14+161
    if ($t10) { goto L5; } else { goto L4; }

    // label L5 at .\sources\ConditionalBorrowChain.move:54:30+9
L5:

    // $t11 := borrow_field<0xbc::ProphecyBenchmark3Levels::Node3>.v2($t0) at .\sources\ConditionalBorrowChain.move:54:30+9
    assume {:print "$at(3,1796,1805)"} true;
    $t11 := $ChildMutation($t0, 2, $Dereference($t0)->$v2);

    // trace_return[0]($t11) at .\sources\ConditionalBorrowChain.move:53:9+235
    assume {:print "$at(3,1706,1941)"} true;
    $temp_0'$bc_ProphecyBenchmark3Levels_Node2' := $Dereference($t11);
    assume {:print "$track_return(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels_Node2';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:53:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node3' := $Dereference($t0);
    assume {:print "$track_local(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node3'} $temp_0'$bc_ProphecyBenchmark3Levels_Node3' == $temp_0'$bc_ProphecyBenchmark3Levels_Node3';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:53:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node3' := $Dereference($t0);
    assume {:print "$track_local(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node3'} $temp_0'$bc_ProphecyBenchmark3Levels_Node3' == $temp_0'$bc_ProphecyBenchmark3Levels_Node3';

    // $t5 := move($t11) at .\sources\ConditionalBorrowChain.move:53:9+235
    $t5 := $t11;

    // goto L12 at .\sources\ConditionalBorrowChain.move:53:9+235
    goto L12;

    // label L4 at .\sources\ConditionalBorrowChain.move:54:51+3
    assume {:print "$at(3,1817,1820)"} true;
L4:

    // $t12 := 3 at .\sources\ConditionalBorrowChain.move:54:58+1
    assume {:print "$at(3,1824,1825)"} true;
    $t12 := 3;
    assume $IsValid'u64'($t12);

    // $t13 := ==($t1, $t12) at .\sources\ConditionalBorrowChain.move:54:51+8
    $t13 := $IsEqual'u64'($t1, $t12);

    // if ($t13) goto L7 else goto L6 at .\sources\ConditionalBorrowChain.move:54:47+128
    if ($t13) { goto L7; } else { goto L6; }

    // label L7 at .\sources\ConditionalBorrowChain.move:54:63+9
L7:

    // $t14 := borrow_field<0xbc::ProphecyBenchmark3Levels::Node3>.v3($t0) at .\sources\ConditionalBorrowChain.move:54:63+9
    assume {:print "$at(3,1829,1838)"} true;
    $t14 := $ChildMutation($t0, 3, $Dereference($t0)->$v3);

    // trace_return[0]($t14) at .\sources\ConditionalBorrowChain.move:53:9+235
    assume {:print "$at(3,1706,1941)"} true;
    $temp_0'$bc_ProphecyBenchmark3Levels_Node2' := $Dereference($t14);
    assume {:print "$track_return(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels_Node2';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:53:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node3' := $Dereference($t0);
    assume {:print "$track_local(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node3'} $temp_0'$bc_ProphecyBenchmark3Levels_Node3' == $temp_0'$bc_ProphecyBenchmark3Levels_Node3';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:53:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node3' := $Dereference($t0);
    assume {:print "$track_local(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node3'} $temp_0'$bc_ProphecyBenchmark3Levels_Node3' == $temp_0'$bc_ProphecyBenchmark3Levels_Node3';

    // $t5 := move($t14) at .\sources\ConditionalBorrowChain.move:53:9+235
    $t5 := $t14;

    // goto L12 at .\sources\ConditionalBorrowChain.move:53:9+235
    goto L12;

    // label L6 at .\sources\ConditionalBorrowChain.move:55:18+3
    assume {:print "$at(3,1858,1861)"} true;
L6:

    // $t15 := 4 at .\sources\ConditionalBorrowChain.move:55:25+1
    assume {:print "$at(3,1865,1866)"} true;
    $t15 := 4;
    assume $IsValid'u64'($t15);

    // $t16 := ==($t1, $t15) at .\sources\ConditionalBorrowChain.move:55:18+8
    $t16 := $IsEqual'u64'($t1, $t15);

    // if ($t16) goto L9 else goto L8 at .\sources\ConditionalBorrowChain.move:55:14+87
    if ($t16) { goto L9; } else { goto L8; }

    // label L9 at .\sources\ConditionalBorrowChain.move:55:30+9
L9:

    // $t17 := borrow_field<0xbc::ProphecyBenchmark3Levels::Node3>.v4($t0) at .\sources\ConditionalBorrowChain.move:55:30+9
    assume {:print "$at(3,1870,1879)"} true;
    $t17 := $ChildMutation($t0, 4, $Dereference($t0)->$v4);

    // trace_return[0]($t17) at .\sources\ConditionalBorrowChain.move:53:9+235
    assume {:print "$at(3,1706,1941)"} true;
    $temp_0'$bc_ProphecyBenchmark3Levels_Node2' := $Dereference($t17);
    assume {:print "$track_return(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels_Node2';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:53:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node3' := $Dereference($t0);
    assume {:print "$track_local(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node3'} $temp_0'$bc_ProphecyBenchmark3Levels_Node3' == $temp_0'$bc_ProphecyBenchmark3Levels_Node3';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:53:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node3' := $Dereference($t0);
    assume {:print "$track_local(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node3'} $temp_0'$bc_ProphecyBenchmark3Levels_Node3' == $temp_0'$bc_ProphecyBenchmark3Levels_Node3';

    // $t5 := move($t17) at .\sources\ConditionalBorrowChain.move:53:9+235
    $t5 := $t17;

    // goto L12 at .\sources\ConditionalBorrowChain.move:53:9+235
    goto L12;

    // label L8 at .\sources\ConditionalBorrowChain.move:55:51+3
    assume {:print "$at(3,1891,1894)"} true;
L8:

    // $t18 := 5 at .\sources\ConditionalBorrowChain.move:55:58+1
    assume {:print "$at(3,1898,1899)"} true;
    $t18 := 5;
    assume $IsValid'u64'($t18);

    // $t19 := ==($t1, $t18) at .\sources\ConditionalBorrowChain.move:55:51+8
    $t19 := $IsEqual'u64'($t1, $t18);

    // if ($t19) goto L11 else goto L10 at .\sources\ConditionalBorrowChain.move:55:47+54
    if ($t19) { goto L11; } else { goto L10; }

    // label L11 at .\sources\ConditionalBorrowChain.move:55:63+9
L11:

    // $t20 := borrow_field<0xbc::ProphecyBenchmark3Levels::Node3>.v5($t0) at .\sources\ConditionalBorrowChain.move:55:63+9
    assume {:print "$at(3,1903,1912)"} true;
    $t20 := $ChildMutation($t0, 5, $Dereference($t0)->$v5);

    // trace_return[0]($t20) at .\sources\ConditionalBorrowChain.move:53:9+235
    assume {:print "$at(3,1706,1941)"} true;
    $temp_0'$bc_ProphecyBenchmark3Levels_Node2' := $Dereference($t20);
    assume {:print "$track_return(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels_Node2';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:53:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node3' := $Dereference($t0);
    assume {:print "$track_local(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node3'} $temp_0'$bc_ProphecyBenchmark3Levels_Node3' == $temp_0'$bc_ProphecyBenchmark3Levels_Node3';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:53:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node3' := $Dereference($t0);
    assume {:print "$track_local(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node3'} $temp_0'$bc_ProphecyBenchmark3Levels_Node3' == $temp_0'$bc_ProphecyBenchmark3Levels_Node3';

    // $t5 := move($t20) at .\sources\ConditionalBorrowChain.move:53:9+235
    $t5 := $t20;

    // goto L12 at .\sources\ConditionalBorrowChain.move:53:9+235
    goto L12;

    // label L10 at .\sources\ConditionalBorrowChain.move:56:16+9
    assume {:print "$at(3,1930,1939)"} true;
L10:

    // $t21 := borrow_field<0xbc::ProphecyBenchmark3Levels::Node3>.v6($t0) at .\sources\ConditionalBorrowChain.move:56:16+9
    assume {:print "$at(3,1930,1939)"} true;
    $t21 := $ChildMutation($t0, 6, $Dereference($t0)->$v6);

    // trace_return[0]($t21) at .\sources\ConditionalBorrowChain.move:53:9+235
    assume {:print "$at(3,1706,1941)"} true;
    $temp_0'$bc_ProphecyBenchmark3Levels_Node2' := $Dereference($t21);
    assume {:print "$track_return(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels_Node2';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:53:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node3' := $Dereference($t0);
    assume {:print "$track_local(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node3'} $temp_0'$bc_ProphecyBenchmark3Levels_Node3' == $temp_0'$bc_ProphecyBenchmark3Levels_Node3';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:53:9+235
    $temp_0'$bc_ProphecyBenchmark3Levels_Node3' := $Dereference($t0);
    assume {:print "$track_local(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels_Node3'} $temp_0'$bc_ProphecyBenchmark3Levels_Node3' == $temp_0'$bc_ProphecyBenchmark3Levels_Node3';

    // $t5 := move($t21) at .\sources\ConditionalBorrowChain.move:53:9+235
    $t5 := $t21;

    // label L12 at .\sources\ConditionalBorrowChain.move:57:5+1
    assume {:print "$at(3,1946,1947)"} true;
L12:

    // return $t5 at .\sources\ConditionalBorrowChain.move:57:5+1
    assume {:print "$at(3,1946,1947)"} true;
    $ret0 := $t5;
    $ret1 := $t0;
    return;

}
