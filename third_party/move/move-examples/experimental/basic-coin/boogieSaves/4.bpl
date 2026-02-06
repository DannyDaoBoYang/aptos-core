
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


function $Arbitrary_value_of'$bc_ProphecyBenchmark3Levels4Fields_Node1'(): $bc_ProphecyBenchmark3Levels4Fields_Node1;



function $Arbitrary_value_of'$bc_ProphecyBenchmark3Levels4Fields_Node2'(): $bc_ProphecyBenchmark3Levels4Fields_Node2;



function $Arbitrary_value_of'$bc_ProphecyBenchmark3Levels4Fields_Node3'(): $bc_ProphecyBenchmark3Levels4Fields_Node3;



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


// struct ProphecyBenchmark3Levels4Fields::Node1 at .\sources\ConditionalBorrowChain.move:8:5+131
datatype $bc_ProphecyBenchmark3Levels4Fields_Node1 {
    $bc_ProphecyBenchmark3Levels4Fields_Node1($v0: int, $v1: int, $v2: int, $v3: int, $v4: int, $v5: int, $v6: int, $v7: int)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v0(s: $bc_ProphecyBenchmark3Levels4Fields_Node1, x: int): $bc_ProphecyBenchmark3Levels4Fields_Node1 {
    $bc_ProphecyBenchmark3Levels4Fields_Node1(x, s->$v1, s->$v2, s->$v3, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v1(s: $bc_ProphecyBenchmark3Levels4Fields_Node1, x: int): $bc_ProphecyBenchmark3Levels4Fields_Node1 {
    $bc_ProphecyBenchmark3Levels4Fields_Node1(s->$v0, x, s->$v2, s->$v3, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v2(s: $bc_ProphecyBenchmark3Levels4Fields_Node1, x: int): $bc_ProphecyBenchmark3Levels4Fields_Node1 {
    $bc_ProphecyBenchmark3Levels4Fields_Node1(s->$v0, s->$v1, x, s->$v3, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v3(s: $bc_ProphecyBenchmark3Levels4Fields_Node1, x: int): $bc_ProphecyBenchmark3Levels4Fields_Node1 {
    $bc_ProphecyBenchmark3Levels4Fields_Node1(s->$v0, s->$v1, s->$v2, x, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v4(s: $bc_ProphecyBenchmark3Levels4Fields_Node1, x: int): $bc_ProphecyBenchmark3Levels4Fields_Node1 {
    $bc_ProphecyBenchmark3Levels4Fields_Node1(s->$v0, s->$v1, s->$v2, s->$v3, x, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v5(s: $bc_ProphecyBenchmark3Levels4Fields_Node1, x: int): $bc_ProphecyBenchmark3Levels4Fields_Node1 {
    $bc_ProphecyBenchmark3Levels4Fields_Node1(s->$v0, s->$v1, s->$v2, s->$v3, s->$v4, x, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v6(s: $bc_ProphecyBenchmark3Levels4Fields_Node1, x: int): $bc_ProphecyBenchmark3Levels4Fields_Node1 {
    $bc_ProphecyBenchmark3Levels4Fields_Node1(s->$v0, s->$v1, s->$v2, s->$v3, s->$v4, s->$v5, x, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v7(s: $bc_ProphecyBenchmark3Levels4Fields_Node1, x: int): $bc_ProphecyBenchmark3Levels4Fields_Node1 {
    $bc_ProphecyBenchmark3Levels4Fields_Node1(s->$v0, s->$v1, s->$v2, s->$v3, s->$v4, s->$v5, s->$v6, x)
}
function $IsValid'$bc_ProphecyBenchmark3Levels4Fields_Node1'(s: $bc_ProphecyBenchmark3Levels4Fields_Node1): bool {
    $IsValid'u64'(s->$v0)
      && $IsValid'u64'(s->$v1)
      && $IsValid'u64'(s->$v2)
      && $IsValid'u64'(s->$v3)
      && $IsValid'u64'(s->$v4)
      && $IsValid'u64'(s->$v5)
      && $IsValid'u64'(s->$v6)
      && $IsValid'u64'(s->$v7)
}
function {:inline} $IsEqual'$bc_ProphecyBenchmark3Levels4Fields_Node1'(s1: $bc_ProphecyBenchmark3Levels4Fields_Node1, s2: $bc_ProphecyBenchmark3Levels4Fields_Node1): bool {
    s1 == s2
}

// struct ProphecyBenchmark3Levels4Fields::Node2 at .\sources\ConditionalBorrowChain.move:14:5+147
datatype $bc_ProphecyBenchmark3Levels4Fields_Node2 {
    $bc_ProphecyBenchmark3Levels4Fields_Node2($v0: $bc_ProphecyBenchmark3Levels4Fields_Node1, $v1: $bc_ProphecyBenchmark3Levels4Fields_Node1, $v2: $bc_ProphecyBenchmark3Levels4Fields_Node1, $v3: $bc_ProphecyBenchmark3Levels4Fields_Node1, $v4: $bc_ProphecyBenchmark3Levels4Fields_Node1, $v5: $bc_ProphecyBenchmark3Levels4Fields_Node1, $v6: $bc_ProphecyBenchmark3Levels4Fields_Node1, $v7: $bc_ProphecyBenchmark3Levels4Fields_Node1)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v0(s: $bc_ProphecyBenchmark3Levels4Fields_Node2, x: $bc_ProphecyBenchmark3Levels4Fields_Node1): $bc_ProphecyBenchmark3Levels4Fields_Node2 {
    $bc_ProphecyBenchmark3Levels4Fields_Node2(x, s->$v1, s->$v2, s->$v3, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v1(s: $bc_ProphecyBenchmark3Levels4Fields_Node2, x: $bc_ProphecyBenchmark3Levels4Fields_Node1): $bc_ProphecyBenchmark3Levels4Fields_Node2 {
    $bc_ProphecyBenchmark3Levels4Fields_Node2(s->$v0, x, s->$v2, s->$v3, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v2(s: $bc_ProphecyBenchmark3Levels4Fields_Node2, x: $bc_ProphecyBenchmark3Levels4Fields_Node1): $bc_ProphecyBenchmark3Levels4Fields_Node2 {
    $bc_ProphecyBenchmark3Levels4Fields_Node2(s->$v0, s->$v1, x, s->$v3, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v3(s: $bc_ProphecyBenchmark3Levels4Fields_Node2, x: $bc_ProphecyBenchmark3Levels4Fields_Node1): $bc_ProphecyBenchmark3Levels4Fields_Node2 {
    $bc_ProphecyBenchmark3Levels4Fields_Node2(s->$v0, s->$v1, s->$v2, x, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v4(s: $bc_ProphecyBenchmark3Levels4Fields_Node2, x: $bc_ProphecyBenchmark3Levels4Fields_Node1): $bc_ProphecyBenchmark3Levels4Fields_Node2 {
    $bc_ProphecyBenchmark3Levels4Fields_Node2(s->$v0, s->$v1, s->$v2, s->$v3, x, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v5(s: $bc_ProphecyBenchmark3Levels4Fields_Node2, x: $bc_ProphecyBenchmark3Levels4Fields_Node1): $bc_ProphecyBenchmark3Levels4Fields_Node2 {
    $bc_ProphecyBenchmark3Levels4Fields_Node2(s->$v0, s->$v1, s->$v2, s->$v3, s->$v4, x, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v6(s: $bc_ProphecyBenchmark3Levels4Fields_Node2, x: $bc_ProphecyBenchmark3Levels4Fields_Node1): $bc_ProphecyBenchmark3Levels4Fields_Node2 {
    $bc_ProphecyBenchmark3Levels4Fields_Node2(s->$v0, s->$v1, s->$v2, s->$v3, s->$v4, s->$v5, x, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v7(s: $bc_ProphecyBenchmark3Levels4Fields_Node2, x: $bc_ProphecyBenchmark3Levels4Fields_Node1): $bc_ProphecyBenchmark3Levels4Fields_Node2 {
    $bc_ProphecyBenchmark3Levels4Fields_Node2(s->$v0, s->$v1, s->$v2, s->$v3, s->$v4, s->$v5, s->$v6, x)
}
function $IsValid'$bc_ProphecyBenchmark3Levels4Fields_Node2'(s: $bc_ProphecyBenchmark3Levels4Fields_Node2): bool {
    $IsValid'$bc_ProphecyBenchmark3Levels4Fields_Node1'(s->$v0)
      && $IsValid'$bc_ProphecyBenchmark3Levels4Fields_Node1'(s->$v1)
      && $IsValid'$bc_ProphecyBenchmark3Levels4Fields_Node1'(s->$v2)
      && $IsValid'$bc_ProphecyBenchmark3Levels4Fields_Node1'(s->$v3)
      && $IsValid'$bc_ProphecyBenchmark3Levels4Fields_Node1'(s->$v4)
      && $IsValid'$bc_ProphecyBenchmark3Levels4Fields_Node1'(s->$v5)
      && $IsValid'$bc_ProphecyBenchmark3Levels4Fields_Node1'(s->$v6)
      && $IsValid'$bc_ProphecyBenchmark3Levels4Fields_Node1'(s->$v7)
}
function {:inline} $IsEqual'$bc_ProphecyBenchmark3Levels4Fields_Node2'(s1: $bc_ProphecyBenchmark3Levels4Fields_Node2, s2: $bc_ProphecyBenchmark3Levels4Fields_Node2): bool {
    s1 == s2
}

// struct ProphecyBenchmark3Levels4Fields::Node3 at .\sources\ConditionalBorrowChain.move:20:5+147
datatype $bc_ProphecyBenchmark3Levels4Fields_Node3 {
    $bc_ProphecyBenchmark3Levels4Fields_Node3($v0: $bc_ProphecyBenchmark3Levels4Fields_Node2, $v1: $bc_ProphecyBenchmark3Levels4Fields_Node2, $v2: $bc_ProphecyBenchmark3Levels4Fields_Node2, $v3: $bc_ProphecyBenchmark3Levels4Fields_Node2, $v4: $bc_ProphecyBenchmark3Levels4Fields_Node2, $v5: $bc_ProphecyBenchmark3Levels4Fields_Node2, $v6: $bc_ProphecyBenchmark3Levels4Fields_Node2, $v7: $bc_ProphecyBenchmark3Levels4Fields_Node2)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v0(s: $bc_ProphecyBenchmark3Levels4Fields_Node3, x: $bc_ProphecyBenchmark3Levels4Fields_Node2): $bc_ProphecyBenchmark3Levels4Fields_Node3 {
    $bc_ProphecyBenchmark3Levels4Fields_Node3(x, s->$v1, s->$v2, s->$v3, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v1(s: $bc_ProphecyBenchmark3Levels4Fields_Node3, x: $bc_ProphecyBenchmark3Levels4Fields_Node2): $bc_ProphecyBenchmark3Levels4Fields_Node3 {
    $bc_ProphecyBenchmark3Levels4Fields_Node3(s->$v0, x, s->$v2, s->$v3, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v2(s: $bc_ProphecyBenchmark3Levels4Fields_Node3, x: $bc_ProphecyBenchmark3Levels4Fields_Node2): $bc_ProphecyBenchmark3Levels4Fields_Node3 {
    $bc_ProphecyBenchmark3Levels4Fields_Node3(s->$v0, s->$v1, x, s->$v3, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v3(s: $bc_ProphecyBenchmark3Levels4Fields_Node3, x: $bc_ProphecyBenchmark3Levels4Fields_Node2): $bc_ProphecyBenchmark3Levels4Fields_Node3 {
    $bc_ProphecyBenchmark3Levels4Fields_Node3(s->$v0, s->$v1, s->$v2, x, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v4(s: $bc_ProphecyBenchmark3Levels4Fields_Node3, x: $bc_ProphecyBenchmark3Levels4Fields_Node2): $bc_ProphecyBenchmark3Levels4Fields_Node3 {
    $bc_ProphecyBenchmark3Levels4Fields_Node3(s->$v0, s->$v1, s->$v2, s->$v3, x, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v5(s: $bc_ProphecyBenchmark3Levels4Fields_Node3, x: $bc_ProphecyBenchmark3Levels4Fields_Node2): $bc_ProphecyBenchmark3Levels4Fields_Node3 {
    $bc_ProphecyBenchmark3Levels4Fields_Node3(s->$v0, s->$v1, s->$v2, s->$v3, s->$v4, x, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v6(s: $bc_ProphecyBenchmark3Levels4Fields_Node3, x: $bc_ProphecyBenchmark3Levels4Fields_Node2): $bc_ProphecyBenchmark3Levels4Fields_Node3 {
    $bc_ProphecyBenchmark3Levels4Fields_Node3(s->$v0, s->$v1, s->$v2, s->$v3, s->$v4, s->$v5, x, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v7(s: $bc_ProphecyBenchmark3Levels4Fields_Node3, x: $bc_ProphecyBenchmark3Levels4Fields_Node2): $bc_ProphecyBenchmark3Levels4Fields_Node3 {
    $bc_ProphecyBenchmark3Levels4Fields_Node3(s->$v0, s->$v1, s->$v2, s->$v3, s->$v4, s->$v5, s->$v6, x)
}
function $IsValid'$bc_ProphecyBenchmark3Levels4Fields_Node3'(s: $bc_ProphecyBenchmark3Levels4Fields_Node3): bool {
    $IsValid'$bc_ProphecyBenchmark3Levels4Fields_Node2'(s->$v0)
      && $IsValid'$bc_ProphecyBenchmark3Levels4Fields_Node2'(s->$v1)
      && $IsValid'$bc_ProphecyBenchmark3Levels4Fields_Node2'(s->$v2)
      && $IsValid'$bc_ProphecyBenchmark3Levels4Fields_Node2'(s->$v3)
      && $IsValid'$bc_ProphecyBenchmark3Levels4Fields_Node2'(s->$v4)
      && $IsValid'$bc_ProphecyBenchmark3Levels4Fields_Node2'(s->$v5)
      && $IsValid'$bc_ProphecyBenchmark3Levels4Fields_Node2'(s->$v6)
      && $IsValid'$bc_ProphecyBenchmark3Levels4Fields_Node2'(s->$v7)
}
function {:inline} $IsEqual'$bc_ProphecyBenchmark3Levels4Fields_Node3'(s1: $bc_ProphecyBenchmark3Levels4Fields_Node3, s2: $bc_ProphecyBenchmark3Levels4Fields_Node3): bool {
    s1 == s2
}

// fun ProphecyBenchmark3Levels4Fields::benchmark_from_scratch [verification] at .\sources\ConditionalBorrowChain.move:85:5+500
procedure {:timeLimit 40} $bc_ProphecyBenchmark3Levels4Fields_benchmark_from_scratch$verify(_$t0: int, _$t1: int, _$t2: int) returns ($ret0: $bc_ProphecyBenchmark3Levels4Fields_Node3)
{
    // declare local variables
    var $t3: $bc_ProphecyBenchmark3Levels4Fields_Node3;
    var $t4: $Mutation (int);
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: int;
    var $t10: int;
    var $t11: int;
    var $t12: $Mutation ($bc_ProphecyBenchmark3Levels4Fields_Node3);
    var $t13: $Mutation ($bc_ProphecyBenchmark3Levels4Fields_Node2);
    var $t14: $Mutation ($bc_ProphecyBenchmark3Levels4Fields_Node1);
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
    var $t339: $bc_ProphecyBenchmark3Levels4Fields_Node3;
    var $t0: int;
    var $t1: int;
    var $t2: int;
    var $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3': $bc_ProphecyBenchmark3Levels4Fields_Node3;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at .\sources\ConditionalBorrowChain.move:85:5+1
    assume {:print "$at(3,2745,2746)"} true;
    assume $IsValid'u64'($t0);

    // assume WellFormed($t1) at .\sources\ConditionalBorrowChain.move:85:5+1
    assume $IsValid'u64'($t1);

    // assume WellFormed($t2) at .\sources\ConditionalBorrowChain.move:85:5+1
    assume $IsValid'u64'($t2);

    // trace_local[c3]($t0) at .\sources\ConditionalBorrowChain.move:85:5+1
    assume {:print "$track_local(2,0,0):", $t0} $t0 == $t0;

    // trace_local[c2]($t1) at .\sources\ConditionalBorrowChain.move:85:5+1
    assume {:print "$track_local(2,0,1):", $t1} $t1 == $t1;

    // trace_local[c1]($t2) at .\sources\ConditionalBorrowChain.move:85:5+1
    assume {:print "$track_local(2,0,2):", $t2} $t2 == $t2;

    // $t3 := ProphecyBenchmark3Levels4Fields::new_node3() on_abort goto L130 with $t5 at .\sources\ConditionalBorrowChain.move:88:20+11
    assume {:print "$at(3,2848,2859)"} true;
    call $t3 := $bc_ProphecyBenchmark3Levels4Fields_new_node3();
    if ($abort_flag) {
        assume {:print "$at(3,2848,2859)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,0):", $t5} $t5 == $t5;
        goto L130;
    }

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:88:20+11
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // $t6 := 8 at .\sources\ConditionalBorrowChain.move:90:25+1
    assume {:print "$at(3,2894,2895)"} true;
    $t6 := 8;
    assume $IsValid'u64'($t6);

    // $t7 := %($t0, $t6) on_abort goto L130 with $t5 at .\sources\ConditionalBorrowChain.move:90:20+6
    call $t7 := $Mod($t0, $t6);
    if ($abort_flag) {
        assume {:print "$at(3,2889,2895)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,0):", $t5} $t5 == $t5;
        goto L130;
    }

    // trace_local[c3]($t7) at .\sources\ConditionalBorrowChain.move:90:20+6
    assume {:print "$track_local(2,0,0):", $t7} $t7 == $t7;

    // $t8 := 8 at .\sources\ConditionalBorrowChain.move:91:25+1
    assume {:print "$at(3,2921,2922)"} true;
    $t8 := 8;
    assume $IsValid'u64'($t8);

    // $t9 := %($t1, $t8) on_abort goto L130 with $t5 at .\sources\ConditionalBorrowChain.move:91:20+6
    call $t9 := $Mod($t1, $t8);
    if ($abort_flag) {
        assume {:print "$at(3,2916,2922)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,0):", $t5} $t5 == $t5;
        goto L130;
    }

    // trace_local[c2]($t9) at .\sources\ConditionalBorrowChain.move:91:20+6
    assume {:print "$track_local(2,0,1):", $t9} $t9 == $t9;

    // $t10 := 8 at .\sources\ConditionalBorrowChain.move:92:25+1
    assume {:print "$at(3,2948,2949)"} true;
    $t10 := 8;
    assume $IsValid'u64'($t10);

    // $t11 := %($t2, $t10) on_abort goto L130 with $t5 at .\sources\ConditionalBorrowChain.move:92:20+6
    call $t11 := $Mod($t2, $t10);
    if ($abort_flag) {
        assume {:print "$at(3,2943,2949)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,0):", $t5} $t5 == $t5;
        goto L130;
    }

    // trace_local[c1]($t11) at .\sources\ConditionalBorrowChain.move:92:20+6
    assume {:print "$track_local(2,0,2):", $t11} $t11 == $t11;

    // $t12 := borrow_local($t3) at .\sources\ConditionalBorrowChain.move:94:22+9
    assume {:print "$at(3,2973,2982)"} true;
    $t12 := $Mutation($Local(3), EmptyVec(), $t3);

    // $t13 := ProphecyBenchmark3Levels4Fields::select_n2($t12, $t7) on_abort goto L130 with $t5 at .\sources\ConditionalBorrowChain.move:97:22+23
    assume {:print "$at(3,3070,3093)"} true;
    call $t13,$t12 := $bc_ProphecyBenchmark3Levels4Fields_select_n2($t12, $t7);
    if ($abort_flag) {
        assume {:print "$at(3,3070,3093)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,0):", $t5} $t5 == $t5;
        goto L130;
    }

    // $t14 := ProphecyBenchmark3Levels4Fields::select_n1($t13, $t9) on_abort goto L130 with $t5 at .\sources\ConditionalBorrowChain.move:98:22+23
    assume {:print "$at(3,3116,3139)"} true;
    call $t14,$t13 := $bc_ProphecyBenchmark3Levels4Fields_select_n1($t13, $t9);
    if ($abort_flag) {
        assume {:print "$at(3,3116,3139)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,0):", $t5} $t5 == $t5;
        goto L130;
    }

    // $t15 := ProphecyBenchmark3Levels4Fields::select_leaf($t14, $t11) on_abort goto L130 with $t5 at .\sources\ConditionalBorrowChain.move:99:24+25
    assume {:print "$at(3,3164,3189)"} true;
    call $t15,$t14 := $bc_ProphecyBenchmark3Levels4Fields_select_leaf($t14, $t11);
    if ($abort_flag) {
        assume {:print "$at(3,3164,3189)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,0):", $t5} $t5 == $t5;
        goto L130;
    }

    // trace_local[leaf_ref]($t15) at .\sources\ConditionalBorrowChain.move:99:24+25
    $temp_0'u64' := $Dereference($t15);
    assume {:print "$track_local(2,0,4):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t16 := read_ref($t15) at .\sources\ConditionalBorrowChain.move:100:21+9
    assume {:print "$at(3,3211,3220)"} true;
    $t16 := $Dereference($t15);

    // $t17 := 1 at .\sources\ConditionalBorrowChain.move:100:33+1
    $t17 := 1;
    assume $IsValid'u64'($t17);

    // $t18 := +($t16, $t17) on_abort goto L130 with $t5 at .\sources\ConditionalBorrowChain.move:100:21+13
    call $t18 := $AddU64($t16, $t17);
    if ($abort_flag) {
        assume {:print "$at(3,3211,3224)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,0):", $t5} $t5 == $t5;
        goto L130;
    }

    // write_ref($t15, $t18) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t15 := $UpdateMutation($t15, $t18);

    // $t19 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t19 := $IsParentMutation($t14, 0, $t15);

    // $t20 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t20 := $IsParentMutation($t13, 0, $t14);

    // $t21 := &&($t19, $t20) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t21 := $And($t19, $t20);

    // $t22 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t22 := $IsParentMutation($t12, 0, $t13);

    // $t23 := &&($t21, $t22) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t23 := $And($t21, $t22);

    // if ($t23) goto L1 else goto L2 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t23) { goto L1; } else { goto L2; }

    // label L1 at .\sources\ConditionalBorrowChain.move:100:9+25
L1:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L2 at .\sources\ConditionalBorrowChain.move:100:9+25
L2:

    // $t24 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t24 := $IsParentMutation($t14, 0, $t15);

    // $t25 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t25 := $IsParentMutation($t13, 0, $t14);

    // $t26 := &&($t24, $t25) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t26 := $And($t24, $t25);

    // $t27 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t27 := $IsParentMutation($t12, 1, $t13);

    // $t28 := &&($t26, $t27) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t28 := $And($t26, $t27);

    // if ($t28) goto L3 else goto L4 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t28) { goto L3; } else { goto L4; }

    // label L3 at .\sources\ConditionalBorrowChain.move:100:9+25
L3:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L4 at .\sources\ConditionalBorrowChain.move:100:9+25
L4:

    // $t29 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t29 := $IsParentMutation($t14, 0, $t15);

    // $t30 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t30 := $IsParentMutation($t13, 0, $t14);

    // $t31 := &&($t29, $t30) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t31 := $And($t29, $t30);

    // $t32 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t32 := $IsParentMutation($t12, 2, $t13);

    // $t33 := &&($t31, $t32) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t33 := $And($t31, $t32);

    // if ($t33) goto L5 else goto L6 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t33) { goto L5; } else { goto L6; }

    // label L5 at .\sources\ConditionalBorrowChain.move:100:9+25
L5:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L6 at .\sources\ConditionalBorrowChain.move:100:9+25
L6:

    // $t34 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t34 := $IsParentMutation($t14, 0, $t15);

    // $t35 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t35 := $IsParentMutation($t13, 0, $t14);

    // $t36 := &&($t34, $t35) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t36 := $And($t34, $t35);

    // $t37 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t37 := $IsParentMutation($t12, 3, $t13);

    // $t38 := &&($t36, $t37) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t38 := $And($t36, $t37);

    // if ($t38) goto L7 else goto L8 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t38) { goto L7; } else { goto L8; }

    // label L7 at .\sources\ConditionalBorrowChain.move:100:9+25
L7:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L8 at .\sources\ConditionalBorrowChain.move:100:9+25
L8:

    // $t39 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t39 := $IsParentMutation($t14, 0, $t15);

    // $t40 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t40 := $IsParentMutation($t13, 1, $t14);

    // $t41 := &&($t39, $t40) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t41 := $And($t39, $t40);

    // $t42 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t42 := $IsParentMutation($t12, 0, $t13);

    // $t43 := &&($t41, $t42) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t43 := $And($t41, $t42);

    // if ($t43) goto L9 else goto L10 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t43) { goto L9; } else { goto L10; }

    // label L9 at .\sources\ConditionalBorrowChain.move:100:9+25
L9:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L10 at .\sources\ConditionalBorrowChain.move:100:9+25
L10:

    // $t44 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t44 := $IsParentMutation($t14, 0, $t15);

    // $t45 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t45 := $IsParentMutation($t13, 1, $t14);

    // $t46 := &&($t44, $t45) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t46 := $And($t44, $t45);

    // $t47 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t47 := $IsParentMutation($t12, 1, $t13);

    // $t48 := &&($t46, $t47) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t48 := $And($t46, $t47);

    // if ($t48) goto L11 else goto L12 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t48) { goto L11; } else { goto L12; }

    // label L11 at .\sources\ConditionalBorrowChain.move:100:9+25
L11:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L12 at .\sources\ConditionalBorrowChain.move:100:9+25
L12:

    // $t49 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t49 := $IsParentMutation($t14, 0, $t15);

    // $t50 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t50 := $IsParentMutation($t13, 1, $t14);

    // $t51 := &&($t49, $t50) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t51 := $And($t49, $t50);

    // $t52 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t52 := $IsParentMutation($t12, 2, $t13);

    // $t53 := &&($t51, $t52) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t53 := $And($t51, $t52);

    // if ($t53) goto L13 else goto L14 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t53) { goto L13; } else { goto L14; }

    // label L13 at .\sources\ConditionalBorrowChain.move:100:9+25
L13:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L14 at .\sources\ConditionalBorrowChain.move:100:9+25
L14:

    // $t54 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t54 := $IsParentMutation($t14, 0, $t15);

    // $t55 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t55 := $IsParentMutation($t13, 1, $t14);

    // $t56 := &&($t54, $t55) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t56 := $And($t54, $t55);

    // $t57 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t57 := $IsParentMutation($t12, 3, $t13);

    // $t58 := &&($t56, $t57) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t58 := $And($t56, $t57);

    // if ($t58) goto L15 else goto L16 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t58) { goto L15; } else { goto L16; }

    // label L15 at .\sources\ConditionalBorrowChain.move:100:9+25
L15:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L16 at .\sources\ConditionalBorrowChain.move:100:9+25
L16:

    // $t59 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t59 := $IsParentMutation($t14, 0, $t15);

    // $t60 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t60 := $IsParentMutation($t13, 2, $t14);

    // $t61 := &&($t59, $t60) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t61 := $And($t59, $t60);

    // $t62 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t62 := $IsParentMutation($t12, 0, $t13);

    // $t63 := &&($t61, $t62) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t63 := $And($t61, $t62);

    // if ($t63) goto L17 else goto L18 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t63) { goto L17; } else { goto L18; }

    // label L17 at .\sources\ConditionalBorrowChain.move:100:9+25
L17:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L18 at .\sources\ConditionalBorrowChain.move:100:9+25
L18:

    // $t64 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t64 := $IsParentMutation($t14, 0, $t15);

    // $t65 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t65 := $IsParentMutation($t13, 2, $t14);

    // $t66 := &&($t64, $t65) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t66 := $And($t64, $t65);

    // $t67 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t67 := $IsParentMutation($t12, 1, $t13);

    // $t68 := &&($t66, $t67) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t68 := $And($t66, $t67);

    // if ($t68) goto L19 else goto L20 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t68) { goto L19; } else { goto L20; }

    // label L19 at .\sources\ConditionalBorrowChain.move:100:9+25
L19:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L20 at .\sources\ConditionalBorrowChain.move:100:9+25
L20:

    // $t69 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t69 := $IsParentMutation($t14, 0, $t15);

    // $t70 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t70 := $IsParentMutation($t13, 2, $t14);

    // $t71 := &&($t69, $t70) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t71 := $And($t69, $t70);

    // $t72 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t72 := $IsParentMutation($t12, 2, $t13);

    // $t73 := &&($t71, $t72) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t73 := $And($t71, $t72);

    // if ($t73) goto L21 else goto L22 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t73) { goto L21; } else { goto L22; }

    // label L21 at .\sources\ConditionalBorrowChain.move:100:9+25
L21:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L22 at .\sources\ConditionalBorrowChain.move:100:9+25
L22:

    // $t74 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t74 := $IsParentMutation($t14, 0, $t15);

    // $t75 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t75 := $IsParentMutation($t13, 2, $t14);

    // $t76 := &&($t74, $t75) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t76 := $And($t74, $t75);

    // $t77 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t77 := $IsParentMutation($t12, 3, $t13);

    // $t78 := &&($t76, $t77) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t78 := $And($t76, $t77);

    // if ($t78) goto L23 else goto L24 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t78) { goto L23; } else { goto L24; }

    // label L23 at .\sources\ConditionalBorrowChain.move:100:9+25
L23:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L24 at .\sources\ConditionalBorrowChain.move:100:9+25
L24:

    // $t79 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t79 := $IsParentMutation($t14, 0, $t15);

    // $t80 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t80 := $IsParentMutation($t13, 3, $t14);

    // $t81 := &&($t79, $t80) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t81 := $And($t79, $t80);

    // $t82 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t82 := $IsParentMutation($t12, 0, $t13);

    // $t83 := &&($t81, $t82) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t83 := $And($t81, $t82);

    // if ($t83) goto L25 else goto L26 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t83) { goto L25; } else { goto L26; }

    // label L25 at .\sources\ConditionalBorrowChain.move:100:9+25
L25:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L26 at .\sources\ConditionalBorrowChain.move:100:9+25
L26:

    // $t84 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t84 := $IsParentMutation($t14, 0, $t15);

    // $t85 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t85 := $IsParentMutation($t13, 3, $t14);

    // $t86 := &&($t84, $t85) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t86 := $And($t84, $t85);

    // $t87 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t87 := $IsParentMutation($t12, 1, $t13);

    // $t88 := &&($t86, $t87) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t88 := $And($t86, $t87);

    // if ($t88) goto L27 else goto L28 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t88) { goto L27; } else { goto L28; }

    // label L27 at .\sources\ConditionalBorrowChain.move:100:9+25
L27:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L28 at .\sources\ConditionalBorrowChain.move:100:9+25
L28:

    // $t89 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t89 := $IsParentMutation($t14, 0, $t15);

    // $t90 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t90 := $IsParentMutation($t13, 3, $t14);

    // $t91 := &&($t89, $t90) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t91 := $And($t89, $t90);

    // $t92 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t92 := $IsParentMutation($t12, 2, $t13);

    // $t93 := &&($t91, $t92) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t93 := $And($t91, $t92);

    // if ($t93) goto L29 else goto L30 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t93) { goto L29; } else { goto L30; }

    // label L29 at .\sources\ConditionalBorrowChain.move:100:9+25
L29:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L30 at .\sources\ConditionalBorrowChain.move:100:9+25
L30:

    // $t94 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t94 := $IsParentMutation($t14, 0, $t15);

    // $t95 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t95 := $IsParentMutation($t13, 3, $t14);

    // $t96 := &&($t94, $t95) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t96 := $And($t94, $t95);

    // $t97 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t97 := $IsParentMutation($t12, 3, $t13);

    // $t98 := &&($t96, $t97) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t98 := $And($t96, $t97);

    // if ($t98) goto L31 else goto L32 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t98) { goto L31; } else { goto L32; }

    // label L31 at .\sources\ConditionalBorrowChain.move:100:9+25
L31:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L32 at .\sources\ConditionalBorrowChain.move:100:9+25
L32:

    // $t99 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t99 := $IsParentMutation($t14, 1, $t15);

    // $t100 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t100 := $IsParentMutation($t13, 0, $t14);

    // $t101 := &&($t99, $t100) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t101 := $And($t99, $t100);

    // $t102 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t102 := $IsParentMutation($t12, 0, $t13);

    // $t103 := &&($t101, $t102) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t103 := $And($t101, $t102);

    // if ($t103) goto L33 else goto L34 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t103) { goto L33; } else { goto L34; }

    // label L33 at .\sources\ConditionalBorrowChain.move:100:9+25
L33:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L34 at .\sources\ConditionalBorrowChain.move:100:9+25
L34:

    // $t104 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t104 := $IsParentMutation($t14, 1, $t15);

    // $t105 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t105 := $IsParentMutation($t13, 0, $t14);

    // $t106 := &&($t104, $t105) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t106 := $And($t104, $t105);

    // $t107 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t107 := $IsParentMutation($t12, 1, $t13);

    // $t108 := &&($t106, $t107) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t108 := $And($t106, $t107);

    // if ($t108) goto L35 else goto L36 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t108) { goto L35; } else { goto L36; }

    // label L35 at .\sources\ConditionalBorrowChain.move:100:9+25
L35:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L36 at .\sources\ConditionalBorrowChain.move:100:9+25
L36:

    // $t109 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t109 := $IsParentMutation($t14, 1, $t15);

    // $t110 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t110 := $IsParentMutation($t13, 0, $t14);

    // $t111 := &&($t109, $t110) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t111 := $And($t109, $t110);

    // $t112 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t112 := $IsParentMutation($t12, 2, $t13);

    // $t113 := &&($t111, $t112) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t113 := $And($t111, $t112);

    // if ($t113) goto L37 else goto L38 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t113) { goto L37; } else { goto L38; }

    // label L37 at .\sources\ConditionalBorrowChain.move:100:9+25
L37:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L38 at .\sources\ConditionalBorrowChain.move:100:9+25
L38:

    // $t114 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t114 := $IsParentMutation($t14, 1, $t15);

    // $t115 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t115 := $IsParentMutation($t13, 0, $t14);

    // $t116 := &&($t114, $t115) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t116 := $And($t114, $t115);

    // $t117 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t117 := $IsParentMutation($t12, 3, $t13);

    // $t118 := &&($t116, $t117) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t118 := $And($t116, $t117);

    // if ($t118) goto L39 else goto L40 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t118) { goto L39; } else { goto L40; }

    // label L39 at .\sources\ConditionalBorrowChain.move:100:9+25
L39:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L40 at .\sources\ConditionalBorrowChain.move:100:9+25
L40:

    // $t119 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t119 := $IsParentMutation($t14, 1, $t15);

    // $t120 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t120 := $IsParentMutation($t13, 1, $t14);

    // $t121 := &&($t119, $t120) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t121 := $And($t119, $t120);

    // $t122 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t122 := $IsParentMutation($t12, 0, $t13);

    // $t123 := &&($t121, $t122) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t123 := $And($t121, $t122);

    // if ($t123) goto L41 else goto L42 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t123) { goto L41; } else { goto L42; }

    // label L41 at .\sources\ConditionalBorrowChain.move:100:9+25
L41:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L42 at .\sources\ConditionalBorrowChain.move:100:9+25
L42:

    // $t124 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t124 := $IsParentMutation($t14, 1, $t15);

    // $t125 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t125 := $IsParentMutation($t13, 1, $t14);

    // $t126 := &&($t124, $t125) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t126 := $And($t124, $t125);

    // $t127 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t127 := $IsParentMutation($t12, 1, $t13);

    // $t128 := &&($t126, $t127) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t128 := $And($t126, $t127);

    // if ($t128) goto L43 else goto L44 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t128) { goto L43; } else { goto L44; }

    // label L43 at .\sources\ConditionalBorrowChain.move:100:9+25
L43:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L44 at .\sources\ConditionalBorrowChain.move:100:9+25
L44:

    // $t129 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t129 := $IsParentMutation($t14, 1, $t15);

    // $t130 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t130 := $IsParentMutation($t13, 1, $t14);

    // $t131 := &&($t129, $t130) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t131 := $And($t129, $t130);

    // $t132 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t132 := $IsParentMutation($t12, 2, $t13);

    // $t133 := &&($t131, $t132) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t133 := $And($t131, $t132);

    // if ($t133) goto L45 else goto L46 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t133) { goto L45; } else { goto L46; }

    // label L45 at .\sources\ConditionalBorrowChain.move:100:9+25
L45:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L46 at .\sources\ConditionalBorrowChain.move:100:9+25
L46:

    // $t134 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t134 := $IsParentMutation($t14, 1, $t15);

    // $t135 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t135 := $IsParentMutation($t13, 1, $t14);

    // $t136 := &&($t134, $t135) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t136 := $And($t134, $t135);

    // $t137 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t137 := $IsParentMutation($t12, 3, $t13);

    // $t138 := &&($t136, $t137) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t138 := $And($t136, $t137);

    // if ($t138) goto L47 else goto L48 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t138) { goto L47; } else { goto L48; }

    // label L47 at .\sources\ConditionalBorrowChain.move:100:9+25
L47:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L48 at .\sources\ConditionalBorrowChain.move:100:9+25
L48:

    // $t139 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t139 := $IsParentMutation($t14, 1, $t15);

    // $t140 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t140 := $IsParentMutation($t13, 2, $t14);

    // $t141 := &&($t139, $t140) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t141 := $And($t139, $t140);

    // $t142 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t142 := $IsParentMutation($t12, 0, $t13);

    // $t143 := &&($t141, $t142) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t143 := $And($t141, $t142);

    // if ($t143) goto L49 else goto L50 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t143) { goto L49; } else { goto L50; }

    // label L49 at .\sources\ConditionalBorrowChain.move:100:9+25
L49:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L50 at .\sources\ConditionalBorrowChain.move:100:9+25
L50:

    // $t144 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t144 := $IsParentMutation($t14, 1, $t15);

    // $t145 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t145 := $IsParentMutation($t13, 2, $t14);

    // $t146 := &&($t144, $t145) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t146 := $And($t144, $t145);

    // $t147 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t147 := $IsParentMutation($t12, 1, $t13);

    // $t148 := &&($t146, $t147) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t148 := $And($t146, $t147);

    // if ($t148) goto L51 else goto L52 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t148) { goto L51; } else { goto L52; }

    // label L51 at .\sources\ConditionalBorrowChain.move:100:9+25
L51:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L52 at .\sources\ConditionalBorrowChain.move:100:9+25
L52:

    // $t149 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t149 := $IsParentMutation($t14, 1, $t15);

    // $t150 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t150 := $IsParentMutation($t13, 2, $t14);

    // $t151 := &&($t149, $t150) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t151 := $And($t149, $t150);

    // $t152 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t152 := $IsParentMutation($t12, 2, $t13);

    // $t153 := &&($t151, $t152) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t153 := $And($t151, $t152);

    // if ($t153) goto L53 else goto L54 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t153) { goto L53; } else { goto L54; }

    // label L53 at .\sources\ConditionalBorrowChain.move:100:9+25
L53:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L54 at .\sources\ConditionalBorrowChain.move:100:9+25
L54:

    // $t154 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t154 := $IsParentMutation($t14, 1, $t15);

    // $t155 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t155 := $IsParentMutation($t13, 2, $t14);

    // $t156 := &&($t154, $t155) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t156 := $And($t154, $t155);

    // $t157 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t157 := $IsParentMutation($t12, 3, $t13);

    // $t158 := &&($t156, $t157) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t158 := $And($t156, $t157);

    // if ($t158) goto L55 else goto L56 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t158) { goto L55; } else { goto L56; }

    // label L55 at .\sources\ConditionalBorrowChain.move:100:9+25
L55:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L56 at .\sources\ConditionalBorrowChain.move:100:9+25
L56:

    // $t159 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t159 := $IsParentMutation($t14, 1, $t15);

    // $t160 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t160 := $IsParentMutation($t13, 3, $t14);

    // $t161 := &&($t159, $t160) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t161 := $And($t159, $t160);

    // $t162 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t162 := $IsParentMutation($t12, 0, $t13);

    // $t163 := &&($t161, $t162) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t163 := $And($t161, $t162);

    // if ($t163) goto L57 else goto L58 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t163) { goto L57; } else { goto L58; }

    // label L57 at .\sources\ConditionalBorrowChain.move:100:9+25
L57:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L58 at .\sources\ConditionalBorrowChain.move:100:9+25
L58:

    // $t164 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t164 := $IsParentMutation($t14, 1, $t15);

    // $t165 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t165 := $IsParentMutation($t13, 3, $t14);

    // $t166 := &&($t164, $t165) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t166 := $And($t164, $t165);

    // $t167 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t167 := $IsParentMutation($t12, 1, $t13);

    // $t168 := &&($t166, $t167) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t168 := $And($t166, $t167);

    // if ($t168) goto L59 else goto L60 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t168) { goto L59; } else { goto L60; }

    // label L59 at .\sources\ConditionalBorrowChain.move:100:9+25
L59:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L60 at .\sources\ConditionalBorrowChain.move:100:9+25
L60:

    // $t169 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t169 := $IsParentMutation($t14, 1, $t15);

    // $t170 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t170 := $IsParentMutation($t13, 3, $t14);

    // $t171 := &&($t169, $t170) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t171 := $And($t169, $t170);

    // $t172 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t172 := $IsParentMutation($t12, 2, $t13);

    // $t173 := &&($t171, $t172) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t173 := $And($t171, $t172);

    // if ($t173) goto L61 else goto L62 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t173) { goto L61; } else { goto L62; }

    // label L61 at .\sources\ConditionalBorrowChain.move:100:9+25
L61:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L62 at .\sources\ConditionalBorrowChain.move:100:9+25
L62:

    // $t174 := is_parent[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t174 := $IsParentMutation($t14, 1, $t15);

    // $t175 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t175 := $IsParentMutation($t13, 3, $t14);

    // $t176 := &&($t174, $t175) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t176 := $And($t174, $t175);

    // $t177 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t177 := $IsParentMutation($t12, 3, $t13);

    // $t178 := &&($t176, $t177) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t178 := $And($t176, $t177);

    // if ($t178) goto L63 else goto L64 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t178) { goto L63; } else { goto L64; }

    // label L63 at .\sources\ConditionalBorrowChain.move:100:9+25
L63:

    // write_back[Reference($t14).v1 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L64 at .\sources\ConditionalBorrowChain.move:100:9+25
L64:

    // $t179 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t179 := $IsParentMutation($t14, 2, $t15);

    // $t180 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t180 := $IsParentMutation($t13, 0, $t14);

    // $t181 := &&($t179, $t180) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t181 := $And($t179, $t180);

    // $t182 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t182 := $IsParentMutation($t12, 0, $t13);

    // $t183 := &&($t181, $t182) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t183 := $And($t181, $t182);

    // if ($t183) goto L65 else goto L66 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t183) { goto L65; } else { goto L66; }

    // label L65 at .\sources\ConditionalBorrowChain.move:100:9+25
L65:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L66 at .\sources\ConditionalBorrowChain.move:100:9+25
L66:

    // $t184 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t184 := $IsParentMutation($t14, 2, $t15);

    // $t185 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t185 := $IsParentMutation($t13, 0, $t14);

    // $t186 := &&($t184, $t185) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t186 := $And($t184, $t185);

    // $t187 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t187 := $IsParentMutation($t12, 1, $t13);

    // $t188 := &&($t186, $t187) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t188 := $And($t186, $t187);

    // if ($t188) goto L67 else goto L68 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t188) { goto L67; } else { goto L68; }

    // label L67 at .\sources\ConditionalBorrowChain.move:100:9+25
L67:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L68 at .\sources\ConditionalBorrowChain.move:100:9+25
L68:

    // $t189 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t189 := $IsParentMutation($t14, 2, $t15);

    // $t190 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t190 := $IsParentMutation($t13, 0, $t14);

    // $t191 := &&($t189, $t190) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t191 := $And($t189, $t190);

    // $t192 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t192 := $IsParentMutation($t12, 2, $t13);

    // $t193 := &&($t191, $t192) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t193 := $And($t191, $t192);

    // if ($t193) goto L69 else goto L70 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t193) { goto L69; } else { goto L70; }

    // label L69 at .\sources\ConditionalBorrowChain.move:100:9+25
L69:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L70 at .\sources\ConditionalBorrowChain.move:100:9+25
L70:

    // $t194 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t194 := $IsParentMutation($t14, 2, $t15);

    // $t195 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t195 := $IsParentMutation($t13, 0, $t14);

    // $t196 := &&($t194, $t195) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t196 := $And($t194, $t195);

    // $t197 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t197 := $IsParentMutation($t12, 3, $t13);

    // $t198 := &&($t196, $t197) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t198 := $And($t196, $t197);

    // if ($t198) goto L71 else goto L72 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t198) { goto L71; } else { goto L72; }

    // label L71 at .\sources\ConditionalBorrowChain.move:100:9+25
L71:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L72 at .\sources\ConditionalBorrowChain.move:100:9+25
L72:

    // $t199 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t199 := $IsParentMutation($t14, 2, $t15);

    // $t200 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t200 := $IsParentMutation($t13, 1, $t14);

    // $t201 := &&($t199, $t200) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t201 := $And($t199, $t200);

    // $t202 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t202 := $IsParentMutation($t12, 0, $t13);

    // $t203 := &&($t201, $t202) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t203 := $And($t201, $t202);

    // if ($t203) goto L73 else goto L74 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t203) { goto L73; } else { goto L74; }

    // label L73 at .\sources\ConditionalBorrowChain.move:100:9+25
L73:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L74 at .\sources\ConditionalBorrowChain.move:100:9+25
L74:

    // $t204 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t204 := $IsParentMutation($t14, 2, $t15);

    // $t205 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t205 := $IsParentMutation($t13, 1, $t14);

    // $t206 := &&($t204, $t205) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t206 := $And($t204, $t205);

    // $t207 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t207 := $IsParentMutation($t12, 1, $t13);

    // $t208 := &&($t206, $t207) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t208 := $And($t206, $t207);

    // if ($t208) goto L75 else goto L76 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t208) { goto L75; } else { goto L76; }

    // label L75 at .\sources\ConditionalBorrowChain.move:100:9+25
L75:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L76 at .\sources\ConditionalBorrowChain.move:100:9+25
L76:

    // $t209 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t209 := $IsParentMutation($t14, 2, $t15);

    // $t210 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t210 := $IsParentMutation($t13, 1, $t14);

    // $t211 := &&($t209, $t210) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t211 := $And($t209, $t210);

    // $t212 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t212 := $IsParentMutation($t12, 2, $t13);

    // $t213 := &&($t211, $t212) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t213 := $And($t211, $t212);

    // if ($t213) goto L77 else goto L78 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t213) { goto L77; } else { goto L78; }

    // label L77 at .\sources\ConditionalBorrowChain.move:100:9+25
L77:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L78 at .\sources\ConditionalBorrowChain.move:100:9+25
L78:

    // $t214 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t214 := $IsParentMutation($t14, 2, $t15);

    // $t215 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t215 := $IsParentMutation($t13, 1, $t14);

    // $t216 := &&($t214, $t215) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t216 := $And($t214, $t215);

    // $t217 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t217 := $IsParentMutation($t12, 3, $t13);

    // $t218 := &&($t216, $t217) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t218 := $And($t216, $t217);

    // if ($t218) goto L79 else goto L80 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t218) { goto L79; } else { goto L80; }

    // label L79 at .\sources\ConditionalBorrowChain.move:100:9+25
L79:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L80 at .\sources\ConditionalBorrowChain.move:100:9+25
L80:

    // $t219 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t219 := $IsParentMutation($t14, 2, $t15);

    // $t220 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t220 := $IsParentMutation($t13, 2, $t14);

    // $t221 := &&($t219, $t220) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t221 := $And($t219, $t220);

    // $t222 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t222 := $IsParentMutation($t12, 0, $t13);

    // $t223 := &&($t221, $t222) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t223 := $And($t221, $t222);

    // if ($t223) goto L81 else goto L82 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t223) { goto L81; } else { goto L82; }

    // label L81 at .\sources\ConditionalBorrowChain.move:100:9+25
L81:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L82 at .\sources\ConditionalBorrowChain.move:100:9+25
L82:

    // $t224 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t224 := $IsParentMutation($t14, 2, $t15);

    // $t225 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t225 := $IsParentMutation($t13, 2, $t14);

    // $t226 := &&($t224, $t225) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t226 := $And($t224, $t225);

    // $t227 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t227 := $IsParentMutation($t12, 1, $t13);

    // $t228 := &&($t226, $t227) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t228 := $And($t226, $t227);

    // if ($t228) goto L83 else goto L84 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t228) { goto L83; } else { goto L84; }

    // label L83 at .\sources\ConditionalBorrowChain.move:100:9+25
L83:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L84 at .\sources\ConditionalBorrowChain.move:100:9+25
L84:

    // $t229 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t229 := $IsParentMutation($t14, 2, $t15);

    // $t230 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t230 := $IsParentMutation($t13, 2, $t14);

    // $t231 := &&($t229, $t230) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t231 := $And($t229, $t230);

    // $t232 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t232 := $IsParentMutation($t12, 2, $t13);

    // $t233 := &&($t231, $t232) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t233 := $And($t231, $t232);

    // if ($t233) goto L85 else goto L86 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t233) { goto L85; } else { goto L86; }

    // label L85 at .\sources\ConditionalBorrowChain.move:100:9+25
L85:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L86 at .\sources\ConditionalBorrowChain.move:100:9+25
L86:

    // $t234 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t234 := $IsParentMutation($t14, 2, $t15);

    // $t235 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t235 := $IsParentMutation($t13, 2, $t14);

    // $t236 := &&($t234, $t235) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t236 := $And($t234, $t235);

    // $t237 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t237 := $IsParentMutation($t12, 3, $t13);

    // $t238 := &&($t236, $t237) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t238 := $And($t236, $t237);

    // if ($t238) goto L87 else goto L88 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t238) { goto L87; } else { goto L88; }

    // label L87 at .\sources\ConditionalBorrowChain.move:100:9+25
L87:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L88 at .\sources\ConditionalBorrowChain.move:100:9+25
L88:

    // $t239 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t239 := $IsParentMutation($t14, 2, $t15);

    // $t240 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t240 := $IsParentMutation($t13, 3, $t14);

    // $t241 := &&($t239, $t240) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t241 := $And($t239, $t240);

    // $t242 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t242 := $IsParentMutation($t12, 0, $t13);

    // $t243 := &&($t241, $t242) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t243 := $And($t241, $t242);

    // if ($t243) goto L89 else goto L90 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t243) { goto L89; } else { goto L90; }

    // label L89 at .\sources\ConditionalBorrowChain.move:100:9+25
L89:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L90 at .\sources\ConditionalBorrowChain.move:100:9+25
L90:

    // $t244 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t244 := $IsParentMutation($t14, 2, $t15);

    // $t245 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t245 := $IsParentMutation($t13, 3, $t14);

    // $t246 := &&($t244, $t245) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t246 := $And($t244, $t245);

    // $t247 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t247 := $IsParentMutation($t12, 1, $t13);

    // $t248 := &&($t246, $t247) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t248 := $And($t246, $t247);

    // if ($t248) goto L91 else goto L92 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t248) { goto L91; } else { goto L92; }

    // label L91 at .\sources\ConditionalBorrowChain.move:100:9+25
L91:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L92 at .\sources\ConditionalBorrowChain.move:100:9+25
L92:

    // $t249 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t249 := $IsParentMutation($t14, 2, $t15);

    // $t250 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t250 := $IsParentMutation($t13, 3, $t14);

    // $t251 := &&($t249, $t250) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t251 := $And($t249, $t250);

    // $t252 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t252 := $IsParentMutation($t12, 2, $t13);

    // $t253 := &&($t251, $t252) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t253 := $And($t251, $t252);

    // if ($t253) goto L93 else goto L94 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t253) { goto L93; } else { goto L94; }

    // label L93 at .\sources\ConditionalBorrowChain.move:100:9+25
L93:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L94 at .\sources\ConditionalBorrowChain.move:100:9+25
L94:

    // $t254 := is_parent[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t254 := $IsParentMutation($t14, 2, $t15);

    // $t255 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t255 := $IsParentMutation($t13, 3, $t14);

    // $t256 := &&($t254, $t255) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t256 := $And($t254, $t255);

    // $t257 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t257 := $IsParentMutation($t12, 3, $t13);

    // $t258 := &&($t256, $t257) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t258 := $And($t256, $t257);

    // if ($t258) goto L95 else goto L96 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t258) { goto L95; } else { goto L96; }

    // label L95 at .\sources\ConditionalBorrowChain.move:100:9+25
L95:

    // write_back[Reference($t14).v2 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L96 at .\sources\ConditionalBorrowChain.move:100:9+25
L96:

    // $t259 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t259 := $IsParentMutation($t14, 3, $t15);

    // $t260 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t260 := $IsParentMutation($t13, 0, $t14);

    // $t261 := &&($t259, $t260) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t261 := $And($t259, $t260);

    // $t262 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t262 := $IsParentMutation($t12, 0, $t13);

    // $t263 := &&($t261, $t262) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t263 := $And($t261, $t262);

    // if ($t263) goto L97 else goto L98 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t263) { goto L97; } else { goto L98; }

    // label L97 at .\sources\ConditionalBorrowChain.move:100:9+25
L97:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L98 at .\sources\ConditionalBorrowChain.move:100:9+25
L98:

    // $t264 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t264 := $IsParentMutation($t14, 3, $t15);

    // $t265 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t265 := $IsParentMutation($t13, 0, $t14);

    // $t266 := &&($t264, $t265) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t266 := $And($t264, $t265);

    // $t267 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t267 := $IsParentMutation($t12, 1, $t13);

    // $t268 := &&($t266, $t267) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t268 := $And($t266, $t267);

    // if ($t268) goto L99 else goto L100 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t268) { goto L99; } else { goto L100; }

    // label L99 at .\sources\ConditionalBorrowChain.move:100:9+25
L99:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L100 at .\sources\ConditionalBorrowChain.move:100:9+25
L100:

    // $t269 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t269 := $IsParentMutation($t14, 3, $t15);

    // $t270 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t270 := $IsParentMutation($t13, 0, $t14);

    // $t271 := &&($t269, $t270) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t271 := $And($t269, $t270);

    // $t272 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t272 := $IsParentMutation($t12, 2, $t13);

    // $t273 := &&($t271, $t272) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t273 := $And($t271, $t272);

    // if ($t273) goto L101 else goto L102 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t273) { goto L101; } else { goto L102; }

    // label L101 at .\sources\ConditionalBorrowChain.move:100:9+25
L101:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L102 at .\sources\ConditionalBorrowChain.move:100:9+25
L102:

    // $t274 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t274 := $IsParentMutation($t14, 3, $t15);

    // $t275 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t275 := $IsParentMutation($t13, 0, $t14);

    // $t276 := &&($t274, $t275) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t276 := $And($t274, $t275);

    // $t277 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t277 := $IsParentMutation($t12, 3, $t13);

    // $t278 := &&($t276, $t277) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t278 := $And($t276, $t277);

    // if ($t278) goto L103 else goto L104 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t278) { goto L103; } else { goto L104; }

    // label L103 at .\sources\ConditionalBorrowChain.move:100:9+25
L103:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L104 at .\sources\ConditionalBorrowChain.move:100:9+25
L104:

    // $t279 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t279 := $IsParentMutation($t14, 3, $t15);

    // $t280 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t280 := $IsParentMutation($t13, 1, $t14);

    // $t281 := &&($t279, $t280) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t281 := $And($t279, $t280);

    // $t282 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t282 := $IsParentMutation($t12, 0, $t13);

    // $t283 := &&($t281, $t282) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t283 := $And($t281, $t282);

    // if ($t283) goto L105 else goto L106 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t283) { goto L105; } else { goto L106; }

    // label L105 at .\sources\ConditionalBorrowChain.move:100:9+25
L105:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L106 at .\sources\ConditionalBorrowChain.move:100:9+25
L106:

    // $t284 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t284 := $IsParentMutation($t14, 3, $t15);

    // $t285 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t285 := $IsParentMutation($t13, 1, $t14);

    // $t286 := &&($t284, $t285) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t286 := $And($t284, $t285);

    // $t287 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t287 := $IsParentMutation($t12, 1, $t13);

    // $t288 := &&($t286, $t287) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t288 := $And($t286, $t287);

    // if ($t288) goto L107 else goto L108 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t288) { goto L107; } else { goto L108; }

    // label L107 at .\sources\ConditionalBorrowChain.move:100:9+25
L107:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L108 at .\sources\ConditionalBorrowChain.move:100:9+25
L108:

    // $t289 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t289 := $IsParentMutation($t14, 3, $t15);

    // $t290 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t290 := $IsParentMutation($t13, 1, $t14);

    // $t291 := &&($t289, $t290) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t291 := $And($t289, $t290);

    // $t292 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t292 := $IsParentMutation($t12, 2, $t13);

    // $t293 := &&($t291, $t292) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t293 := $And($t291, $t292);

    // if ($t293) goto L109 else goto L110 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t293) { goto L109; } else { goto L110; }

    // label L109 at .\sources\ConditionalBorrowChain.move:100:9+25
L109:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L110 at .\sources\ConditionalBorrowChain.move:100:9+25
L110:

    // $t294 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t294 := $IsParentMutation($t14, 3, $t15);

    // $t295 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t295 := $IsParentMutation($t13, 1, $t14);

    // $t296 := &&($t294, $t295) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t296 := $And($t294, $t295);

    // $t297 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t297 := $IsParentMutation($t12, 3, $t13);

    // $t298 := &&($t296, $t297) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t298 := $And($t296, $t297);

    // if ($t298) goto L111 else goto L112 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t298) { goto L111; } else { goto L112; }

    // label L111 at .\sources\ConditionalBorrowChain.move:100:9+25
L111:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L112 at .\sources\ConditionalBorrowChain.move:100:9+25
L112:

    // $t299 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t299 := $IsParentMutation($t14, 3, $t15);

    // $t300 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t300 := $IsParentMutation($t13, 2, $t14);

    // $t301 := &&($t299, $t300) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t301 := $And($t299, $t300);

    // $t302 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t302 := $IsParentMutation($t12, 0, $t13);

    // $t303 := &&($t301, $t302) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t303 := $And($t301, $t302);

    // if ($t303) goto L113 else goto L114 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t303) { goto L113; } else { goto L114; }

    // label L113 at .\sources\ConditionalBorrowChain.move:100:9+25
L113:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L114 at .\sources\ConditionalBorrowChain.move:100:9+25
L114:

    // $t304 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t304 := $IsParentMutation($t14, 3, $t15);

    // $t305 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t305 := $IsParentMutation($t13, 2, $t14);

    // $t306 := &&($t304, $t305) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t306 := $And($t304, $t305);

    // $t307 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t307 := $IsParentMutation($t12, 1, $t13);

    // $t308 := &&($t306, $t307) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t308 := $And($t306, $t307);

    // if ($t308) goto L115 else goto L116 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t308) { goto L115; } else { goto L116; }

    // label L115 at .\sources\ConditionalBorrowChain.move:100:9+25
L115:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L116 at .\sources\ConditionalBorrowChain.move:100:9+25
L116:

    // $t309 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t309 := $IsParentMutation($t14, 3, $t15);

    // $t310 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t310 := $IsParentMutation($t13, 2, $t14);

    // $t311 := &&($t309, $t310) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t311 := $And($t309, $t310);

    // $t312 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t312 := $IsParentMutation($t12, 2, $t13);

    // $t313 := &&($t311, $t312) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t313 := $And($t311, $t312);

    // if ($t313) goto L117 else goto L118 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t313) { goto L117; } else { goto L118; }

    // label L117 at .\sources\ConditionalBorrowChain.move:100:9+25
L117:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L118 at .\sources\ConditionalBorrowChain.move:100:9+25
L118:

    // $t314 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t314 := $IsParentMutation($t14, 3, $t15);

    // $t315 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t315 := $IsParentMutation($t13, 2, $t14);

    // $t316 := &&($t314, $t315) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t316 := $And($t314, $t315);

    // $t317 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t317 := $IsParentMutation($t12, 3, $t13);

    // $t318 := &&($t316, $t317) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t318 := $And($t316, $t317);

    // if ($t318) goto L119 else goto L120 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t318) { goto L119; } else { goto L120; }

    // label L119 at .\sources\ConditionalBorrowChain.move:100:9+25
L119:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L120 at .\sources\ConditionalBorrowChain.move:100:9+25
L120:

    // $t319 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t319 := $IsParentMutation($t14, 3, $t15);

    // $t320 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t320 := $IsParentMutation($t13, 3, $t14);

    // $t321 := &&($t319, $t320) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t321 := $And($t319, $t320);

    // $t322 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t322 := $IsParentMutation($t12, 0, $t13);

    // $t323 := &&($t321, $t322) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t323 := $And($t321, $t322);

    // if ($t323) goto L121 else goto L122 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t323) { goto L121; } else { goto L122; }

    // label L121 at .\sources\ConditionalBorrowChain.move:100:9+25
L121:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L122 at .\sources\ConditionalBorrowChain.move:100:9+25
L122:

    // $t324 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t324 := $IsParentMutation($t14, 3, $t15);

    // $t325 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t325 := $IsParentMutation($t13, 3, $t14);

    // $t326 := &&($t324, $t325) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t326 := $And($t324, $t325);

    // $t327 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t327 := $IsParentMutation($t12, 1, $t13);

    // $t328 := &&($t326, $t327) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t328 := $And($t326, $t327);

    // if ($t328) goto L123 else goto L124 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t328) { goto L123; } else { goto L124; }

    // label L123 at .\sources\ConditionalBorrowChain.move:100:9+25
L123:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L124 at .\sources\ConditionalBorrowChain.move:100:9+25
L124:

    // $t329 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t329 := $IsParentMutation($t14, 3, $t15);

    // $t330 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t330 := $IsParentMutation($t13, 3, $t14);

    // $t331 := &&($t329, $t330) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t331 := $And($t329, $t330);

    // $t332 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t332 := $IsParentMutation($t12, 2, $t13);

    // $t333 := &&($t331, $t332) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t333 := $And($t331, $t332);

    // if ($t333) goto L125 else goto L126 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t333) { goto L125; } else { goto L126; }

    // label L125 at .\sources\ConditionalBorrowChain.move:100:9+25
L125:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L126 at .\sources\ConditionalBorrowChain.move:100:9+25
L126:

    // $t334 := is_parent[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t334 := $IsParentMutation($t14, 3, $t15);

    // $t335 := is_parent[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t335 := $IsParentMutation($t13, 3, $t14);

    // $t336 := &&($t334, $t335) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t336 := $And($t334, $t335);

    // $t337 := is_parent[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t337 := $IsParentMutation($t12, 3, $t13);

    // $t338 := &&($t336, $t337) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t338 := $And($t336, $t337);

    // if ($t338) goto L127 else goto L131 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t338) { goto L127; } else { goto L131; }

    // label L127 at .\sources\ConditionalBorrowChain.move:100:9+25
L127:

    // write_back[Reference($t14).v3 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3199,3224)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node1'_v3($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node2'_v3($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v3 (0xbc::ProphecyBenchmark3Levels4Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels4Fields_Node3'_v3($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L128 at .\sources\ConditionalBorrowChain.move:100:9+25
L128:

    // $t339 := move($t3) at .\sources\ConditionalBorrowChain.move:102:9+4
    assume {:print "$at(3,3235,3239)"} true;
    $t339 := $t3;

    // trace_return[0]($t339) at .\sources\ConditionalBorrowChain.move:87:14+418
    assume {:print "$at(3,2827,3245)"} true;
    assume {:print "$track_return(2,0,0):", $t339} $t339 == $t339;

    // label L129 at .\sources\ConditionalBorrowChain.move:103:5+1
    assume {:print "$at(3,3244,3245)"} true;
L129:

    // assert Implies(And(And(Eq<u64>($t0, 0), Eq<u64>($t1, 0)), Eq<u64>($t2, 0)), Eq<u64>(select ProphecyBenchmark3Levels4Fields::Node1.v0<0xbc::ProphecyBenchmark3Levels4Fields::Node1>(select ProphecyBenchmark3Levels4Fields::Node2.v0<0xbc::ProphecyBenchmark3Levels4Fields::Node2>(select ProphecyBenchmark3Levels4Fields::Node3.v0<0xbc::ProphecyBenchmark3Levels4Fields::Node3>($t339))), 1)) at .\sources\ConditionalBorrowChain.move:119:9+72
    assume {:print "$at(3,3580,3652)"} true;
    assert {:msg "assert_failed(3,3580,3652): post-condition does not hold"}
      ((($IsEqual'u64'($t0, 0) && $IsEqual'u64'($t1, 0)) && $IsEqual'u64'($t2, 0)) ==> $IsEqual'u64'($t339->$v0->$v0->$v0, 1));

    // assert Le(select ProphecyBenchmark3Levels4Fields::Node1.v0<0xbc::ProphecyBenchmark3Levels4Fields::Node1>(select ProphecyBenchmark3Levels4Fields::Node2.v0<0xbc::ProphecyBenchmark3Levels4Fields::Node2>(select ProphecyBenchmark3Levels4Fields::Node3.v0<0xbc::ProphecyBenchmark3Levels4Fields::Node3>($t339))), 1) at .\sources\ConditionalBorrowChain.move:127:9+29
    assume {:print "$at(3,3852,3881)"} true;
    assert {:msg "assert_failed(3,3852,3881): post-condition does not hold"}
      ($t339->$v0->$v0->$v0 <= 1);

    // return $t339 at .\sources\ConditionalBorrowChain.move:127:9+29
    $ret0 := $t339;
    return;

    // label L130 at .\sources\ConditionalBorrowChain.move:103:5+1
    assume {:print "$at(3,3244,3245)"} true;
L130:

    // abort($t5) at .\sources\ConditionalBorrowChain.move:103:5+1
    assume {:print "$at(3,3244,3245)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

    // label L131 at <internal>:1:1+10
    assume {:print "$at(1,0,10)"} true;
L131:

    // drop($t12) at <internal>:1:1+10
    assume {:print "$at(1,0,10)"} true;

    // drop($t13) at <internal>:1:1+10

    // drop($t14) at <internal>:1:1+10

    // drop($t15) at <internal>:1:1+10

    // goto L128 at <internal>:1:1+10
    goto L128;

}

// fun ProphecyBenchmark3Levels4Fields::new_node1 [baseline] at .\sources\ConditionalBorrowChain.move:29:5+110
procedure {:inline 1} $bc_ProphecyBenchmark3Levels4Fields_new_node1() returns ($ret0: $bc_ProphecyBenchmark3Levels4Fields_Node1)
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
    var $t8: $bc_ProphecyBenchmark3Levels4Fields_Node1;
    var $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1': $bc_ProphecyBenchmark3Levels4Fields_Node1;

    // bytecode translation starts here
    // $t0 := 0 at .\sources\ConditionalBorrowChain.move:30:21+1
    assume {:print "$at(3,931,932)"} true;
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

    // $t8 := pack 0xbc::ProphecyBenchmark3Levels4Fields::Node1($t0, $t1, $t2, $t3, $t4, $t5, $t6, $t7) at .\sources\ConditionalBorrowChain.move:30:9+64
    $t8 := $bc_ProphecyBenchmark3Levels4Fields_Node1($t0, $t1, $t2, $t3, $t4, $t5, $t6, $t7);

    // trace_return[0]($t8) at .\sources\ConditionalBorrowChain.move:30:9+64
    assume {:print "$track_return(2,1,0):", $t8} $t8 == $t8;

    // label L1 at .\sources\ConditionalBorrowChain.move:31:5+1
    assume {:print "$at(3,988,989)"} true;
L1:

    // return $t8 at .\sources\ConditionalBorrowChain.move:31:5+1
    assume {:print "$at(3,988,989)"} true;
    $ret0 := $t8;
    return;

}

// fun ProphecyBenchmark3Levels4Fields::new_node1 [verification] at .\sources\ConditionalBorrowChain.move:29:5+110
procedure {:timeLimit 40} $bc_ProphecyBenchmark3Levels4Fields_new_node1$verify() returns ($ret0: $bc_ProphecyBenchmark3Levels4Fields_Node1)
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
    var $t8: $bc_ProphecyBenchmark3Levels4Fields_Node1;
    var $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1': $bc_ProphecyBenchmark3Levels4Fields_Node1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t0 := 0 at .\sources\ConditionalBorrowChain.move:30:21+1
    assume {:print "$at(3,931,932)"} true;
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

    // $t8 := pack 0xbc::ProphecyBenchmark3Levels4Fields::Node1($t0, $t1, $t2, $t3, $t4, $t5, $t6, $t7) at .\sources\ConditionalBorrowChain.move:30:9+64
    $t8 := $bc_ProphecyBenchmark3Levels4Fields_Node1($t0, $t1, $t2, $t3, $t4, $t5, $t6, $t7);

    // trace_return[0]($t8) at .\sources\ConditionalBorrowChain.move:30:9+64
    assume {:print "$track_return(2,1,0):", $t8} $t8 == $t8;

    // label L1 at .\sources\ConditionalBorrowChain.move:31:5+1
    assume {:print "$at(3,988,989)"} true;
L1:

    // return $t8 at .\sources\ConditionalBorrowChain.move:31:5+1
    assume {:print "$at(3,988,989)"} true;
    $ret0 := $t8;
    return;

}

// fun ProphecyBenchmark3Levels4Fields::new_node2 [baseline] at .\sources\ConditionalBorrowChain.move:33:5+225
procedure {:inline 1} $bc_ProphecyBenchmark3Levels4Fields_new_node2() returns ($ret0: $bc_ProphecyBenchmark3Levels4Fields_Node2)
{
    // declare local variables
    var $t0: $bc_ProphecyBenchmark3Levels4Fields_Node1;
    var $t1: int;
    var $t2: $bc_ProphecyBenchmark3Levels4Fields_Node1;
    var $t3: $bc_ProphecyBenchmark3Levels4Fields_Node1;
    var $t4: $bc_ProphecyBenchmark3Levels4Fields_Node1;
    var $t5: $bc_ProphecyBenchmark3Levels4Fields_Node1;
    var $t6: $bc_ProphecyBenchmark3Levels4Fields_Node1;
    var $t7: $bc_ProphecyBenchmark3Levels4Fields_Node1;
    var $t8: $bc_ProphecyBenchmark3Levels4Fields_Node1;
    var $t9: $bc_ProphecyBenchmark3Levels4Fields_Node2;
    var $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2': $bc_ProphecyBenchmark3Levels4Fields_Node2;

    // bytecode translation starts here
    // $t0 := ProphecyBenchmark3Levels4Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:35:17+11
    assume {:print "$at(3,1060,1071)"} true;
    call $t0 := $bc_ProphecyBenchmark3Levels4Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1060,1071)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t2 := ProphecyBenchmark3Levels4Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:35:34+11
    call $t2 := $bc_ProphecyBenchmark3Levels4Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1077,1088)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t3 := ProphecyBenchmark3Levels4Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:35:51+11
    call $t3 := $bc_ProphecyBenchmark3Levels4Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1094,1105)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t4 := ProphecyBenchmark3Levels4Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:35:68+11
    call $t4 := $bc_ProphecyBenchmark3Levels4Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1111,1122)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t5 := ProphecyBenchmark3Levels4Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:36:17+11
    assume {:print "$at(3,1141,1152)"} true;
    call $t5 := $bc_ProphecyBenchmark3Levels4Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1141,1152)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t6 := ProphecyBenchmark3Levels4Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:36:34+11
    call $t6 := $bc_ProphecyBenchmark3Levels4Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1158,1169)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t7 := ProphecyBenchmark3Levels4Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:36:51+11
    call $t7 := $bc_ProphecyBenchmark3Levels4Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1175,1186)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t8 := ProphecyBenchmark3Levels4Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:36:68+11
    call $t8 := $bc_ProphecyBenchmark3Levels4Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1192,1203)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t9 := pack 0xbc::ProphecyBenchmark3Levels4Fields::Node2($t0, $t2, $t3, $t4, $t5, $t6, $t7, $t8) at .\sources\ConditionalBorrowChain.move:34:9+179
    assume {:print "$at(3,1035,1214)"} true;
    $t9 := $bc_ProphecyBenchmark3Levels4Fields_Node2($t0, $t2, $t3, $t4, $t5, $t6, $t7, $t8);

    // trace_return[0]($t9) at .\sources\ConditionalBorrowChain.move:34:9+179
    assume {:print "$track_return(2,2,0):", $t9} $t9 == $t9;

    // label L1 at .\sources\ConditionalBorrowChain.move:38:5+1
    assume {:print "$at(3,1219,1220)"} true;
L1:

    // return $t9 at .\sources\ConditionalBorrowChain.move:38:5+1
    assume {:print "$at(3,1219,1220)"} true;
    $ret0 := $t9;
    return;

    // label L2 at .\sources\ConditionalBorrowChain.move:38:5+1
L2:

    // abort($t1) at .\sources\ConditionalBorrowChain.move:38:5+1
    assume {:print "$at(3,1219,1220)"} true;
    $abort_code := $t1;
    $abort_flag := true;
    return;

}

// fun ProphecyBenchmark3Levels4Fields::new_node2 [verification] at .\sources\ConditionalBorrowChain.move:33:5+225
procedure {:timeLimit 40} $bc_ProphecyBenchmark3Levels4Fields_new_node2$verify() returns ($ret0: $bc_ProphecyBenchmark3Levels4Fields_Node2)
{
    // declare local variables
    var $t0: $bc_ProphecyBenchmark3Levels4Fields_Node1;
    var $t1: int;
    var $t2: $bc_ProphecyBenchmark3Levels4Fields_Node1;
    var $t3: $bc_ProphecyBenchmark3Levels4Fields_Node1;
    var $t4: $bc_ProphecyBenchmark3Levels4Fields_Node1;
    var $t5: $bc_ProphecyBenchmark3Levels4Fields_Node1;
    var $t6: $bc_ProphecyBenchmark3Levels4Fields_Node1;
    var $t7: $bc_ProphecyBenchmark3Levels4Fields_Node1;
    var $t8: $bc_ProphecyBenchmark3Levels4Fields_Node1;
    var $t9: $bc_ProphecyBenchmark3Levels4Fields_Node2;
    var $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2': $bc_ProphecyBenchmark3Levels4Fields_Node2;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t0 := ProphecyBenchmark3Levels4Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:35:17+11
    assume {:print "$at(3,1060,1071)"} true;
    call $t0 := $bc_ProphecyBenchmark3Levels4Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1060,1071)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t2 := ProphecyBenchmark3Levels4Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:35:34+11
    call $t2 := $bc_ProphecyBenchmark3Levels4Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1077,1088)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t3 := ProphecyBenchmark3Levels4Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:35:51+11
    call $t3 := $bc_ProphecyBenchmark3Levels4Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1094,1105)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t4 := ProphecyBenchmark3Levels4Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:35:68+11
    call $t4 := $bc_ProphecyBenchmark3Levels4Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1111,1122)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t5 := ProphecyBenchmark3Levels4Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:36:17+11
    assume {:print "$at(3,1141,1152)"} true;
    call $t5 := $bc_ProphecyBenchmark3Levels4Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1141,1152)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t6 := ProphecyBenchmark3Levels4Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:36:34+11
    call $t6 := $bc_ProphecyBenchmark3Levels4Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1158,1169)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t7 := ProphecyBenchmark3Levels4Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:36:51+11
    call $t7 := $bc_ProphecyBenchmark3Levels4Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1175,1186)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t8 := ProphecyBenchmark3Levels4Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:36:68+11
    call $t8 := $bc_ProphecyBenchmark3Levels4Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1192,1203)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t9 := pack 0xbc::ProphecyBenchmark3Levels4Fields::Node2($t0, $t2, $t3, $t4, $t5, $t6, $t7, $t8) at .\sources\ConditionalBorrowChain.move:34:9+179
    assume {:print "$at(3,1035,1214)"} true;
    $t9 := $bc_ProphecyBenchmark3Levels4Fields_Node2($t0, $t2, $t3, $t4, $t5, $t6, $t7, $t8);

    // trace_return[0]($t9) at .\sources\ConditionalBorrowChain.move:34:9+179
    assume {:print "$track_return(2,2,0):", $t9} $t9 == $t9;

    // label L1 at .\sources\ConditionalBorrowChain.move:38:5+1
    assume {:print "$at(3,1219,1220)"} true;
L1:

    // return $t9 at .\sources\ConditionalBorrowChain.move:38:5+1
    assume {:print "$at(3,1219,1220)"} true;
    $ret0 := $t9;
    return;

    // label L2 at .\sources\ConditionalBorrowChain.move:38:5+1
L2:

    // abort($t1) at .\sources\ConditionalBorrowChain.move:38:5+1
    assume {:print "$at(3,1219,1220)"} true;
    $abort_code := $t1;
    $abort_flag := true;
    return;

}

// fun ProphecyBenchmark3Levels4Fields::new_node3 [baseline] at .\sources\ConditionalBorrowChain.move:40:5+225
procedure {:inline 1} $bc_ProphecyBenchmark3Levels4Fields_new_node3() returns ($ret0: $bc_ProphecyBenchmark3Levels4Fields_Node3)
{
    // declare local variables
    var $t0: $bc_ProphecyBenchmark3Levels4Fields_Node2;
    var $t1: int;
    var $t2: $bc_ProphecyBenchmark3Levels4Fields_Node2;
    var $t3: $bc_ProphecyBenchmark3Levels4Fields_Node2;
    var $t4: $bc_ProphecyBenchmark3Levels4Fields_Node2;
    var $t5: $bc_ProphecyBenchmark3Levels4Fields_Node2;
    var $t6: $bc_ProphecyBenchmark3Levels4Fields_Node2;
    var $t7: $bc_ProphecyBenchmark3Levels4Fields_Node2;
    var $t8: $bc_ProphecyBenchmark3Levels4Fields_Node2;
    var $t9: $bc_ProphecyBenchmark3Levels4Fields_Node3;
    var $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3': $bc_ProphecyBenchmark3Levels4Fields_Node3;

    // bytecode translation starts here
    // $t0 := ProphecyBenchmark3Levels4Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:42:17+11
    assume {:print "$at(3,1291,1302)"} true;
    call $t0 := $bc_ProphecyBenchmark3Levels4Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1291,1302)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t2 := ProphecyBenchmark3Levels4Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:42:34+11
    call $t2 := $bc_ProphecyBenchmark3Levels4Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1308,1319)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t3 := ProphecyBenchmark3Levels4Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:42:51+11
    call $t3 := $bc_ProphecyBenchmark3Levels4Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1325,1336)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t4 := ProphecyBenchmark3Levels4Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:42:68+11
    call $t4 := $bc_ProphecyBenchmark3Levels4Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1342,1353)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t5 := ProphecyBenchmark3Levels4Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:43:17+11
    assume {:print "$at(3,1372,1383)"} true;
    call $t5 := $bc_ProphecyBenchmark3Levels4Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1372,1383)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t6 := ProphecyBenchmark3Levels4Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:43:34+11
    call $t6 := $bc_ProphecyBenchmark3Levels4Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1389,1400)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t7 := ProphecyBenchmark3Levels4Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:43:51+11
    call $t7 := $bc_ProphecyBenchmark3Levels4Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1406,1417)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t8 := ProphecyBenchmark3Levels4Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:43:68+11
    call $t8 := $bc_ProphecyBenchmark3Levels4Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1423,1434)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t9 := pack 0xbc::ProphecyBenchmark3Levels4Fields::Node3($t0, $t2, $t3, $t4, $t5, $t6, $t7, $t8) at .\sources\ConditionalBorrowChain.move:41:9+179
    assume {:print "$at(3,1266,1445)"} true;
    $t9 := $bc_ProphecyBenchmark3Levels4Fields_Node3($t0, $t2, $t3, $t4, $t5, $t6, $t7, $t8);

    // trace_return[0]($t9) at .\sources\ConditionalBorrowChain.move:41:9+179
    assume {:print "$track_return(2,3,0):", $t9} $t9 == $t9;

    // label L1 at .\sources\ConditionalBorrowChain.move:45:5+1
    assume {:print "$at(3,1450,1451)"} true;
L1:

    // return $t9 at .\sources\ConditionalBorrowChain.move:45:5+1
    assume {:print "$at(3,1450,1451)"} true;
    $ret0 := $t9;
    return;

    // label L2 at .\sources\ConditionalBorrowChain.move:45:5+1
L2:

    // abort($t1) at .\sources\ConditionalBorrowChain.move:45:5+1
    assume {:print "$at(3,1450,1451)"} true;
    $abort_code := $t1;
    $abort_flag := true;
    return;

}

// fun ProphecyBenchmark3Levels4Fields::new_node3 [verification] at .\sources\ConditionalBorrowChain.move:40:5+225
procedure {:timeLimit 40} $bc_ProphecyBenchmark3Levels4Fields_new_node3$verify() returns ($ret0: $bc_ProphecyBenchmark3Levels4Fields_Node3)
{
    // declare local variables
    var $t0: $bc_ProphecyBenchmark3Levels4Fields_Node2;
    var $t1: int;
    var $t2: $bc_ProphecyBenchmark3Levels4Fields_Node2;
    var $t3: $bc_ProphecyBenchmark3Levels4Fields_Node2;
    var $t4: $bc_ProphecyBenchmark3Levels4Fields_Node2;
    var $t5: $bc_ProphecyBenchmark3Levels4Fields_Node2;
    var $t6: $bc_ProphecyBenchmark3Levels4Fields_Node2;
    var $t7: $bc_ProphecyBenchmark3Levels4Fields_Node2;
    var $t8: $bc_ProphecyBenchmark3Levels4Fields_Node2;
    var $t9: $bc_ProphecyBenchmark3Levels4Fields_Node3;
    var $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3': $bc_ProphecyBenchmark3Levels4Fields_Node3;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t0 := ProphecyBenchmark3Levels4Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:42:17+11
    assume {:print "$at(3,1291,1302)"} true;
    call $t0 := $bc_ProphecyBenchmark3Levels4Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1291,1302)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t2 := ProphecyBenchmark3Levels4Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:42:34+11
    call $t2 := $bc_ProphecyBenchmark3Levels4Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1308,1319)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t3 := ProphecyBenchmark3Levels4Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:42:51+11
    call $t3 := $bc_ProphecyBenchmark3Levels4Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1325,1336)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t4 := ProphecyBenchmark3Levels4Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:42:68+11
    call $t4 := $bc_ProphecyBenchmark3Levels4Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1342,1353)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t5 := ProphecyBenchmark3Levels4Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:43:17+11
    assume {:print "$at(3,1372,1383)"} true;
    call $t5 := $bc_ProphecyBenchmark3Levels4Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1372,1383)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t6 := ProphecyBenchmark3Levels4Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:43:34+11
    call $t6 := $bc_ProphecyBenchmark3Levels4Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1389,1400)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t7 := ProphecyBenchmark3Levels4Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:43:51+11
    call $t7 := $bc_ProphecyBenchmark3Levels4Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1406,1417)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t8 := ProphecyBenchmark3Levels4Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:43:68+11
    call $t8 := $bc_ProphecyBenchmark3Levels4Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1423,1434)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t9 := pack 0xbc::ProphecyBenchmark3Levels4Fields::Node3($t0, $t2, $t3, $t4, $t5, $t6, $t7, $t8) at .\sources\ConditionalBorrowChain.move:41:9+179
    assume {:print "$at(3,1266,1445)"} true;
    $t9 := $bc_ProphecyBenchmark3Levels4Fields_Node3($t0, $t2, $t3, $t4, $t5, $t6, $t7, $t8);

    // trace_return[0]($t9) at .\sources\ConditionalBorrowChain.move:41:9+179
    assume {:print "$track_return(2,3,0):", $t9} $t9 == $t9;

    // label L1 at .\sources\ConditionalBorrowChain.move:45:5+1
    assume {:print "$at(3,1450,1451)"} true;
L1:

    // return $t9 at .\sources\ConditionalBorrowChain.move:45:5+1
    assume {:print "$at(3,1450,1451)"} true;
    $ret0 := $t9;
    return;

    // label L2 at .\sources\ConditionalBorrowChain.move:45:5+1
L2:

    // abort($t1) at .\sources\ConditionalBorrowChain.move:45:5+1
    assume {:print "$at(3,1450,1451)"} true;
    $abort_code := $t1;
    $abort_flag := true;
    return;

}

// fun ProphecyBenchmark3Levels4Fields::select_leaf [baseline] at .\sources\ConditionalBorrowChain.move:72:5+187
procedure {:inline 1} $bc_ProphecyBenchmark3Levels4Fields_select_leaf(_$t0: $Mutation ($bc_ProphecyBenchmark3Levels4Fields_Node1), _$t1: int) returns ($ret0: $Mutation (int), $ret1: $Mutation ($bc_ProphecyBenchmark3Levels4Fields_Node1))
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
    var $t12: $Mutation (int);
    var $t0: $Mutation ($bc_ProphecyBenchmark3Levels4Fields_Node1);
    var $t1: int;
    var $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1': $bc_ProphecyBenchmark3Levels4Fields_Node1;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:72:5+1
    assume {:print "$at(3,2323,2324)"} true;
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1' := $Dereference($t0);
    assume {:print "$track_local(2,4,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1';

    // trace_local[idx]($t1) at .\sources\ConditionalBorrowChain.move:72:5+1
    assume {:print "$track_local(2,4,1):", $t1} $t1 == $t1;

    // $t2 := 0 at .\sources\ConditionalBorrowChain.move:73:20+1
    assume {:print "$at(3,2395,2396)"} true;
    $t2 := 0;
    assume $IsValid'u64'($t2);

    // $t3 := ==($t1, $t2) at .\sources\ConditionalBorrowChain.move:73:13+8
    $t3 := $IsEqual'u64'($t1, $t2);

    // if ($t3) goto L1 else goto L0 at .\sources\ConditionalBorrowChain.move:73:9+120
    if ($t3) { goto L1; } else { goto L0; }

    // label L1 at .\sources\ConditionalBorrowChain.move:73:25+9
L1:

    // $t4 := borrow_field<0xbc::ProphecyBenchmark3Levels4Fields::Node1>.v0($t0) at .\sources\ConditionalBorrowChain.move:73:25+9
    assume {:print "$at(3,2400,2409)"} true;
    $t4 := $ChildMutation($t0, 0, $Dereference($t0)->$v0);

    // trace_return[0]($t4) at .\sources\ConditionalBorrowChain.move:73:9+120
    $temp_0'u64' := $Dereference($t4);
    assume {:print "$track_return(2,4,0):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:73:9+120
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1' := $Dereference($t0);
    assume {:print "$track_local(2,4,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:73:9+120
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1' := $Dereference($t0);
    assume {:print "$track_local(2,4,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1';

    // $t5 := move($t4) at .\sources\ConditionalBorrowChain.move:73:9+120
    $t5 := $t4;

    // goto L6 at .\sources\ConditionalBorrowChain.move:73:9+120
    goto L6;

    // label L0 at .\sources\ConditionalBorrowChain.move:73:46+3
L0:

    // $t6 := 1 at .\sources\ConditionalBorrowChain.move:73:53+1
    assume {:print "$at(3,2428,2429)"} true;
    $t6 := 1;
    assume $IsValid'u64'($t6);

    // $t7 := ==($t1, $t6) at .\sources\ConditionalBorrowChain.move:73:46+8
    $t7 := $IsEqual'u64'($t1, $t6);

    // if ($t7) goto L3 else goto L2 at .\sources\ConditionalBorrowChain.move:73:42+87
    if ($t7) { goto L3; } else { goto L2; }

    // label L3 at .\sources\ConditionalBorrowChain.move:73:58+9
L3:

    // $t8 := borrow_field<0xbc::ProphecyBenchmark3Levels4Fields::Node1>.v1($t0) at .\sources\ConditionalBorrowChain.move:73:58+9
    assume {:print "$at(3,2433,2442)"} true;
    $t8 := $ChildMutation($t0, 1, $Dereference($t0)->$v1);

    // trace_return[0]($t8) at .\sources\ConditionalBorrowChain.move:73:9+120
    $temp_0'u64' := $Dereference($t8);
    assume {:print "$track_return(2,4,0):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:73:9+120
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1' := $Dereference($t0);
    assume {:print "$track_local(2,4,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:73:9+120
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1' := $Dereference($t0);
    assume {:print "$track_local(2,4,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1';

    // $t5 := move($t8) at .\sources\ConditionalBorrowChain.move:73:9+120
    $t5 := $t8;

    // goto L6 at .\sources\ConditionalBorrowChain.move:73:9+120
    goto L6;

    // label L2 at .\sources\ConditionalBorrowChain.move:74:18+3
    assume {:print "$at(3,2462,2465)"} true;
L2:

    // $t9 := 2 at .\sources\ConditionalBorrowChain.move:74:25+1
    assume {:print "$at(3,2469,2470)"} true;
    $t9 := 2;
    assume $IsValid'u64'($t9);

    // $t10 := ==($t1, $t9) at .\sources\ConditionalBorrowChain.move:74:18+8
    $t10 := $IsEqual'u64'($t1, $t9);

    // if ($t10) goto L5 else goto L4 at .\sources\ConditionalBorrowChain.move:74:14+46
    if ($t10) { goto L5; } else { goto L4; }

    // label L5 at .\sources\ConditionalBorrowChain.move:74:30+9
L5:

    // $t11 := borrow_field<0xbc::ProphecyBenchmark3Levels4Fields::Node1>.v2($t0) at .\sources\ConditionalBorrowChain.move:74:30+9
    assume {:print "$at(3,2474,2483)"} true;
    $t11 := $ChildMutation($t0, 2, $Dereference($t0)->$v2);

    // trace_return[0]($t11) at .\sources\ConditionalBorrowChain.move:73:9+120
    assume {:print "$at(3,2384,2504)"} true;
    $temp_0'u64' := $Dereference($t11);
    assume {:print "$track_return(2,4,0):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:73:9+120
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1' := $Dereference($t0);
    assume {:print "$track_local(2,4,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:73:9+120
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1' := $Dereference($t0);
    assume {:print "$track_local(2,4,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1';

    // $t5 := move($t11) at .\sources\ConditionalBorrowChain.move:73:9+120
    $t5 := $t11;

    // goto L6 at .\sources\ConditionalBorrowChain.move:73:9+120
    goto L6;

    // label L4 at .\sources\ConditionalBorrowChain.move:74:49+9
    assume {:print "$at(3,2493,2502)"} true;
L4:

    // $t12 := borrow_field<0xbc::ProphecyBenchmark3Levels4Fields::Node1>.v3($t0) at .\sources\ConditionalBorrowChain.move:74:49+9
    assume {:print "$at(3,2493,2502)"} true;
    $t12 := $ChildMutation($t0, 3, $Dereference($t0)->$v3);

    // trace_return[0]($t12) at .\sources\ConditionalBorrowChain.move:73:9+120
    assume {:print "$at(3,2384,2504)"} true;
    $temp_0'u64' := $Dereference($t12);
    assume {:print "$track_return(2,4,0):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:73:9+120
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1' := $Dereference($t0);
    assume {:print "$track_local(2,4,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:73:9+120
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1' := $Dereference($t0);
    assume {:print "$track_local(2,4,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1';

    // $t5 := move($t12) at .\sources\ConditionalBorrowChain.move:73:9+120
    $t5 := $t12;

    // label L6 at .\sources\ConditionalBorrowChain.move:75:5+1
    assume {:print "$at(3,2509,2510)"} true;
L6:

    // return $t5 at .\sources\ConditionalBorrowChain.move:75:5+1
    assume {:print "$at(3,2509,2510)"} true;
    $ret0 := $t5;
    $ret1 := $t0;
    return;

}

// fun ProphecyBenchmark3Levels4Fields::select_n1 [baseline] at .\sources\ConditionalBorrowChain.move:62:5+187
procedure {:inline 1} $bc_ProphecyBenchmark3Levels4Fields_select_n1(_$t0: $Mutation ($bc_ProphecyBenchmark3Levels4Fields_Node2), _$t1: int) returns ($ret0: $Mutation ($bc_ProphecyBenchmark3Levels4Fields_Node1), $ret1: $Mutation ($bc_ProphecyBenchmark3Levels4Fields_Node2))
{
    // declare local variables
    var $t2: int;
    var $t3: bool;
    var $t4: $Mutation ($bc_ProphecyBenchmark3Levels4Fields_Node1);
    var $t5: $Mutation ($bc_ProphecyBenchmark3Levels4Fields_Node1);
    var $t6: int;
    var $t7: bool;
    var $t8: $Mutation ($bc_ProphecyBenchmark3Levels4Fields_Node1);
    var $t9: int;
    var $t10: bool;
    var $t11: $Mutation ($bc_ProphecyBenchmark3Levels4Fields_Node1);
    var $t12: $Mutation ($bc_ProphecyBenchmark3Levels4Fields_Node1);
    var $t0: $Mutation ($bc_ProphecyBenchmark3Levels4Fields_Node2);
    var $t1: int;
    var $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1': $bc_ProphecyBenchmark3Levels4Fields_Node1;
    var $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2': $bc_ProphecyBenchmark3Levels4Fields_Node2;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:62:5+1
    assume {:print "$at(3,1984,1985)"} true;
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2' := $Dereference($t0);
    assume {:print "$track_local(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2';

    // trace_local[idx]($t1) at .\sources\ConditionalBorrowChain.move:62:5+1
    assume {:print "$track_local(2,5,1):", $t1} $t1 == $t1;

    // $t2 := 0 at .\sources\ConditionalBorrowChain.move:63:20+1
    assume {:print "$at(3,2056,2057)"} true;
    $t2 := 0;
    assume $IsValid'u64'($t2);

    // $t3 := ==($t1, $t2) at .\sources\ConditionalBorrowChain.move:63:13+8
    $t3 := $IsEqual'u64'($t1, $t2);

    // if ($t3) goto L1 else goto L0 at .\sources\ConditionalBorrowChain.move:63:9+120
    if ($t3) { goto L1; } else { goto L0; }

    // label L1 at .\sources\ConditionalBorrowChain.move:63:25+9
L1:

    // $t4 := borrow_field<0xbc::ProphecyBenchmark3Levels4Fields::Node2>.v0($t0) at .\sources\ConditionalBorrowChain.move:63:25+9
    assume {:print "$at(3,2061,2070)"} true;
    $t4 := $ChildMutation($t0, 0, $Dereference($t0)->$v0);

    // trace_return[0]($t4) at .\sources\ConditionalBorrowChain.move:63:9+120
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1' := $Dereference($t4);
    assume {:print "$track_return(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:63:9+120
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2' := $Dereference($t0);
    assume {:print "$track_local(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:63:9+120
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2' := $Dereference($t0);
    assume {:print "$track_local(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2';

    // $t5 := move($t4) at .\sources\ConditionalBorrowChain.move:63:9+120
    $t5 := $t4;

    // goto L6 at .\sources\ConditionalBorrowChain.move:63:9+120
    goto L6;

    // label L0 at .\sources\ConditionalBorrowChain.move:63:46+3
L0:

    // $t6 := 1 at .\sources\ConditionalBorrowChain.move:63:53+1
    assume {:print "$at(3,2089,2090)"} true;
    $t6 := 1;
    assume $IsValid'u64'($t6);

    // $t7 := ==($t1, $t6) at .\sources\ConditionalBorrowChain.move:63:46+8
    $t7 := $IsEqual'u64'($t1, $t6);

    // if ($t7) goto L3 else goto L2 at .\sources\ConditionalBorrowChain.move:63:42+87
    if ($t7) { goto L3; } else { goto L2; }

    // label L3 at .\sources\ConditionalBorrowChain.move:63:58+9
L3:

    // $t8 := borrow_field<0xbc::ProphecyBenchmark3Levels4Fields::Node2>.v1($t0) at .\sources\ConditionalBorrowChain.move:63:58+9
    assume {:print "$at(3,2094,2103)"} true;
    $t8 := $ChildMutation($t0, 1, $Dereference($t0)->$v1);

    // trace_return[0]($t8) at .\sources\ConditionalBorrowChain.move:63:9+120
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1' := $Dereference($t8);
    assume {:print "$track_return(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:63:9+120
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2' := $Dereference($t0);
    assume {:print "$track_local(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:63:9+120
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2' := $Dereference($t0);
    assume {:print "$track_local(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2';

    // $t5 := move($t8) at .\sources\ConditionalBorrowChain.move:63:9+120
    $t5 := $t8;

    // goto L6 at .\sources\ConditionalBorrowChain.move:63:9+120
    goto L6;

    // label L2 at .\sources\ConditionalBorrowChain.move:64:18+3
    assume {:print "$at(3,2123,2126)"} true;
L2:

    // $t9 := 2 at .\sources\ConditionalBorrowChain.move:64:25+1
    assume {:print "$at(3,2130,2131)"} true;
    $t9 := 2;
    assume $IsValid'u64'($t9);

    // $t10 := ==($t1, $t9) at .\sources\ConditionalBorrowChain.move:64:18+8
    $t10 := $IsEqual'u64'($t1, $t9);

    // if ($t10) goto L5 else goto L4 at .\sources\ConditionalBorrowChain.move:64:14+46
    if ($t10) { goto L5; } else { goto L4; }

    // label L5 at .\sources\ConditionalBorrowChain.move:64:30+9
L5:

    // $t11 := borrow_field<0xbc::ProphecyBenchmark3Levels4Fields::Node2>.v2($t0) at .\sources\ConditionalBorrowChain.move:64:30+9
    assume {:print "$at(3,2135,2144)"} true;
    $t11 := $ChildMutation($t0, 2, $Dereference($t0)->$v2);

    // trace_return[0]($t11) at .\sources\ConditionalBorrowChain.move:63:9+120
    assume {:print "$at(3,2045,2165)"} true;
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1' := $Dereference($t11);
    assume {:print "$track_return(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:63:9+120
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2' := $Dereference($t0);
    assume {:print "$track_local(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:63:9+120
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2' := $Dereference($t0);
    assume {:print "$track_local(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2';

    // $t5 := move($t11) at .\sources\ConditionalBorrowChain.move:63:9+120
    $t5 := $t11;

    // goto L6 at .\sources\ConditionalBorrowChain.move:63:9+120
    goto L6;

    // label L4 at .\sources\ConditionalBorrowChain.move:64:49+9
    assume {:print "$at(3,2154,2163)"} true;
L4:

    // $t12 := borrow_field<0xbc::ProphecyBenchmark3Levels4Fields::Node2>.v3($t0) at .\sources\ConditionalBorrowChain.move:64:49+9
    assume {:print "$at(3,2154,2163)"} true;
    $t12 := $ChildMutation($t0, 3, $Dereference($t0)->$v3);

    // trace_return[0]($t12) at .\sources\ConditionalBorrowChain.move:63:9+120
    assume {:print "$at(3,2045,2165)"} true;
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1' := $Dereference($t12);
    assume {:print "$track_return(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node1';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:63:9+120
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2' := $Dereference($t0);
    assume {:print "$track_local(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:63:9+120
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2' := $Dereference($t0);
    assume {:print "$track_local(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2';

    // $t5 := move($t12) at .\sources\ConditionalBorrowChain.move:63:9+120
    $t5 := $t12;

    // label L6 at .\sources\ConditionalBorrowChain.move:65:5+1
    assume {:print "$at(3,2170,2171)"} true;
L6:

    // return $t5 at .\sources\ConditionalBorrowChain.move:65:5+1
    assume {:print "$at(3,2170,2171)"} true;
    $ret0 := $t5;
    $ret1 := $t0;
    return;

}

// fun ProphecyBenchmark3Levels4Fields::select_n2 [baseline] at .\sources\ConditionalBorrowChain.move:52:5+187
procedure {:inline 1} $bc_ProphecyBenchmark3Levels4Fields_select_n2(_$t0: $Mutation ($bc_ProphecyBenchmark3Levels4Fields_Node3), _$t1: int) returns ($ret0: $Mutation ($bc_ProphecyBenchmark3Levels4Fields_Node2), $ret1: $Mutation ($bc_ProphecyBenchmark3Levels4Fields_Node3))
{
    // declare local variables
    var $t2: int;
    var $t3: bool;
    var $t4: $Mutation ($bc_ProphecyBenchmark3Levels4Fields_Node2);
    var $t5: $Mutation ($bc_ProphecyBenchmark3Levels4Fields_Node2);
    var $t6: int;
    var $t7: bool;
    var $t8: $Mutation ($bc_ProphecyBenchmark3Levels4Fields_Node2);
    var $t9: int;
    var $t10: bool;
    var $t11: $Mutation ($bc_ProphecyBenchmark3Levels4Fields_Node2);
    var $t12: $Mutation ($bc_ProphecyBenchmark3Levels4Fields_Node2);
    var $t0: $Mutation ($bc_ProphecyBenchmark3Levels4Fields_Node3);
    var $t1: int;
    var $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2': $bc_ProphecyBenchmark3Levels4Fields_Node2;
    var $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3': $bc_ProphecyBenchmark3Levels4Fields_Node3;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:52:5+1
    assume {:print "$at(3,1652,1653)"} true;
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3' := $Dereference($t0);
    assume {:print "$track_local(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3';

    // trace_local[idx]($t1) at .\sources\ConditionalBorrowChain.move:52:5+1
    assume {:print "$track_local(2,6,1):", $t1} $t1 == $t1;

    // $t2 := 0 at .\sources\ConditionalBorrowChain.move:53:20+1
    assume {:print "$at(3,1724,1725)"} true;
    $t2 := 0;
    assume $IsValid'u64'($t2);

    // $t3 := ==($t1, $t2) at .\sources\ConditionalBorrowChain.move:53:13+8
    $t3 := $IsEqual'u64'($t1, $t2);

    // if ($t3) goto L1 else goto L0 at .\sources\ConditionalBorrowChain.move:53:9+120
    if ($t3) { goto L1; } else { goto L0; }

    // label L1 at .\sources\ConditionalBorrowChain.move:53:25+9
L1:

    // $t4 := borrow_field<0xbc::ProphecyBenchmark3Levels4Fields::Node3>.v0($t0) at .\sources\ConditionalBorrowChain.move:53:25+9
    assume {:print "$at(3,1729,1738)"} true;
    $t4 := $ChildMutation($t0, 0, $Dereference($t0)->$v0);

    // trace_return[0]($t4) at .\sources\ConditionalBorrowChain.move:53:9+120
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2' := $Dereference($t4);
    assume {:print "$track_return(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:53:9+120
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3' := $Dereference($t0);
    assume {:print "$track_local(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:53:9+120
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3' := $Dereference($t0);
    assume {:print "$track_local(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3';

    // $t5 := move($t4) at .\sources\ConditionalBorrowChain.move:53:9+120
    $t5 := $t4;

    // goto L6 at .\sources\ConditionalBorrowChain.move:53:9+120
    goto L6;

    // label L0 at .\sources\ConditionalBorrowChain.move:53:46+3
L0:

    // $t6 := 1 at .\sources\ConditionalBorrowChain.move:53:53+1
    assume {:print "$at(3,1757,1758)"} true;
    $t6 := 1;
    assume $IsValid'u64'($t6);

    // $t7 := ==($t1, $t6) at .\sources\ConditionalBorrowChain.move:53:46+8
    $t7 := $IsEqual'u64'($t1, $t6);

    // if ($t7) goto L3 else goto L2 at .\sources\ConditionalBorrowChain.move:53:42+87
    if ($t7) { goto L3; } else { goto L2; }

    // label L3 at .\sources\ConditionalBorrowChain.move:53:58+9
L3:

    // $t8 := borrow_field<0xbc::ProphecyBenchmark3Levels4Fields::Node3>.v1($t0) at .\sources\ConditionalBorrowChain.move:53:58+9
    assume {:print "$at(3,1762,1771)"} true;
    $t8 := $ChildMutation($t0, 1, $Dereference($t0)->$v1);

    // trace_return[0]($t8) at .\sources\ConditionalBorrowChain.move:53:9+120
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2' := $Dereference($t8);
    assume {:print "$track_return(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:53:9+120
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3' := $Dereference($t0);
    assume {:print "$track_local(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:53:9+120
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3' := $Dereference($t0);
    assume {:print "$track_local(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3';

    // $t5 := move($t8) at .\sources\ConditionalBorrowChain.move:53:9+120
    $t5 := $t8;

    // goto L6 at .\sources\ConditionalBorrowChain.move:53:9+120
    goto L6;

    // label L2 at .\sources\ConditionalBorrowChain.move:54:18+3
    assume {:print "$at(3,1791,1794)"} true;
L2:

    // $t9 := 2 at .\sources\ConditionalBorrowChain.move:54:25+1
    assume {:print "$at(3,1798,1799)"} true;
    $t9 := 2;
    assume $IsValid'u64'($t9);

    // $t10 := ==($t1, $t9) at .\sources\ConditionalBorrowChain.move:54:18+8
    $t10 := $IsEqual'u64'($t1, $t9);

    // if ($t10) goto L5 else goto L4 at .\sources\ConditionalBorrowChain.move:54:14+46
    if ($t10) { goto L5; } else { goto L4; }

    // label L5 at .\sources\ConditionalBorrowChain.move:54:30+9
L5:

    // $t11 := borrow_field<0xbc::ProphecyBenchmark3Levels4Fields::Node3>.v2($t0) at .\sources\ConditionalBorrowChain.move:54:30+9
    assume {:print "$at(3,1803,1812)"} true;
    $t11 := $ChildMutation($t0, 2, $Dereference($t0)->$v2);

    // trace_return[0]($t11) at .\sources\ConditionalBorrowChain.move:53:9+120
    assume {:print "$at(3,1713,1833)"} true;
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2' := $Dereference($t11);
    assume {:print "$track_return(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:53:9+120
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3' := $Dereference($t0);
    assume {:print "$track_local(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:53:9+120
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3' := $Dereference($t0);
    assume {:print "$track_local(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3';

    // $t5 := move($t11) at .\sources\ConditionalBorrowChain.move:53:9+120
    $t5 := $t11;

    // goto L6 at .\sources\ConditionalBorrowChain.move:53:9+120
    goto L6;

    // label L4 at .\sources\ConditionalBorrowChain.move:54:49+9
    assume {:print "$at(3,1822,1831)"} true;
L4:

    // $t12 := borrow_field<0xbc::ProphecyBenchmark3Levels4Fields::Node3>.v3($t0) at .\sources\ConditionalBorrowChain.move:54:49+9
    assume {:print "$at(3,1822,1831)"} true;
    $t12 := $ChildMutation($t0, 3, $Dereference($t0)->$v3);

    // trace_return[0]($t12) at .\sources\ConditionalBorrowChain.move:53:9+120
    assume {:print "$at(3,1713,1833)"} true;
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2' := $Dereference($t12);
    assume {:print "$track_return(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node2';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:53:9+120
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3' := $Dereference($t0);
    assume {:print "$track_local(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:53:9+120
    $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3' := $Dereference($t0);
    assume {:print "$track_local(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3'} $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3' == $temp_0'$bc_ProphecyBenchmark3Levels4Fields_Node3';

    // $t5 := move($t12) at .\sources\ConditionalBorrowChain.move:53:9+120
    $t5 := $t12;

    // label L6 at .\sources\ConditionalBorrowChain.move:55:5+1
    assume {:print "$at(3,1838,1839)"} true;
L6:

    // return $t5 at .\sources\ConditionalBorrowChain.move:55:5+1
    assume {:print "$at(3,1838,1839)"} true;
    $ret0 := $t5;
    $ret1 := $t0;
    return;

}
