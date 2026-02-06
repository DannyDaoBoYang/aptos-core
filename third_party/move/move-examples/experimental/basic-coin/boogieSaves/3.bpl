
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


function $Arbitrary_value_of'$bc_ProphecyBenchmark3Levels3Fields_Node1'(): $bc_ProphecyBenchmark3Levels3Fields_Node1;



function $Arbitrary_value_of'$bc_ProphecyBenchmark3Levels3Fields_Node2'(): $bc_ProphecyBenchmark3Levels3Fields_Node2;



function $Arbitrary_value_of'$bc_ProphecyBenchmark3Levels3Fields_Node3'(): $bc_ProphecyBenchmark3Levels3Fields_Node3;



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


// struct ProphecyBenchmark3Levels3Fields::Node1 at .\sources\ConditionalBorrowChain.move:8:5+131
datatype $bc_ProphecyBenchmark3Levels3Fields_Node1 {
    $bc_ProphecyBenchmark3Levels3Fields_Node1($v0: int, $v1: int, $v2: int, $v3: int, $v4: int, $v5: int, $v6: int, $v7: int)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v0(s: $bc_ProphecyBenchmark3Levels3Fields_Node1, x: int): $bc_ProphecyBenchmark3Levels3Fields_Node1 {
    $bc_ProphecyBenchmark3Levels3Fields_Node1(x, s->$v1, s->$v2, s->$v3, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v1(s: $bc_ProphecyBenchmark3Levels3Fields_Node1, x: int): $bc_ProphecyBenchmark3Levels3Fields_Node1 {
    $bc_ProphecyBenchmark3Levels3Fields_Node1(s->$v0, x, s->$v2, s->$v3, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v2(s: $bc_ProphecyBenchmark3Levels3Fields_Node1, x: int): $bc_ProphecyBenchmark3Levels3Fields_Node1 {
    $bc_ProphecyBenchmark3Levels3Fields_Node1(s->$v0, s->$v1, x, s->$v3, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v3(s: $bc_ProphecyBenchmark3Levels3Fields_Node1, x: int): $bc_ProphecyBenchmark3Levels3Fields_Node1 {
    $bc_ProphecyBenchmark3Levels3Fields_Node1(s->$v0, s->$v1, s->$v2, x, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v4(s: $bc_ProphecyBenchmark3Levels3Fields_Node1, x: int): $bc_ProphecyBenchmark3Levels3Fields_Node1 {
    $bc_ProphecyBenchmark3Levels3Fields_Node1(s->$v0, s->$v1, s->$v2, s->$v3, x, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v5(s: $bc_ProphecyBenchmark3Levels3Fields_Node1, x: int): $bc_ProphecyBenchmark3Levels3Fields_Node1 {
    $bc_ProphecyBenchmark3Levels3Fields_Node1(s->$v0, s->$v1, s->$v2, s->$v3, s->$v4, x, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v6(s: $bc_ProphecyBenchmark3Levels3Fields_Node1, x: int): $bc_ProphecyBenchmark3Levels3Fields_Node1 {
    $bc_ProphecyBenchmark3Levels3Fields_Node1(s->$v0, s->$v1, s->$v2, s->$v3, s->$v4, s->$v5, x, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v7(s: $bc_ProphecyBenchmark3Levels3Fields_Node1, x: int): $bc_ProphecyBenchmark3Levels3Fields_Node1 {
    $bc_ProphecyBenchmark3Levels3Fields_Node1(s->$v0, s->$v1, s->$v2, s->$v3, s->$v4, s->$v5, s->$v6, x)
}
function $IsValid'$bc_ProphecyBenchmark3Levels3Fields_Node1'(s: $bc_ProphecyBenchmark3Levels3Fields_Node1): bool {
    $IsValid'u64'(s->$v0)
      && $IsValid'u64'(s->$v1)
      && $IsValid'u64'(s->$v2)
      && $IsValid'u64'(s->$v3)
      && $IsValid'u64'(s->$v4)
      && $IsValid'u64'(s->$v5)
      && $IsValid'u64'(s->$v6)
      && $IsValid'u64'(s->$v7)
}
function {:inline} $IsEqual'$bc_ProphecyBenchmark3Levels3Fields_Node1'(s1: $bc_ProphecyBenchmark3Levels3Fields_Node1, s2: $bc_ProphecyBenchmark3Levels3Fields_Node1): bool {
    s1 == s2
}

// struct ProphecyBenchmark3Levels3Fields::Node2 at .\sources\ConditionalBorrowChain.move:14:5+147
datatype $bc_ProphecyBenchmark3Levels3Fields_Node2 {
    $bc_ProphecyBenchmark3Levels3Fields_Node2($v0: $bc_ProphecyBenchmark3Levels3Fields_Node1, $v1: $bc_ProphecyBenchmark3Levels3Fields_Node1, $v2: $bc_ProphecyBenchmark3Levels3Fields_Node1, $v3: $bc_ProphecyBenchmark3Levels3Fields_Node1, $v4: $bc_ProphecyBenchmark3Levels3Fields_Node1, $v5: $bc_ProphecyBenchmark3Levels3Fields_Node1, $v6: $bc_ProphecyBenchmark3Levels3Fields_Node1, $v7: $bc_ProphecyBenchmark3Levels3Fields_Node1)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v0(s: $bc_ProphecyBenchmark3Levels3Fields_Node2, x: $bc_ProphecyBenchmark3Levels3Fields_Node1): $bc_ProphecyBenchmark3Levels3Fields_Node2 {
    $bc_ProphecyBenchmark3Levels3Fields_Node2(x, s->$v1, s->$v2, s->$v3, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v1(s: $bc_ProphecyBenchmark3Levels3Fields_Node2, x: $bc_ProphecyBenchmark3Levels3Fields_Node1): $bc_ProphecyBenchmark3Levels3Fields_Node2 {
    $bc_ProphecyBenchmark3Levels3Fields_Node2(s->$v0, x, s->$v2, s->$v3, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v2(s: $bc_ProphecyBenchmark3Levels3Fields_Node2, x: $bc_ProphecyBenchmark3Levels3Fields_Node1): $bc_ProphecyBenchmark3Levels3Fields_Node2 {
    $bc_ProphecyBenchmark3Levels3Fields_Node2(s->$v0, s->$v1, x, s->$v3, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v3(s: $bc_ProphecyBenchmark3Levels3Fields_Node2, x: $bc_ProphecyBenchmark3Levels3Fields_Node1): $bc_ProphecyBenchmark3Levels3Fields_Node2 {
    $bc_ProphecyBenchmark3Levels3Fields_Node2(s->$v0, s->$v1, s->$v2, x, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v4(s: $bc_ProphecyBenchmark3Levels3Fields_Node2, x: $bc_ProphecyBenchmark3Levels3Fields_Node1): $bc_ProphecyBenchmark3Levels3Fields_Node2 {
    $bc_ProphecyBenchmark3Levels3Fields_Node2(s->$v0, s->$v1, s->$v2, s->$v3, x, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v5(s: $bc_ProphecyBenchmark3Levels3Fields_Node2, x: $bc_ProphecyBenchmark3Levels3Fields_Node1): $bc_ProphecyBenchmark3Levels3Fields_Node2 {
    $bc_ProphecyBenchmark3Levels3Fields_Node2(s->$v0, s->$v1, s->$v2, s->$v3, s->$v4, x, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v6(s: $bc_ProphecyBenchmark3Levels3Fields_Node2, x: $bc_ProphecyBenchmark3Levels3Fields_Node1): $bc_ProphecyBenchmark3Levels3Fields_Node2 {
    $bc_ProphecyBenchmark3Levels3Fields_Node2(s->$v0, s->$v1, s->$v2, s->$v3, s->$v4, s->$v5, x, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v7(s: $bc_ProphecyBenchmark3Levels3Fields_Node2, x: $bc_ProphecyBenchmark3Levels3Fields_Node1): $bc_ProphecyBenchmark3Levels3Fields_Node2 {
    $bc_ProphecyBenchmark3Levels3Fields_Node2(s->$v0, s->$v1, s->$v2, s->$v3, s->$v4, s->$v5, s->$v6, x)
}
function $IsValid'$bc_ProphecyBenchmark3Levels3Fields_Node2'(s: $bc_ProphecyBenchmark3Levels3Fields_Node2): bool {
    $IsValid'$bc_ProphecyBenchmark3Levels3Fields_Node1'(s->$v0)
      && $IsValid'$bc_ProphecyBenchmark3Levels3Fields_Node1'(s->$v1)
      && $IsValid'$bc_ProphecyBenchmark3Levels3Fields_Node1'(s->$v2)
      && $IsValid'$bc_ProphecyBenchmark3Levels3Fields_Node1'(s->$v3)
      && $IsValid'$bc_ProphecyBenchmark3Levels3Fields_Node1'(s->$v4)
      && $IsValid'$bc_ProphecyBenchmark3Levels3Fields_Node1'(s->$v5)
      && $IsValid'$bc_ProphecyBenchmark3Levels3Fields_Node1'(s->$v6)
      && $IsValid'$bc_ProphecyBenchmark3Levels3Fields_Node1'(s->$v7)
}
function {:inline} $IsEqual'$bc_ProphecyBenchmark3Levels3Fields_Node2'(s1: $bc_ProphecyBenchmark3Levels3Fields_Node2, s2: $bc_ProphecyBenchmark3Levels3Fields_Node2): bool {
    s1 == s2
}

// struct ProphecyBenchmark3Levels3Fields::Node3 at .\sources\ConditionalBorrowChain.move:20:5+147
datatype $bc_ProphecyBenchmark3Levels3Fields_Node3 {
    $bc_ProphecyBenchmark3Levels3Fields_Node3($v0: $bc_ProphecyBenchmark3Levels3Fields_Node2, $v1: $bc_ProphecyBenchmark3Levels3Fields_Node2, $v2: $bc_ProphecyBenchmark3Levels3Fields_Node2, $v3: $bc_ProphecyBenchmark3Levels3Fields_Node2, $v4: $bc_ProphecyBenchmark3Levels3Fields_Node2, $v5: $bc_ProphecyBenchmark3Levels3Fields_Node2, $v6: $bc_ProphecyBenchmark3Levels3Fields_Node2, $v7: $bc_ProphecyBenchmark3Levels3Fields_Node2)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v0(s: $bc_ProphecyBenchmark3Levels3Fields_Node3, x: $bc_ProphecyBenchmark3Levels3Fields_Node2): $bc_ProphecyBenchmark3Levels3Fields_Node3 {
    $bc_ProphecyBenchmark3Levels3Fields_Node3(x, s->$v1, s->$v2, s->$v3, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v1(s: $bc_ProphecyBenchmark3Levels3Fields_Node3, x: $bc_ProphecyBenchmark3Levels3Fields_Node2): $bc_ProphecyBenchmark3Levels3Fields_Node3 {
    $bc_ProphecyBenchmark3Levels3Fields_Node3(s->$v0, x, s->$v2, s->$v3, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v2(s: $bc_ProphecyBenchmark3Levels3Fields_Node3, x: $bc_ProphecyBenchmark3Levels3Fields_Node2): $bc_ProphecyBenchmark3Levels3Fields_Node3 {
    $bc_ProphecyBenchmark3Levels3Fields_Node3(s->$v0, s->$v1, x, s->$v3, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v3(s: $bc_ProphecyBenchmark3Levels3Fields_Node3, x: $bc_ProphecyBenchmark3Levels3Fields_Node2): $bc_ProphecyBenchmark3Levels3Fields_Node3 {
    $bc_ProphecyBenchmark3Levels3Fields_Node3(s->$v0, s->$v1, s->$v2, x, s->$v4, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v4(s: $bc_ProphecyBenchmark3Levels3Fields_Node3, x: $bc_ProphecyBenchmark3Levels3Fields_Node2): $bc_ProphecyBenchmark3Levels3Fields_Node3 {
    $bc_ProphecyBenchmark3Levels3Fields_Node3(s->$v0, s->$v1, s->$v2, s->$v3, x, s->$v5, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v5(s: $bc_ProphecyBenchmark3Levels3Fields_Node3, x: $bc_ProphecyBenchmark3Levels3Fields_Node2): $bc_ProphecyBenchmark3Levels3Fields_Node3 {
    $bc_ProphecyBenchmark3Levels3Fields_Node3(s->$v0, s->$v1, s->$v2, s->$v3, s->$v4, x, s->$v6, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v6(s: $bc_ProphecyBenchmark3Levels3Fields_Node3, x: $bc_ProphecyBenchmark3Levels3Fields_Node2): $bc_ProphecyBenchmark3Levels3Fields_Node3 {
    $bc_ProphecyBenchmark3Levels3Fields_Node3(s->$v0, s->$v1, s->$v2, s->$v3, s->$v4, s->$v5, x, s->$v7)
}
function {:inline} $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v7(s: $bc_ProphecyBenchmark3Levels3Fields_Node3, x: $bc_ProphecyBenchmark3Levels3Fields_Node2): $bc_ProphecyBenchmark3Levels3Fields_Node3 {
    $bc_ProphecyBenchmark3Levels3Fields_Node3(s->$v0, s->$v1, s->$v2, s->$v3, s->$v4, s->$v5, s->$v6, x)
}
function $IsValid'$bc_ProphecyBenchmark3Levels3Fields_Node3'(s: $bc_ProphecyBenchmark3Levels3Fields_Node3): bool {
    $IsValid'$bc_ProphecyBenchmark3Levels3Fields_Node2'(s->$v0)
      && $IsValid'$bc_ProphecyBenchmark3Levels3Fields_Node2'(s->$v1)
      && $IsValid'$bc_ProphecyBenchmark3Levels3Fields_Node2'(s->$v2)
      && $IsValid'$bc_ProphecyBenchmark3Levels3Fields_Node2'(s->$v3)
      && $IsValid'$bc_ProphecyBenchmark3Levels3Fields_Node2'(s->$v4)
      && $IsValid'$bc_ProphecyBenchmark3Levels3Fields_Node2'(s->$v5)
      && $IsValid'$bc_ProphecyBenchmark3Levels3Fields_Node2'(s->$v6)
      && $IsValid'$bc_ProphecyBenchmark3Levels3Fields_Node2'(s->$v7)
}
function {:inline} $IsEqual'$bc_ProphecyBenchmark3Levels3Fields_Node3'(s1: $bc_ProphecyBenchmark3Levels3Fields_Node3, s2: $bc_ProphecyBenchmark3Levels3Fields_Node3): bool {
    s1 == s2
}

// fun ProphecyBenchmark3Levels3Fields::benchmark_from_scratch [verification] at .\sources\ConditionalBorrowChain.move:85:5+500
procedure {:timeLimit 40} $bc_ProphecyBenchmark3Levels3Fields_benchmark_from_scratch$verify(_$t0: int, _$t1: int, _$t2: int) returns ($ret0: $bc_ProphecyBenchmark3Levels3Fields_Node3)
{
    // declare local variables
    var $t3: $bc_ProphecyBenchmark3Levels3Fields_Node3;
    var $t4: $Mutation (int);
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: int;
    var $t10: int;
    var $t11: int;
    var $t12: $Mutation ($bc_ProphecyBenchmark3Levels3Fields_Node3);
    var $t13: $Mutation ($bc_ProphecyBenchmark3Levels3Fields_Node2);
    var $t14: $Mutation ($bc_ProphecyBenchmark3Levels3Fields_Node1);
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
    var $t154: $bc_ProphecyBenchmark3Levels3Fields_Node3;
    var $t0: int;
    var $t1: int;
    var $t2: int;
    var $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node3': $bc_ProphecyBenchmark3Levels3Fields_Node3;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at .\sources\ConditionalBorrowChain.move:85:5+1
    assume {:print "$at(3,2646,2647)"} true;
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

    // $t3 := ProphecyBenchmark3Levels3Fields::new_node3() on_abort goto L56 with $t5 at .\sources\ConditionalBorrowChain.move:88:20+11
    assume {:print "$at(3,2749,2760)"} true;
    call $t3 := $bc_ProphecyBenchmark3Levels3Fields_new_node3();
    if ($abort_flag) {
        assume {:print "$at(3,2749,2760)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,0):", $t5} $t5 == $t5;
        goto L56;
    }

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:88:20+11
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // $t6 := 8 at .\sources\ConditionalBorrowChain.move:90:25+1
    assume {:print "$at(3,2795,2796)"} true;
    $t6 := 8;
    assume $IsValid'u64'($t6);

    // $t7 := %($t0, $t6) on_abort goto L56 with $t5 at .\sources\ConditionalBorrowChain.move:90:20+6
    call $t7 := $Mod($t0, $t6);
    if ($abort_flag) {
        assume {:print "$at(3,2790,2796)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,0):", $t5} $t5 == $t5;
        goto L56;
    }

    // trace_local[c3]($t7) at .\sources\ConditionalBorrowChain.move:90:20+6
    assume {:print "$track_local(2,0,0):", $t7} $t7 == $t7;

    // $t8 := 8 at .\sources\ConditionalBorrowChain.move:91:25+1
    assume {:print "$at(3,2822,2823)"} true;
    $t8 := 8;
    assume $IsValid'u64'($t8);

    // $t9 := %($t1, $t8) on_abort goto L56 with $t5 at .\sources\ConditionalBorrowChain.move:91:20+6
    call $t9 := $Mod($t1, $t8);
    if ($abort_flag) {
        assume {:print "$at(3,2817,2823)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,0):", $t5} $t5 == $t5;
        goto L56;
    }

    // trace_local[c2]($t9) at .\sources\ConditionalBorrowChain.move:91:20+6
    assume {:print "$track_local(2,0,1):", $t9} $t9 == $t9;

    // $t10 := 8 at .\sources\ConditionalBorrowChain.move:92:25+1
    assume {:print "$at(3,2849,2850)"} true;
    $t10 := 8;
    assume $IsValid'u64'($t10);

    // $t11 := %($t2, $t10) on_abort goto L56 with $t5 at .\sources\ConditionalBorrowChain.move:92:20+6
    call $t11 := $Mod($t2, $t10);
    if ($abort_flag) {
        assume {:print "$at(3,2844,2850)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,0):", $t5} $t5 == $t5;
        goto L56;
    }

    // trace_local[c1]($t11) at .\sources\ConditionalBorrowChain.move:92:20+6
    assume {:print "$track_local(2,0,2):", $t11} $t11 == $t11;

    // $t12 := borrow_local($t3) at .\sources\ConditionalBorrowChain.move:94:22+9
    assume {:print "$at(3,2874,2883)"} true;
    $t12 := $Mutation($Local(3), EmptyVec(), $t3);

    // $t13 := ProphecyBenchmark3Levels3Fields::select_n2($t12, $t7) on_abort goto L56 with $t5 at .\sources\ConditionalBorrowChain.move:97:22+23
    assume {:print "$at(3,2971,2994)"} true;
    call $t13,$t12 := $bc_ProphecyBenchmark3Levels3Fields_select_n2($t12, $t7);
    if ($abort_flag) {
        assume {:print "$at(3,2971,2994)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,0):", $t5} $t5 == $t5;
        goto L56;
    }

    // $t14 := ProphecyBenchmark3Levels3Fields::select_n1($t13, $t9) on_abort goto L56 with $t5 at .\sources\ConditionalBorrowChain.move:98:22+23
    assume {:print "$at(3,3017,3040)"} true;
    call $t14,$t13 := $bc_ProphecyBenchmark3Levels3Fields_select_n1($t13, $t9);
    if ($abort_flag) {
        assume {:print "$at(3,3017,3040)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,0):", $t5} $t5 == $t5;
        goto L56;
    }

    // $t15 := ProphecyBenchmark3Levels3Fields::select_leaf($t14, $t11) on_abort goto L56 with $t5 at .\sources\ConditionalBorrowChain.move:99:24+25
    assume {:print "$at(3,3065,3090)"} true;
    call $t15,$t14 := $bc_ProphecyBenchmark3Levels3Fields_select_leaf($t14, $t11);
    if ($abort_flag) {
        assume {:print "$at(3,3065,3090)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,0):", $t5} $t5 == $t5;
        goto L56;
    }

    // trace_local[leaf_ref]($t15) at .\sources\ConditionalBorrowChain.move:99:24+25
    $temp_0'u64' := $Dereference($t15);
    assume {:print "$track_local(2,0,4):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t16 := read_ref($t15) at .\sources\ConditionalBorrowChain.move:100:21+9
    assume {:print "$at(3,3112,3121)"} true;
    $t16 := $Dereference($t15);

    // $t17 := 1 at .\sources\ConditionalBorrowChain.move:100:33+1
    $t17 := 1;
    assume $IsValid'u64'($t17);

    // $t18 := +($t16, $t17) on_abort goto L56 with $t5 at .\sources\ConditionalBorrowChain.move:100:21+13
    call $t18 := $AddU64($t16, $t17);
    if ($abort_flag) {
        assume {:print "$at(3,3112,3125)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,0):", $t5} $t5 == $t5;
        goto L56;
    }

    // write_ref($t15, $t18) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t15 := $UpdateMutation($t15, $t18);

    // $t19 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t19 := $IsParentMutation($t14, 0, $t15);

    // $t20 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t20 := $IsParentMutation($t13, 0, $t14);

    // $t21 := &&($t19, $t20) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t21 := $And($t19, $t20);

    // $t22 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t22 := $IsParentMutation($t12, 0, $t13);

    // $t23 := &&($t21, $t22) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t23 := $And($t21, $t22);

    // if ($t23) goto L1 else goto L2 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t23) { goto L1; } else { goto L2; }

    // label L1 at .\sources\ConditionalBorrowChain.move:100:9+25
L1:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L2 at .\sources\ConditionalBorrowChain.move:100:9+25
L2:

    // $t24 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t24 := $IsParentMutation($t14, 0, $t15);

    // $t25 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t25 := $IsParentMutation($t13, 0, $t14);

    // $t26 := &&($t24, $t25) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t26 := $And($t24, $t25);

    // $t27 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t27 := $IsParentMutation($t12, 1, $t13);

    // $t28 := &&($t26, $t27) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t28 := $And($t26, $t27);

    // if ($t28) goto L3 else goto L4 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t28) { goto L3; } else { goto L4; }

    // label L3 at .\sources\ConditionalBorrowChain.move:100:9+25
L3:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L4 at .\sources\ConditionalBorrowChain.move:100:9+25
L4:

    // $t29 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t29 := $IsParentMutation($t14, 0, $t15);

    // $t30 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t30 := $IsParentMutation($t13, 0, $t14);

    // $t31 := &&($t29, $t30) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t31 := $And($t29, $t30);

    // $t32 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t32 := $IsParentMutation($t12, 2, $t13);

    // $t33 := &&($t31, $t32) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t33 := $And($t31, $t32);

    // if ($t33) goto L5 else goto L6 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t33) { goto L5; } else { goto L6; }

    // label L5 at .\sources\ConditionalBorrowChain.move:100:9+25
L5:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L6 at .\sources\ConditionalBorrowChain.move:100:9+25
L6:

    // $t34 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t34 := $IsParentMutation($t14, 0, $t15);

    // $t35 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t35 := $IsParentMutation($t13, 1, $t14);

    // $t36 := &&($t34, $t35) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t36 := $And($t34, $t35);

    // $t37 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t37 := $IsParentMutation($t12, 0, $t13);

    // $t38 := &&($t36, $t37) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t38 := $And($t36, $t37);

    // if ($t38) goto L7 else goto L8 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t38) { goto L7; } else { goto L8; }

    // label L7 at .\sources\ConditionalBorrowChain.move:100:9+25
L7:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L8 at .\sources\ConditionalBorrowChain.move:100:9+25
L8:

    // $t39 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t39 := $IsParentMutation($t14, 0, $t15);

    // $t40 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t40 := $IsParentMutation($t13, 1, $t14);

    // $t41 := &&($t39, $t40) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t41 := $And($t39, $t40);

    // $t42 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t42 := $IsParentMutation($t12, 1, $t13);

    // $t43 := &&($t41, $t42) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t43 := $And($t41, $t42);

    // if ($t43) goto L9 else goto L10 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t43) { goto L9; } else { goto L10; }

    // label L9 at .\sources\ConditionalBorrowChain.move:100:9+25
L9:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L10 at .\sources\ConditionalBorrowChain.move:100:9+25
L10:

    // $t44 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t44 := $IsParentMutation($t14, 0, $t15);

    // $t45 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t45 := $IsParentMutation($t13, 1, $t14);

    // $t46 := &&($t44, $t45) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t46 := $And($t44, $t45);

    // $t47 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t47 := $IsParentMutation($t12, 2, $t13);

    // $t48 := &&($t46, $t47) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t48 := $And($t46, $t47);

    // if ($t48) goto L11 else goto L12 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t48) { goto L11; } else { goto L12; }

    // label L11 at .\sources\ConditionalBorrowChain.move:100:9+25
L11:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L12 at .\sources\ConditionalBorrowChain.move:100:9+25
L12:

    // $t49 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t49 := $IsParentMutation($t14, 0, $t15);

    // $t50 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t50 := $IsParentMutation($t13, 2, $t14);

    // $t51 := &&($t49, $t50) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t51 := $And($t49, $t50);

    // $t52 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t52 := $IsParentMutation($t12, 0, $t13);

    // $t53 := &&($t51, $t52) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t53 := $And($t51, $t52);

    // if ($t53) goto L13 else goto L14 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t53) { goto L13; } else { goto L14; }

    // label L13 at .\sources\ConditionalBorrowChain.move:100:9+25
L13:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L14 at .\sources\ConditionalBorrowChain.move:100:9+25
L14:

    // $t54 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t54 := $IsParentMutation($t14, 0, $t15);

    // $t55 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t55 := $IsParentMutation($t13, 2, $t14);

    // $t56 := &&($t54, $t55) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t56 := $And($t54, $t55);

    // $t57 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t57 := $IsParentMutation($t12, 1, $t13);

    // $t58 := &&($t56, $t57) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t58 := $And($t56, $t57);

    // if ($t58) goto L15 else goto L16 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t58) { goto L15; } else { goto L16; }

    // label L15 at .\sources\ConditionalBorrowChain.move:100:9+25
L15:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L16 at .\sources\ConditionalBorrowChain.move:100:9+25
L16:

    // $t59 := is_parent[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t59 := $IsParentMutation($t14, 0, $t15);

    // $t60 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t60 := $IsParentMutation($t13, 2, $t14);

    // $t61 := &&($t59, $t60) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t61 := $And($t59, $t60);

    // $t62 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t62 := $IsParentMutation($t12, 2, $t13);

    // $t63 := &&($t61, $t62) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t63 := $And($t61, $t62);

    // if ($t63) goto L17 else goto L18 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t63) { goto L17; } else { goto L18; }

    // label L17 at .\sources\ConditionalBorrowChain.move:100:9+25
L17:

    // write_back[Reference($t14).v0 (u64)]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v0($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L18 at .\sources\ConditionalBorrowChain.move:100:9+25
L18:

    // $t64 := is_parent[Reference($t14).v1 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t64 := $IsParentMutation($t14, 1, $t15);

    // $t65 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t65 := $IsParentMutation($t13, 0, $t14);

    // $t66 := &&($t64, $t65) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t66 := $And($t64, $t65);

    // $t67 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t67 := $IsParentMutation($t12, 0, $t13);

    // $t68 := &&($t66, $t67) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t68 := $And($t66, $t67);

    // if ($t68) goto L19 else goto L20 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t68) { goto L19; } else { goto L20; }

    // label L19 at .\sources\ConditionalBorrowChain.move:100:9+25
L19:

    // write_back[Reference($t14).v1 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L20 at .\sources\ConditionalBorrowChain.move:100:9+25
L20:

    // $t69 := is_parent[Reference($t14).v1 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t69 := $IsParentMutation($t14, 1, $t15);

    // $t70 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t70 := $IsParentMutation($t13, 0, $t14);

    // $t71 := &&($t69, $t70) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t71 := $And($t69, $t70);

    // $t72 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t72 := $IsParentMutation($t12, 1, $t13);

    // $t73 := &&($t71, $t72) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t73 := $And($t71, $t72);

    // if ($t73) goto L21 else goto L22 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t73) { goto L21; } else { goto L22; }

    // label L21 at .\sources\ConditionalBorrowChain.move:100:9+25
L21:

    // write_back[Reference($t14).v1 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L22 at .\sources\ConditionalBorrowChain.move:100:9+25
L22:

    // $t74 := is_parent[Reference($t14).v1 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t74 := $IsParentMutation($t14, 1, $t15);

    // $t75 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t75 := $IsParentMutation($t13, 0, $t14);

    // $t76 := &&($t74, $t75) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t76 := $And($t74, $t75);

    // $t77 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t77 := $IsParentMutation($t12, 2, $t13);

    // $t78 := &&($t76, $t77) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t78 := $And($t76, $t77);

    // if ($t78) goto L23 else goto L24 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t78) { goto L23; } else { goto L24; }

    // label L23 at .\sources\ConditionalBorrowChain.move:100:9+25
L23:

    // write_back[Reference($t14).v1 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L24 at .\sources\ConditionalBorrowChain.move:100:9+25
L24:

    // $t79 := is_parent[Reference($t14).v1 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t79 := $IsParentMutation($t14, 1, $t15);

    // $t80 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t80 := $IsParentMutation($t13, 1, $t14);

    // $t81 := &&($t79, $t80) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t81 := $And($t79, $t80);

    // $t82 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t82 := $IsParentMutation($t12, 0, $t13);

    // $t83 := &&($t81, $t82) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t83 := $And($t81, $t82);

    // if ($t83) goto L25 else goto L26 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t83) { goto L25; } else { goto L26; }

    // label L25 at .\sources\ConditionalBorrowChain.move:100:9+25
L25:

    // write_back[Reference($t14).v1 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L26 at .\sources\ConditionalBorrowChain.move:100:9+25
L26:

    // $t84 := is_parent[Reference($t14).v1 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t84 := $IsParentMutation($t14, 1, $t15);

    // $t85 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t85 := $IsParentMutation($t13, 1, $t14);

    // $t86 := &&($t84, $t85) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t86 := $And($t84, $t85);

    // $t87 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t87 := $IsParentMutation($t12, 1, $t13);

    // $t88 := &&($t86, $t87) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t88 := $And($t86, $t87);

    // if ($t88) goto L27 else goto L28 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t88) { goto L27; } else { goto L28; }

    // label L27 at .\sources\ConditionalBorrowChain.move:100:9+25
L27:

    // write_back[Reference($t14).v1 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L28 at .\sources\ConditionalBorrowChain.move:100:9+25
L28:

    // $t89 := is_parent[Reference($t14).v1 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t89 := $IsParentMutation($t14, 1, $t15);

    // $t90 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t90 := $IsParentMutation($t13, 1, $t14);

    // $t91 := &&($t89, $t90) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t91 := $And($t89, $t90);

    // $t92 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t92 := $IsParentMutation($t12, 2, $t13);

    // $t93 := &&($t91, $t92) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t93 := $And($t91, $t92);

    // if ($t93) goto L29 else goto L30 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t93) { goto L29; } else { goto L30; }

    // label L29 at .\sources\ConditionalBorrowChain.move:100:9+25
L29:

    // write_back[Reference($t14).v1 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L30 at .\sources\ConditionalBorrowChain.move:100:9+25
L30:

    // $t94 := is_parent[Reference($t14).v1 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t94 := $IsParentMutation($t14, 1, $t15);

    // $t95 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t95 := $IsParentMutation($t13, 2, $t14);

    // $t96 := &&($t94, $t95) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t96 := $And($t94, $t95);

    // $t97 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t97 := $IsParentMutation($t12, 0, $t13);

    // $t98 := &&($t96, $t97) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t98 := $And($t96, $t97);

    // if ($t98) goto L31 else goto L32 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t98) { goto L31; } else { goto L32; }

    // label L31 at .\sources\ConditionalBorrowChain.move:100:9+25
L31:

    // write_back[Reference($t14).v1 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L32 at .\sources\ConditionalBorrowChain.move:100:9+25
L32:

    // $t99 := is_parent[Reference($t14).v1 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t99 := $IsParentMutation($t14, 1, $t15);

    // $t100 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t100 := $IsParentMutation($t13, 2, $t14);

    // $t101 := &&($t99, $t100) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t101 := $And($t99, $t100);

    // $t102 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t102 := $IsParentMutation($t12, 1, $t13);

    // $t103 := &&($t101, $t102) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t103 := $And($t101, $t102);

    // if ($t103) goto L33 else goto L34 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t103) { goto L33; } else { goto L34; }

    // label L33 at .\sources\ConditionalBorrowChain.move:100:9+25
L33:

    // write_back[Reference($t14).v1 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L34 at .\sources\ConditionalBorrowChain.move:100:9+25
L34:

    // $t104 := is_parent[Reference($t14).v1 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t104 := $IsParentMutation($t14, 1, $t15);

    // $t105 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t105 := $IsParentMutation($t13, 2, $t14);

    // $t106 := &&($t104, $t105) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t106 := $And($t104, $t105);

    // $t107 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t107 := $IsParentMutation($t12, 2, $t13);

    // $t108 := &&($t106, $t107) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t108 := $And($t106, $t107);

    // if ($t108) goto L35 else goto L36 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t108) { goto L35; } else { goto L36; }

    // label L35 at .\sources\ConditionalBorrowChain.move:100:9+25
L35:

    // write_back[Reference($t14).v1 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v1($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L36 at .\sources\ConditionalBorrowChain.move:100:9+25
L36:

    // $t109 := is_parent[Reference($t14).v2 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t109 := $IsParentMutation($t14, 2, $t15);

    // $t110 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t110 := $IsParentMutation($t13, 0, $t14);

    // $t111 := &&($t109, $t110) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t111 := $And($t109, $t110);

    // $t112 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t112 := $IsParentMutation($t12, 0, $t13);

    // $t113 := &&($t111, $t112) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t113 := $And($t111, $t112);

    // if ($t113) goto L37 else goto L38 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t113) { goto L37; } else { goto L38; }

    // label L37 at .\sources\ConditionalBorrowChain.move:100:9+25
L37:

    // write_back[Reference($t14).v2 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L38 at .\sources\ConditionalBorrowChain.move:100:9+25
L38:

    // $t114 := is_parent[Reference($t14).v2 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t114 := $IsParentMutation($t14, 2, $t15);

    // $t115 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t115 := $IsParentMutation($t13, 0, $t14);

    // $t116 := &&($t114, $t115) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t116 := $And($t114, $t115);

    // $t117 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t117 := $IsParentMutation($t12, 1, $t13);

    // $t118 := &&($t116, $t117) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t118 := $And($t116, $t117);

    // if ($t118) goto L39 else goto L40 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t118) { goto L39; } else { goto L40; }

    // label L39 at .\sources\ConditionalBorrowChain.move:100:9+25
L39:

    // write_back[Reference($t14).v2 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L40 at .\sources\ConditionalBorrowChain.move:100:9+25
L40:

    // $t119 := is_parent[Reference($t14).v2 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t119 := $IsParentMutation($t14, 2, $t15);

    // $t120 := is_parent[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t120 := $IsParentMutation($t13, 0, $t14);

    // $t121 := &&($t119, $t120) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t121 := $And($t119, $t120);

    // $t122 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t122 := $IsParentMutation($t12, 2, $t13);

    // $t123 := &&($t121, $t122) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t123 := $And($t121, $t122);

    // if ($t123) goto L41 else goto L42 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t123) { goto L41; } else { goto L42; }

    // label L41 at .\sources\ConditionalBorrowChain.move:100:9+25
L41:

    // write_back[Reference($t14).v2 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v0($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L42 at .\sources\ConditionalBorrowChain.move:100:9+25
L42:

    // $t124 := is_parent[Reference($t14).v2 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t124 := $IsParentMutation($t14, 2, $t15);

    // $t125 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t125 := $IsParentMutation($t13, 1, $t14);

    // $t126 := &&($t124, $t125) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t126 := $And($t124, $t125);

    // $t127 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t127 := $IsParentMutation($t12, 0, $t13);

    // $t128 := &&($t126, $t127) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t128 := $And($t126, $t127);

    // if ($t128) goto L43 else goto L44 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t128) { goto L43; } else { goto L44; }

    // label L43 at .\sources\ConditionalBorrowChain.move:100:9+25
L43:

    // write_back[Reference($t14).v2 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L44 at .\sources\ConditionalBorrowChain.move:100:9+25
L44:

    // $t129 := is_parent[Reference($t14).v2 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t129 := $IsParentMutation($t14, 2, $t15);

    // $t130 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t130 := $IsParentMutation($t13, 1, $t14);

    // $t131 := &&($t129, $t130) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t131 := $And($t129, $t130);

    // $t132 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t132 := $IsParentMutation($t12, 1, $t13);

    // $t133 := &&($t131, $t132) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t133 := $And($t131, $t132);

    // if ($t133) goto L45 else goto L46 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t133) { goto L45; } else { goto L46; }

    // label L45 at .\sources\ConditionalBorrowChain.move:100:9+25
L45:

    // write_back[Reference($t14).v2 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L46 at .\sources\ConditionalBorrowChain.move:100:9+25
L46:

    // $t134 := is_parent[Reference($t14).v2 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t134 := $IsParentMutation($t14, 2, $t15);

    // $t135 := is_parent[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t135 := $IsParentMutation($t13, 1, $t14);

    // $t136 := &&($t134, $t135) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t136 := $And($t134, $t135);

    // $t137 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t137 := $IsParentMutation($t12, 2, $t13);

    // $t138 := &&($t136, $t137) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t138 := $And($t136, $t137);

    // if ($t138) goto L47 else goto L48 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t138) { goto L47; } else { goto L48; }

    // label L47 at .\sources\ConditionalBorrowChain.move:100:9+25
L47:

    // write_back[Reference($t14).v2 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v1($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L48 at .\sources\ConditionalBorrowChain.move:100:9+25
L48:

    // $t139 := is_parent[Reference($t14).v2 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t139 := $IsParentMutation($t14, 2, $t15);

    // $t140 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t140 := $IsParentMutation($t13, 2, $t14);

    // $t141 := &&($t139, $t140) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t141 := $And($t139, $t140);

    // $t142 := is_parent[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t142 := $IsParentMutation($t12, 0, $t13);

    // $t143 := &&($t141, $t142) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t143 := $And($t141, $t142);

    // if ($t143) goto L49 else goto L50 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t143) { goto L49; } else { goto L50; }

    // label L49 at .\sources\ConditionalBorrowChain.move:100:9+25
L49:

    // write_back[Reference($t14).v2 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v0 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v0($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L50 at .\sources\ConditionalBorrowChain.move:100:9+25
L50:

    // $t144 := is_parent[Reference($t14).v2 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t144 := $IsParentMutation($t14, 2, $t15);

    // $t145 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t145 := $IsParentMutation($t13, 2, $t14);

    // $t146 := &&($t144, $t145) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t146 := $And($t144, $t145);

    // $t147 := is_parent[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t147 := $IsParentMutation($t12, 1, $t13);

    // $t148 := &&($t146, $t147) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t148 := $And($t146, $t147);

    // if ($t148) goto L51 else goto L52 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t148) { goto L51; } else { goto L52; }

    // label L51 at .\sources\ConditionalBorrowChain.move:100:9+25
L51:

    // write_back[Reference($t14).v2 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v1 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v1($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L52 at .\sources\ConditionalBorrowChain.move:100:9+25
L52:

    // $t149 := is_parent[Reference($t14).v2 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t149 := $IsParentMutation($t14, 2, $t15);

    // $t150 := is_parent[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t150 := $IsParentMutation($t13, 2, $t14);

    // $t151 := &&($t149, $t150) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t151 := $And($t149, $t150);

    // $t152 := is_parent[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t152 := $IsParentMutation($t12, 2, $t13);

    // $t153 := &&($t151, $t152) at .\sources\ConditionalBorrowChain.move:100:9+25
    call $t153 := $And($t151, $t152);

    // if ($t153) goto L53 else goto L57 at .\sources\ConditionalBorrowChain.move:100:9+25
    if ($t153) { goto L53; } else { goto L57; }

    // label L53 at .\sources\ConditionalBorrowChain.move:100:9+25
L53:

    // write_back[Reference($t14).v2 (u64)/@]($t15) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$at(3,3100,3125)"} true;
    $t14 := $UpdateMutation($t14, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node1'_v2($Dereference($t14), $Dereference($t15)));

    // write_back[Reference($t13).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node1)/@]($t14) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t13 := $UpdateMutation($t13, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node2'_v2($Dereference($t13), $Dereference($t14)));

    // write_back[Reference($t12).v2 (0xbc::ProphecyBenchmark3Levels3Fields::Node2)/@]($t13) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t12 := $UpdateMutation($t12, $Update'$bc_ProphecyBenchmark3Levels3Fields_Node3'_v2($Dereference($t12), $Dereference($t13)));

    // write_back[LocalRoot($t3)@]($t12) at .\sources\ConditionalBorrowChain.move:100:9+25
    $t3 := $Dereference($t12);

    // trace_local[root]($t3) at .\sources\ConditionalBorrowChain.move:100:9+25
    assume {:print "$track_local(2,0,3):", $t3} $t3 == $t3;

    // label L54 at .\sources\ConditionalBorrowChain.move:100:9+25
L54:

    // $t154 := move($t3) at .\sources\ConditionalBorrowChain.move:102:9+4
    assume {:print "$at(3,3136,3140)"} true;
    $t154 := $t3;

    // trace_return[0]($t154) at .\sources\ConditionalBorrowChain.move:87:14+418
    assume {:print "$at(3,2728,3146)"} true;
    assume {:print "$track_return(2,0,0):", $t154} $t154 == $t154;

    // label L55 at .\sources\ConditionalBorrowChain.move:103:5+1
    assume {:print "$at(3,3145,3146)"} true;
L55:

    // assert Implies(And(And(Eq<u64>($t0, 0), Eq<u64>($t1, 0)), Eq<u64>($t2, 0)), Eq<u64>(select ProphecyBenchmark3Levels3Fields::Node1.v0<0xbc::ProphecyBenchmark3Levels3Fields::Node1>(select ProphecyBenchmark3Levels3Fields::Node2.v0<0xbc::ProphecyBenchmark3Levels3Fields::Node2>(select ProphecyBenchmark3Levels3Fields::Node3.v0<0xbc::ProphecyBenchmark3Levels3Fields::Node3>($t154))), 1)) at .\sources\ConditionalBorrowChain.move:119:9+72
    assume {:print "$at(3,3481,3553)"} true;
    assert {:msg "assert_failed(3,3481,3553): post-condition does not hold"}
      ((($IsEqual'u64'($t0, 0) && $IsEqual'u64'($t1, 0)) && $IsEqual'u64'($t2, 0)) ==> $IsEqual'u64'($t154->$v0->$v0->$v0, 1));

    // assert Le(select ProphecyBenchmark3Levels3Fields::Node1.v0<0xbc::ProphecyBenchmark3Levels3Fields::Node1>(select ProphecyBenchmark3Levels3Fields::Node2.v0<0xbc::ProphecyBenchmark3Levels3Fields::Node2>(select ProphecyBenchmark3Levels3Fields::Node3.v0<0xbc::ProphecyBenchmark3Levels3Fields::Node3>($t154))), 1) at .\sources\ConditionalBorrowChain.move:127:9+29
    assume {:print "$at(3,3753,3782)"} true;
    assert {:msg "assert_failed(3,3753,3782): post-condition does not hold"}
      ($t154->$v0->$v0->$v0 <= 1);

    // return $t154 at .\sources\ConditionalBorrowChain.move:127:9+29
    $ret0 := $t154;
    return;

    // label L56 at .\sources\ConditionalBorrowChain.move:103:5+1
    assume {:print "$at(3,3145,3146)"} true;
L56:

    // abort($t5) at .\sources\ConditionalBorrowChain.move:103:5+1
    assume {:print "$at(3,3145,3146)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

    // label L57 at <internal>:1:1+10
    assume {:print "$at(1,0,10)"} true;
L57:

    // drop($t12) at <internal>:1:1+10
    assume {:print "$at(1,0,10)"} true;

    // drop($t13) at <internal>:1:1+10

    // drop($t14) at <internal>:1:1+10

    // drop($t15) at <internal>:1:1+10

    // goto L54 at <internal>:1:1+10
    goto L54;

}

// fun ProphecyBenchmark3Levels3Fields::new_node1 [baseline] at .\sources\ConditionalBorrowChain.move:29:5+110
procedure {:inline 1} $bc_ProphecyBenchmark3Levels3Fields_new_node1() returns ($ret0: $bc_ProphecyBenchmark3Levels3Fields_Node1)
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
    var $t8: $bc_ProphecyBenchmark3Levels3Fields_Node1;
    var $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1': $bc_ProphecyBenchmark3Levels3Fields_Node1;

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

    // $t8 := pack 0xbc::ProphecyBenchmark3Levels3Fields::Node1($t0, $t1, $t2, $t3, $t4, $t5, $t6, $t7) at .\sources\ConditionalBorrowChain.move:30:9+64
    $t8 := $bc_ProphecyBenchmark3Levels3Fields_Node1($t0, $t1, $t2, $t3, $t4, $t5, $t6, $t7);

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

// fun ProphecyBenchmark3Levels3Fields::new_node1 [verification] at .\sources\ConditionalBorrowChain.move:29:5+110
procedure {:timeLimit 40} $bc_ProphecyBenchmark3Levels3Fields_new_node1$verify() returns ($ret0: $bc_ProphecyBenchmark3Levels3Fields_Node1)
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
    var $t8: $bc_ProphecyBenchmark3Levels3Fields_Node1;
    var $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1': $bc_ProphecyBenchmark3Levels3Fields_Node1;

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

    // $t8 := pack 0xbc::ProphecyBenchmark3Levels3Fields::Node1($t0, $t1, $t2, $t3, $t4, $t5, $t6, $t7) at .\sources\ConditionalBorrowChain.move:30:9+64
    $t8 := $bc_ProphecyBenchmark3Levels3Fields_Node1($t0, $t1, $t2, $t3, $t4, $t5, $t6, $t7);

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

// fun ProphecyBenchmark3Levels3Fields::new_node2 [baseline] at .\sources\ConditionalBorrowChain.move:33:5+225
procedure {:inline 1} $bc_ProphecyBenchmark3Levels3Fields_new_node2() returns ($ret0: $bc_ProphecyBenchmark3Levels3Fields_Node2)
{
    // declare local variables
    var $t0: $bc_ProphecyBenchmark3Levels3Fields_Node1;
    var $t1: int;
    var $t2: $bc_ProphecyBenchmark3Levels3Fields_Node1;
    var $t3: $bc_ProphecyBenchmark3Levels3Fields_Node1;
    var $t4: $bc_ProphecyBenchmark3Levels3Fields_Node1;
    var $t5: $bc_ProphecyBenchmark3Levels3Fields_Node1;
    var $t6: $bc_ProphecyBenchmark3Levels3Fields_Node1;
    var $t7: $bc_ProphecyBenchmark3Levels3Fields_Node1;
    var $t8: $bc_ProphecyBenchmark3Levels3Fields_Node1;
    var $t9: $bc_ProphecyBenchmark3Levels3Fields_Node2;
    var $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2': $bc_ProphecyBenchmark3Levels3Fields_Node2;

    // bytecode translation starts here
    // $t0 := ProphecyBenchmark3Levels3Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:35:17+11
    assume {:print "$at(3,1060,1071)"} true;
    call $t0 := $bc_ProphecyBenchmark3Levels3Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1060,1071)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t2 := ProphecyBenchmark3Levels3Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:35:34+11
    call $t2 := $bc_ProphecyBenchmark3Levels3Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1077,1088)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t3 := ProphecyBenchmark3Levels3Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:35:51+11
    call $t3 := $bc_ProphecyBenchmark3Levels3Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1094,1105)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t4 := ProphecyBenchmark3Levels3Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:35:68+11
    call $t4 := $bc_ProphecyBenchmark3Levels3Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1111,1122)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t5 := ProphecyBenchmark3Levels3Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:36:17+11
    assume {:print "$at(3,1141,1152)"} true;
    call $t5 := $bc_ProphecyBenchmark3Levels3Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1141,1152)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t6 := ProphecyBenchmark3Levels3Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:36:34+11
    call $t6 := $bc_ProphecyBenchmark3Levels3Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1158,1169)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t7 := ProphecyBenchmark3Levels3Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:36:51+11
    call $t7 := $bc_ProphecyBenchmark3Levels3Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1175,1186)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t8 := ProphecyBenchmark3Levels3Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:36:68+11
    call $t8 := $bc_ProphecyBenchmark3Levels3Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1192,1203)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t9 := pack 0xbc::ProphecyBenchmark3Levels3Fields::Node2($t0, $t2, $t3, $t4, $t5, $t6, $t7, $t8) at .\sources\ConditionalBorrowChain.move:34:9+179
    assume {:print "$at(3,1035,1214)"} true;
    $t9 := $bc_ProphecyBenchmark3Levels3Fields_Node2($t0, $t2, $t3, $t4, $t5, $t6, $t7, $t8);

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

// fun ProphecyBenchmark3Levels3Fields::new_node2 [verification] at .\sources\ConditionalBorrowChain.move:33:5+225
procedure {:timeLimit 40} $bc_ProphecyBenchmark3Levels3Fields_new_node2$verify() returns ($ret0: $bc_ProphecyBenchmark3Levels3Fields_Node2)
{
    // declare local variables
    var $t0: $bc_ProphecyBenchmark3Levels3Fields_Node1;
    var $t1: int;
    var $t2: $bc_ProphecyBenchmark3Levels3Fields_Node1;
    var $t3: $bc_ProphecyBenchmark3Levels3Fields_Node1;
    var $t4: $bc_ProphecyBenchmark3Levels3Fields_Node1;
    var $t5: $bc_ProphecyBenchmark3Levels3Fields_Node1;
    var $t6: $bc_ProphecyBenchmark3Levels3Fields_Node1;
    var $t7: $bc_ProphecyBenchmark3Levels3Fields_Node1;
    var $t8: $bc_ProphecyBenchmark3Levels3Fields_Node1;
    var $t9: $bc_ProphecyBenchmark3Levels3Fields_Node2;
    var $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2': $bc_ProphecyBenchmark3Levels3Fields_Node2;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t0 := ProphecyBenchmark3Levels3Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:35:17+11
    assume {:print "$at(3,1060,1071)"} true;
    call $t0 := $bc_ProphecyBenchmark3Levels3Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1060,1071)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t2 := ProphecyBenchmark3Levels3Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:35:34+11
    call $t2 := $bc_ProphecyBenchmark3Levels3Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1077,1088)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t3 := ProphecyBenchmark3Levels3Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:35:51+11
    call $t3 := $bc_ProphecyBenchmark3Levels3Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1094,1105)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t4 := ProphecyBenchmark3Levels3Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:35:68+11
    call $t4 := $bc_ProphecyBenchmark3Levels3Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1111,1122)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t5 := ProphecyBenchmark3Levels3Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:36:17+11
    assume {:print "$at(3,1141,1152)"} true;
    call $t5 := $bc_ProphecyBenchmark3Levels3Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1141,1152)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t6 := ProphecyBenchmark3Levels3Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:36:34+11
    call $t6 := $bc_ProphecyBenchmark3Levels3Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1158,1169)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t7 := ProphecyBenchmark3Levels3Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:36:51+11
    call $t7 := $bc_ProphecyBenchmark3Levels3Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1175,1186)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t8 := ProphecyBenchmark3Levels3Fields::new_node1() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:36:68+11
    call $t8 := $bc_ProphecyBenchmark3Levels3Fields_new_node1();
    if ($abort_flag) {
        assume {:print "$at(3,1192,1203)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t9 := pack 0xbc::ProphecyBenchmark3Levels3Fields::Node2($t0, $t2, $t3, $t4, $t5, $t6, $t7, $t8) at .\sources\ConditionalBorrowChain.move:34:9+179
    assume {:print "$at(3,1035,1214)"} true;
    $t9 := $bc_ProphecyBenchmark3Levels3Fields_Node2($t0, $t2, $t3, $t4, $t5, $t6, $t7, $t8);

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

// fun ProphecyBenchmark3Levels3Fields::new_node3 [baseline] at .\sources\ConditionalBorrowChain.move:40:5+225
procedure {:inline 1} $bc_ProphecyBenchmark3Levels3Fields_new_node3() returns ($ret0: $bc_ProphecyBenchmark3Levels3Fields_Node3)
{
    // declare local variables
    var $t0: $bc_ProphecyBenchmark3Levels3Fields_Node2;
    var $t1: int;
    var $t2: $bc_ProphecyBenchmark3Levels3Fields_Node2;
    var $t3: $bc_ProphecyBenchmark3Levels3Fields_Node2;
    var $t4: $bc_ProphecyBenchmark3Levels3Fields_Node2;
    var $t5: $bc_ProphecyBenchmark3Levels3Fields_Node2;
    var $t6: $bc_ProphecyBenchmark3Levels3Fields_Node2;
    var $t7: $bc_ProphecyBenchmark3Levels3Fields_Node2;
    var $t8: $bc_ProphecyBenchmark3Levels3Fields_Node2;
    var $t9: $bc_ProphecyBenchmark3Levels3Fields_Node3;
    var $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node3': $bc_ProphecyBenchmark3Levels3Fields_Node3;

    // bytecode translation starts here
    // $t0 := ProphecyBenchmark3Levels3Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:42:17+11
    assume {:print "$at(3,1291,1302)"} true;
    call $t0 := $bc_ProphecyBenchmark3Levels3Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1291,1302)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t2 := ProphecyBenchmark3Levels3Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:42:34+11
    call $t2 := $bc_ProphecyBenchmark3Levels3Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1308,1319)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t3 := ProphecyBenchmark3Levels3Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:42:51+11
    call $t3 := $bc_ProphecyBenchmark3Levels3Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1325,1336)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t4 := ProphecyBenchmark3Levels3Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:42:68+11
    call $t4 := $bc_ProphecyBenchmark3Levels3Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1342,1353)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t5 := ProphecyBenchmark3Levels3Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:43:17+11
    assume {:print "$at(3,1372,1383)"} true;
    call $t5 := $bc_ProphecyBenchmark3Levels3Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1372,1383)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t6 := ProphecyBenchmark3Levels3Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:43:34+11
    call $t6 := $bc_ProphecyBenchmark3Levels3Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1389,1400)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t7 := ProphecyBenchmark3Levels3Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:43:51+11
    call $t7 := $bc_ProphecyBenchmark3Levels3Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1406,1417)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t8 := ProphecyBenchmark3Levels3Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:43:68+11
    call $t8 := $bc_ProphecyBenchmark3Levels3Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1423,1434)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t9 := pack 0xbc::ProphecyBenchmark3Levels3Fields::Node3($t0, $t2, $t3, $t4, $t5, $t6, $t7, $t8) at .\sources\ConditionalBorrowChain.move:41:9+179
    assume {:print "$at(3,1266,1445)"} true;
    $t9 := $bc_ProphecyBenchmark3Levels3Fields_Node3($t0, $t2, $t3, $t4, $t5, $t6, $t7, $t8);

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

// fun ProphecyBenchmark3Levels3Fields::new_node3 [verification] at .\sources\ConditionalBorrowChain.move:40:5+225
procedure {:timeLimit 40} $bc_ProphecyBenchmark3Levels3Fields_new_node3$verify() returns ($ret0: $bc_ProphecyBenchmark3Levels3Fields_Node3)
{
    // declare local variables
    var $t0: $bc_ProphecyBenchmark3Levels3Fields_Node2;
    var $t1: int;
    var $t2: $bc_ProphecyBenchmark3Levels3Fields_Node2;
    var $t3: $bc_ProphecyBenchmark3Levels3Fields_Node2;
    var $t4: $bc_ProphecyBenchmark3Levels3Fields_Node2;
    var $t5: $bc_ProphecyBenchmark3Levels3Fields_Node2;
    var $t6: $bc_ProphecyBenchmark3Levels3Fields_Node2;
    var $t7: $bc_ProphecyBenchmark3Levels3Fields_Node2;
    var $t8: $bc_ProphecyBenchmark3Levels3Fields_Node2;
    var $t9: $bc_ProphecyBenchmark3Levels3Fields_Node3;
    var $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node3': $bc_ProphecyBenchmark3Levels3Fields_Node3;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t0 := ProphecyBenchmark3Levels3Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:42:17+11
    assume {:print "$at(3,1291,1302)"} true;
    call $t0 := $bc_ProphecyBenchmark3Levels3Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1291,1302)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t2 := ProphecyBenchmark3Levels3Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:42:34+11
    call $t2 := $bc_ProphecyBenchmark3Levels3Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1308,1319)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t3 := ProphecyBenchmark3Levels3Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:42:51+11
    call $t3 := $bc_ProphecyBenchmark3Levels3Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1325,1336)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t4 := ProphecyBenchmark3Levels3Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:42:68+11
    call $t4 := $bc_ProphecyBenchmark3Levels3Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1342,1353)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t5 := ProphecyBenchmark3Levels3Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:43:17+11
    assume {:print "$at(3,1372,1383)"} true;
    call $t5 := $bc_ProphecyBenchmark3Levels3Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1372,1383)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t6 := ProphecyBenchmark3Levels3Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:43:34+11
    call $t6 := $bc_ProphecyBenchmark3Levels3Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1389,1400)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t7 := ProphecyBenchmark3Levels3Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:43:51+11
    call $t7 := $bc_ProphecyBenchmark3Levels3Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1406,1417)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t8 := ProphecyBenchmark3Levels3Fields::new_node2() on_abort goto L2 with $t1 at .\sources\ConditionalBorrowChain.move:43:68+11
    call $t8 := $bc_ProphecyBenchmark3Levels3Fields_new_node2();
    if ($abort_flag) {
        assume {:print "$at(3,1423,1434)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(2,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t9 := pack 0xbc::ProphecyBenchmark3Levels3Fields::Node3($t0, $t2, $t3, $t4, $t5, $t6, $t7, $t8) at .\sources\ConditionalBorrowChain.move:41:9+179
    assume {:print "$at(3,1266,1445)"} true;
    $t9 := $bc_ProphecyBenchmark3Levels3Fields_Node3($t0, $t2, $t3, $t4, $t5, $t6, $t7, $t8);

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

// fun ProphecyBenchmark3Levels3Fields::select_leaf [baseline] at .\sources\ConditionalBorrowChain.move:72:5+154
procedure {:inline 1} $bc_ProphecyBenchmark3Levels3Fields_select_leaf(_$t0: $Mutation ($bc_ProphecyBenchmark3Levels3Fields_Node1), _$t1: int) returns ($ret0: $Mutation (int), $ret1: $Mutation ($bc_ProphecyBenchmark3Levels3Fields_Node1))
{
    // declare local variables
    var $t2: $Mutation (int);
    var $t3: int;
    var $t4: bool;
    var $t5: $Mutation (int);
    var $t6: $Mutation (int);
    var $t7: int;
    var $t8: bool;
    var $t9: $Mutation (int);
    var $t10: $Mutation (int);
    var $t0: $Mutation ($bc_ProphecyBenchmark3Levels3Fields_Node1);
    var $t1: int;
    var $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1': $bc_ProphecyBenchmark3Levels3Fields_Node1;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:72:5+1
    assume {:print "$at(3,2257,2258)"} true;
    $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1' := $Dereference($t0);
    assume {:print "$track_local(2,4,0):", $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1';

    // trace_local[idx]($t1) at .\sources\ConditionalBorrowChain.move:72:5+1
    assume {:print "$track_local(2,4,1):", $t1} $t1 == $t1;

    // $t3 := 0 at .\sources\ConditionalBorrowChain.move:73:20+1
    assume {:print "$at(3,2329,2330)"} true;
    $t3 := 0;
    assume $IsValid'u64'($t3);

    // $t4 := ==($t1, $t3) at .\sources\ConditionalBorrowChain.move:73:13+8
    $t4 := $IsEqual'u64'($t1, $t3);

    // if ($t4) goto L1 else goto L0 at .\sources\ConditionalBorrowChain.move:73:9+87
    if ($t4) { goto L1; } else { goto L0; }

    // label L1 at .\sources\ConditionalBorrowChain.move:73:25+9
L1:

    // $t5 := borrow_field<0xbc::ProphecyBenchmark3Levels3Fields::Node1>.v0($t0) at .\sources\ConditionalBorrowChain.move:73:25+9
    assume {:print "$at(3,2334,2343)"} true;
    $t5 := $ChildMutation($t0, 0, $Dereference($t0)->$v0);

    // trace_return[0]($t5) at .\sources\ConditionalBorrowChain.move:73:9+87
    $temp_0'u64' := $Dereference($t5);
    assume {:print "$track_return(2,4,0):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:73:9+87
    $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1' := $Dereference($t0);
    assume {:print "$track_local(2,4,0):", $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:73:9+87
    $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1' := $Dereference($t0);
    assume {:print "$track_local(2,4,0):", $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1';

    // $t6 := move($t5) at .\sources\ConditionalBorrowChain.move:73:9+87
    $t6 := $t5;

    // goto L9 at .\sources\ConditionalBorrowChain.move:73:9+87
    goto L9;

    // label L4 at .\sources\ConditionalBorrowChain.move:73:9+87
L4:

    // trace_return[0]($t2) at .\sources\ConditionalBorrowChain.move:73:9+87
    assume {:print "$at(3,2318,2405)"} true;
    $temp_0'u64' := $Dereference($t2);
    assume {:print "$track_return(2,4,0):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:73:9+87
    $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1' := $Dereference($t0);
    assume {:print "$track_local(2,4,0):", $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1';

    // label L6 at .\sources\ConditionalBorrowChain.move:73:9+87
L6:

    // label L8 at .\sources\ConditionalBorrowChain.move:73:9+87
    assume {:print "$at(3,2318,2405)"} true;
L8:

    // $t6 := move($t2) at .\sources\ConditionalBorrowChain.move:73:9+87
    assume {:print "$at(3,2318,2405)"} true;
    $t6 := $t2;

    // goto L9 at .\sources\ConditionalBorrowChain.move:73:9+87
    goto L9;

    // label L0 at .\sources\ConditionalBorrowChain.move:73:46+3
L0:

    // $t7 := 1 at .\sources\ConditionalBorrowChain.move:73:53+1
    assume {:print "$at(3,2362,2363)"} true;
    $t7 := 1;
    assume $IsValid'u64'($t7);

    // $t8 := ==($t1, $t7) at .\sources\ConditionalBorrowChain.move:73:46+8
    $t8 := $IsEqual'u64'($t1, $t7);

    // if ($t8) goto L3 else goto L2 at .\sources\ConditionalBorrowChain.move:73:42+54
    if ($t8) { goto L3; } else { goto L2; }

    // label L3 at .\sources\ConditionalBorrowChain.move:73:58+9
L3:

    // $t9 := borrow_field<0xbc::ProphecyBenchmark3Levels3Fields::Node1>.v1($t0) at .\sources\ConditionalBorrowChain.move:73:58+9
    assume {:print "$at(3,2367,2376)"} true;
    $t9 := $ChildMutation($t0, 1, $Dereference($t0)->$v1);

    // $t2 := $t9 at .\sources\ConditionalBorrowChain.move:73:58+9
    $t2 := $t9;

    // trace_local[return]($t9) at .\sources\ConditionalBorrowChain.move:73:58+9
    $temp_0'u64' := $Dereference($t9);
    assume {:print "$track_local(2,4,2):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // goto L4 at .\sources\ConditionalBorrowChain.move:73:58+9
    goto L4;

    // label L2 at .\sources\ConditionalBorrowChain.move:74:16+9
    assume {:print "$at(3,2394,2403)"} true;
L2:

    // $t10 := borrow_field<0xbc::ProphecyBenchmark3Levels3Fields::Node1>.v2($t0) at .\sources\ConditionalBorrowChain.move:74:16+9
    assume {:print "$at(3,2394,2403)"} true;
    $t10 := $ChildMutation($t0, 2, $Dereference($t0)->$v2);

    // $t2 := $t10 at .\sources\ConditionalBorrowChain.move:74:16+9
    $t2 := $t10;

    // trace_local[return]($t10) at .\sources\ConditionalBorrowChain.move:74:16+9
    $temp_0'u64' := $Dereference($t10);
    assume {:print "$track_local(2,4,2):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // goto L4 at .\sources\ConditionalBorrowChain.move:74:16+9
    goto L4;

    // label L9 at .\sources\ConditionalBorrowChain.move:75:5+1
    assume {:print "$at(3,2410,2411)"} true;
L9:

    // return $t6 at .\sources\ConditionalBorrowChain.move:75:5+1
    assume {:print "$at(3,2410,2411)"} true;
    $ret0 := $t6;
    $ret1 := $t0;
    return;

}

// fun ProphecyBenchmark3Levels3Fields::select_n1 [baseline] at .\sources\ConditionalBorrowChain.move:62:5+154
procedure {:inline 1} $bc_ProphecyBenchmark3Levels3Fields_select_n1(_$t0: $Mutation ($bc_ProphecyBenchmark3Levels3Fields_Node2), _$t1: int) returns ($ret0: $Mutation ($bc_ProphecyBenchmark3Levels3Fields_Node1), $ret1: $Mutation ($bc_ProphecyBenchmark3Levels3Fields_Node2))
{
    // declare local variables
    var $t2: $Mutation ($bc_ProphecyBenchmark3Levels3Fields_Node1);
    var $t3: int;
    var $t4: bool;
    var $t5: $Mutation ($bc_ProphecyBenchmark3Levels3Fields_Node1);
    var $t6: $Mutation ($bc_ProphecyBenchmark3Levels3Fields_Node1);
    var $t7: int;
    var $t8: bool;
    var $t9: $Mutation ($bc_ProphecyBenchmark3Levels3Fields_Node1);
    var $t10: $Mutation ($bc_ProphecyBenchmark3Levels3Fields_Node1);
    var $t0: $Mutation ($bc_ProphecyBenchmark3Levels3Fields_Node2);
    var $t1: int;
    var $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1': $bc_ProphecyBenchmark3Levels3Fields_Node1;
    var $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2': $bc_ProphecyBenchmark3Levels3Fields_Node2;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:62:5+1
    assume {:print "$at(3,1951,1952)"} true;
    $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2' := $Dereference($t0);
    assume {:print "$track_local(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2';

    // trace_local[idx]($t1) at .\sources\ConditionalBorrowChain.move:62:5+1
    assume {:print "$track_local(2,5,1):", $t1} $t1 == $t1;

    // $t3 := 0 at .\sources\ConditionalBorrowChain.move:63:20+1
    assume {:print "$at(3,2023,2024)"} true;
    $t3 := 0;
    assume $IsValid'u64'($t3);

    // $t4 := ==($t1, $t3) at .\sources\ConditionalBorrowChain.move:63:13+8
    $t4 := $IsEqual'u64'($t1, $t3);

    // if ($t4) goto L1 else goto L0 at .\sources\ConditionalBorrowChain.move:63:9+87
    if ($t4) { goto L1; } else { goto L0; }

    // label L1 at .\sources\ConditionalBorrowChain.move:63:25+9
L1:

    // $t5 := borrow_field<0xbc::ProphecyBenchmark3Levels3Fields::Node2>.v0($t0) at .\sources\ConditionalBorrowChain.move:63:25+9
    assume {:print "$at(3,2028,2037)"} true;
    $t5 := $ChildMutation($t0, 0, $Dereference($t0)->$v0);

    // trace_return[0]($t5) at .\sources\ConditionalBorrowChain.move:63:9+87
    $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1' := $Dereference($t5);
    assume {:print "$track_return(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:63:9+87
    $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2' := $Dereference($t0);
    assume {:print "$track_local(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:63:9+87
    $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2' := $Dereference($t0);
    assume {:print "$track_local(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2';

    // $t6 := move($t5) at .\sources\ConditionalBorrowChain.move:63:9+87
    $t6 := $t5;

    // goto L9 at .\sources\ConditionalBorrowChain.move:63:9+87
    goto L9;

    // label L4 at .\sources\ConditionalBorrowChain.move:63:9+87
L4:

    // trace_return[0]($t2) at .\sources\ConditionalBorrowChain.move:63:9+87
    assume {:print "$at(3,2012,2099)"} true;
    $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1' := $Dereference($t2);
    assume {:print "$track_return(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:63:9+87
    $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2' := $Dereference($t0);
    assume {:print "$track_local(2,5,0):", $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2';

    // label L6 at .\sources\ConditionalBorrowChain.move:63:9+87
L6:

    // label L8 at .\sources\ConditionalBorrowChain.move:63:9+87
    assume {:print "$at(3,2012,2099)"} true;
L8:

    // $t6 := move($t2) at .\sources\ConditionalBorrowChain.move:63:9+87
    assume {:print "$at(3,2012,2099)"} true;
    $t6 := $t2;

    // goto L9 at .\sources\ConditionalBorrowChain.move:63:9+87
    goto L9;

    // label L0 at .\sources\ConditionalBorrowChain.move:63:46+3
L0:

    // $t7 := 1 at .\sources\ConditionalBorrowChain.move:63:53+1
    assume {:print "$at(3,2056,2057)"} true;
    $t7 := 1;
    assume $IsValid'u64'($t7);

    // $t8 := ==($t1, $t7) at .\sources\ConditionalBorrowChain.move:63:46+8
    $t8 := $IsEqual'u64'($t1, $t7);

    // if ($t8) goto L3 else goto L2 at .\sources\ConditionalBorrowChain.move:63:42+54
    if ($t8) { goto L3; } else { goto L2; }

    // label L3 at .\sources\ConditionalBorrowChain.move:63:58+9
L3:

    // $t9 := borrow_field<0xbc::ProphecyBenchmark3Levels3Fields::Node2>.v1($t0) at .\sources\ConditionalBorrowChain.move:63:58+9
    assume {:print "$at(3,2061,2070)"} true;
    $t9 := $ChildMutation($t0, 1, $Dereference($t0)->$v1);

    // $t2 := $t9 at .\sources\ConditionalBorrowChain.move:63:58+9
    $t2 := $t9;

    // trace_local[return]($t9) at .\sources\ConditionalBorrowChain.move:63:58+9
    $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1' := $Dereference($t9);
    assume {:print "$track_local(2,5,2):", $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1';

    // goto L4 at .\sources\ConditionalBorrowChain.move:63:58+9
    goto L4;

    // label L2 at .\sources\ConditionalBorrowChain.move:64:16+9
    assume {:print "$at(3,2088,2097)"} true;
L2:

    // $t10 := borrow_field<0xbc::ProphecyBenchmark3Levels3Fields::Node2>.v2($t0) at .\sources\ConditionalBorrowChain.move:64:16+9
    assume {:print "$at(3,2088,2097)"} true;
    $t10 := $ChildMutation($t0, 2, $Dereference($t0)->$v2);

    // $t2 := $t10 at .\sources\ConditionalBorrowChain.move:64:16+9
    $t2 := $t10;

    // trace_local[return]($t10) at .\sources\ConditionalBorrowChain.move:64:16+9
    $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1' := $Dereference($t10);
    assume {:print "$track_local(2,5,2):", $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1'} $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1' == $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node1';

    // goto L4 at .\sources\ConditionalBorrowChain.move:64:16+9
    goto L4;

    // label L9 at .\sources\ConditionalBorrowChain.move:65:5+1
    assume {:print "$at(3,2104,2105)"} true;
L9:

    // return $t6 at .\sources\ConditionalBorrowChain.move:65:5+1
    assume {:print "$at(3,2104,2105)"} true;
    $ret0 := $t6;
    $ret1 := $t0;
    return;

}

// fun ProphecyBenchmark3Levels3Fields::select_n2 [baseline] at .\sources\ConditionalBorrowChain.move:52:5+154
procedure {:inline 1} $bc_ProphecyBenchmark3Levels3Fields_select_n2(_$t0: $Mutation ($bc_ProphecyBenchmark3Levels3Fields_Node3), _$t1: int) returns ($ret0: $Mutation ($bc_ProphecyBenchmark3Levels3Fields_Node2), $ret1: $Mutation ($bc_ProphecyBenchmark3Levels3Fields_Node3))
{
    // declare local variables
    var $t2: $Mutation ($bc_ProphecyBenchmark3Levels3Fields_Node2);
    var $t3: int;
    var $t4: bool;
    var $t5: $Mutation ($bc_ProphecyBenchmark3Levels3Fields_Node2);
    var $t6: $Mutation ($bc_ProphecyBenchmark3Levels3Fields_Node2);
    var $t7: int;
    var $t8: bool;
    var $t9: $Mutation ($bc_ProphecyBenchmark3Levels3Fields_Node2);
    var $t10: $Mutation ($bc_ProphecyBenchmark3Levels3Fields_Node2);
    var $t0: $Mutation ($bc_ProphecyBenchmark3Levels3Fields_Node3);
    var $t1: int;
    var $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2': $bc_ProphecyBenchmark3Levels3Fields_Node2;
    var $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node3': $bc_ProphecyBenchmark3Levels3Fields_Node3;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:52:5+1
    assume {:print "$at(3,1652,1653)"} true;
    $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node3' := $Dereference($t0);
    assume {:print "$track_local(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node3'} $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node3' == $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node3';

    // trace_local[idx]($t1) at .\sources\ConditionalBorrowChain.move:52:5+1
    assume {:print "$track_local(2,6,1):", $t1} $t1 == $t1;

    // $t3 := 0 at .\sources\ConditionalBorrowChain.move:53:20+1
    assume {:print "$at(3,1724,1725)"} true;
    $t3 := 0;
    assume $IsValid'u64'($t3);

    // $t4 := ==($t1, $t3) at .\sources\ConditionalBorrowChain.move:53:13+8
    $t4 := $IsEqual'u64'($t1, $t3);

    // if ($t4) goto L1 else goto L0 at .\sources\ConditionalBorrowChain.move:53:9+87
    if ($t4) { goto L1; } else { goto L0; }

    // label L1 at .\sources\ConditionalBorrowChain.move:53:25+9
L1:

    // $t5 := borrow_field<0xbc::ProphecyBenchmark3Levels3Fields::Node3>.v0($t0) at .\sources\ConditionalBorrowChain.move:53:25+9
    assume {:print "$at(3,1729,1738)"} true;
    $t5 := $ChildMutation($t0, 0, $Dereference($t0)->$v0);

    // trace_return[0]($t5) at .\sources\ConditionalBorrowChain.move:53:9+87
    $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2' := $Dereference($t5);
    assume {:print "$track_return(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:53:9+87
    $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node3' := $Dereference($t0);
    assume {:print "$track_local(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node3'} $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node3' == $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node3';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:53:9+87
    $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node3' := $Dereference($t0);
    assume {:print "$track_local(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node3'} $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node3' == $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node3';

    // $t6 := move($t5) at .\sources\ConditionalBorrowChain.move:53:9+87
    $t6 := $t5;

    // goto L9 at .\sources\ConditionalBorrowChain.move:53:9+87
    goto L9;

    // label L4 at .\sources\ConditionalBorrowChain.move:53:9+87
L4:

    // trace_return[0]($t2) at .\sources\ConditionalBorrowChain.move:53:9+87
    assume {:print "$at(3,1713,1800)"} true;
    $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2' := $Dereference($t2);
    assume {:print "$track_return(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2';

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:53:9+87
    $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node3' := $Dereference($t0);
    assume {:print "$track_local(2,6,0):", $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node3'} $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node3' == $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node3';

    // label L6 at .\sources\ConditionalBorrowChain.move:53:9+87
L6:

    // label L8 at .\sources\ConditionalBorrowChain.move:53:9+87
    assume {:print "$at(3,1713,1800)"} true;
L8:

    // $t6 := move($t2) at .\sources\ConditionalBorrowChain.move:53:9+87
    assume {:print "$at(3,1713,1800)"} true;
    $t6 := $t2;

    // goto L9 at .\sources\ConditionalBorrowChain.move:53:9+87
    goto L9;

    // label L0 at .\sources\ConditionalBorrowChain.move:53:46+3
L0:

    // $t7 := 1 at .\sources\ConditionalBorrowChain.move:53:53+1
    assume {:print "$at(3,1757,1758)"} true;
    $t7 := 1;
    assume $IsValid'u64'($t7);

    // $t8 := ==($t1, $t7) at .\sources\ConditionalBorrowChain.move:53:46+8
    $t8 := $IsEqual'u64'($t1, $t7);

    // if ($t8) goto L3 else goto L2 at .\sources\ConditionalBorrowChain.move:53:42+54
    if ($t8) { goto L3; } else { goto L2; }

    // label L3 at .\sources\ConditionalBorrowChain.move:53:58+9
L3:

    // $t9 := borrow_field<0xbc::ProphecyBenchmark3Levels3Fields::Node3>.v1($t0) at .\sources\ConditionalBorrowChain.move:53:58+9
    assume {:print "$at(3,1762,1771)"} true;
    $t9 := $ChildMutation($t0, 1, $Dereference($t0)->$v1);

    // $t2 := $t9 at .\sources\ConditionalBorrowChain.move:53:58+9
    $t2 := $t9;

    // trace_local[return]($t9) at .\sources\ConditionalBorrowChain.move:53:58+9
    $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2' := $Dereference($t9);
    assume {:print "$track_local(2,6,2):", $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2';

    // goto L4 at .\sources\ConditionalBorrowChain.move:53:58+9
    goto L4;

    // label L2 at .\sources\ConditionalBorrowChain.move:54:16+9
    assume {:print "$at(3,1789,1798)"} true;
L2:

    // $t10 := borrow_field<0xbc::ProphecyBenchmark3Levels3Fields::Node3>.v2($t0) at .\sources\ConditionalBorrowChain.move:54:16+9
    assume {:print "$at(3,1789,1798)"} true;
    $t10 := $ChildMutation($t0, 2, $Dereference($t0)->$v2);

    // $t2 := $t10 at .\sources\ConditionalBorrowChain.move:54:16+9
    $t2 := $t10;

    // trace_local[return]($t10) at .\sources\ConditionalBorrowChain.move:54:16+9
    $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2' := $Dereference($t10);
    assume {:print "$track_local(2,6,2):", $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2'} $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2' == $temp_0'$bc_ProphecyBenchmark3Levels3Fields_Node2';

    // goto L4 at .\sources\ConditionalBorrowChain.move:54:16+9
    goto L4;

    // label L9 at .\sources\ConditionalBorrowChain.move:55:5+1
    assume {:print "$at(3,1805,1806)"} true;
L9:

    // return $t6 at .\sources\ConditionalBorrowChain.move:55:5+1
    assume {:print "$at(3,1805,1806)"} true;
    $ret0 := $t6;
    $ret1 := $t0;
    return;

}
