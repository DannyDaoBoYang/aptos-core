
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


function $Arbitrary_value_of'#0'(): #0;



function $Arbitrary_value_of'$bc_BasicCoin_Balance'#0''(): $bc_BasicCoin_Balance'#0';



function $Arbitrary_value_of'$bc_BasicCoin_Coin'#0''(): $bc_BasicCoin_Coin'#0';



function $Arbitrary_value_of'$bc_ProphecyBenchmark_Node'(): $bc_ProphecyBenchmark_Node;



function $Arbitrary_value_of'signer'(): $signer;



function $Arbitrary_value_of'bool'(): bool;



function $Arbitrary_value_of'address'(): int;



function $Arbitrary_value_of'u256'(): int;



function $Arbitrary_value_of'u64'(): int;



function $Arbitrary_value_of'u8'(): int;



function $Arbitrary_value_of'bv256'(): bv256;



function $Arbitrary_value_of'bv64'(): bv64;



function $Arbitrary_value_of'bv8'(): bv8;




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


function $castBv8to8(src: bv8) returns (bv8)
{
    src
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


function $castBv64to8(src: bv64) returns (bv8)
{
    if ($Gt'Bv64'(src, 255bv64)) then
        $Arbitrary_value_of'bv8'()
    else
    src[8:0]
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


function $castBv256to8(src: bv256) returns (bv8)
{
    if ($Gt'Bv256'(src, 255bv256)) then
        $Arbitrary_value_of'bv8'()
    else
    src[8:0]
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


function $castBv8to64(src: bv8) returns (bv64)
{
    0bv56 ++ src
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


function $castBv8to256(src: bv8) returns (bv256)
{
    0bv248 ++ src
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

function $TypeName(t: $TypeParamInfo): Vec int;
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamBool ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 98][1 := 111][2 := 111][3 := 108], 4)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 98][1 := 111][2 := 111][3 := 108], 4)) ==> t is $TypeParamBool);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU8 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 56], 2)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 56], 2)) ==> t is $TypeParamU8);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU16 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 54], 3)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 54], 3)) ==> t is $TypeParamU16);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU32 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 51][2 := 50], 3)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 51][2 := 50], 3)) ==> t is $TypeParamU32);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU64 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 54][2 := 52], 3)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 54][2 := 52], 3)) ==> t is $TypeParamU64);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU128 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 50][3 := 56], 4)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 50][3 := 56], 4)) ==> t is $TypeParamU128);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamU256 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 50][2 := 53][3 := 54], 4)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 50][2 := 53][3 := 54], 4)) ==> t is $TypeParamU256);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamI8 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 105][1 := 56], 2)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 105][1 := 56], 2)) ==> t is $TypeParamI8);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamI16 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 105][1 := 49][2 := 54], 3)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 105][1 := 49][2 := 54], 3)) ==> t is $TypeParamI16);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamI32 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 105][1 := 51][2 := 50], 3)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 105][1 := 51][2 := 50], 3)) ==> t is $TypeParamI32);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamI64 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 105][1 := 54][2 := 52], 3)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 105][1 := 54][2 := 52], 3)) ==> t is $TypeParamI64);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamI128 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 105][1 := 49][2 := 50][3 := 56], 4)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 105][1 := 49][2 := 50][3 := 56], 4)) ==> t is $TypeParamI128);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamI256 ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 105][1 := 50][2 := 53][3 := 54], 4)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 105][1 := 50][2 := 53][3 := 54], 4)) ==> t is $TypeParamI256);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamAddress ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 97][1 := 100][2 := 100][3 := 114][4 := 101][5 := 115][6 := 115], 7)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 97][1 := 100][2 := 100][3 := 114][4 := 101][5 := 115][6 := 115], 7)) ==> t is $TypeParamAddress);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamSigner ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 115][1 := 105][2 := 103][3 := 110][4 := 101][5 := 114], 6)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 115][1 := 105][2 := 103][3 := 110][4 := 101][5 := 114], 6)) ==> t is $TypeParamSigner);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamVector ==> $IsEqual'vec'u8''($TypeName(t), ConcatVec(ConcatVec(Vec(DefaultVecMap()[0 := 118][1 := 101][2 := 99][3 := 116][4 := 111][5 := 114][6 := 60], 7), $TypeName(t->e)), Vec(DefaultVecMap()[0 := 62], 1))));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} ($IsPrefix'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 118][1 := 101][2 := 99][3 := 116][4 := 111][5 := 114][6 := 60], 7)) && $IsSuffix'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 62], 1))) ==> t is $TypeParamVector);
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} t is $TypeParamStruct ==> $IsEqual'vec'u8''($TypeName(t), ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(Vec(DefaultVecMap()[0 := 48][1 := 120], 2), MakeVec1(t->a)), Vec(DefaultVecMap()[0 := 58][1 := 58], 2)), t->m), Vec(DefaultVecMap()[0 := 58][1 := 58], 2)), t->s)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsPrefix'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 48][1 := 120], 2)) ==> t is $TypeParamVector);


// Given Types for Type Parameters

type #0;
function {:inline} $IsEqual'#0'(x1: #0, x2: #0): bool { x1 == x2 }
function {:inline} $IsValid'#0'(x: #0): bool { true }
var #0_info: $TypeParamInfo;
var #0_$memory: $Memory #0;

// fun error::already_exists [baseline] at .\../../../move-stdlib/sources\error.move:76:3+71
procedure {:inline 1} $1_error_already_exists(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t0: int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[r]($t0) at .\../../../move-stdlib/sources\error.move:76:3+1
    assume {:print "$at(7,3376,3377)"} true;
    assume {:print "$track_local(1,1,0):", $t0} $t0 == $t0;

    // $t1 := 8 at .\../../../move-stdlib/sources\error.move:76:54+14
    $t1 := 8;
    assume $IsValid'u64'($t1);

    // $t2 := error::canonical($t1, $t0) on_abort goto L2 with $t3 at .\../../../move-stdlib/sources\error.move:76:44+28
    call $t2 := $1_error_canonical($t1, $t0);
    if ($abort_flag) {
        assume {:print "$at(7,3417,3445)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(1,1):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_return[0]($t2) at .\../../../move-stdlib/sources\error.move:76:44+28
    assume {:print "$track_return(1,1,0):", $t2} $t2 == $t2;

    // label L1 at .\../../../move-stdlib/sources\error.move:76:73+1
L1:

    // return $t2 at .\../../../move-stdlib/sources\error.move:76:73+1
    assume {:print "$at(7,3446,3447)"} true;
    $ret0 := $t2;
    return;

    // label L2 at .\../../../move-stdlib/sources\error.move:76:73+1
L2:

    // abort($t3) at .\../../../move-stdlib/sources\error.move:76:73+1
    assume {:print "$at(7,3446,3447)"} true;
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun error::canonical [baseline] at .\../../../move-stdlib/sources\error.move:64:3+89
procedure {:inline 1} $1_error_canonical(_$t0: int, _$t1: int) returns ($ret0: int)
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t0: int;
    var $t1: int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[category]($t0) at .\../../../move-stdlib/sources\error.move:64:3+1
    assume {:print "$at(7,2705,2706)"} true;
    assume {:print "$track_local(1,2,0):", $t0} $t0 == $t0;

    // trace_local[reason]($t1) at .\../../../move-stdlib/sources\error.move:64:3+1
    assume {:print "$track_local(1,2,1):", $t1} $t1 == $t1;

    // $t2 := 16 at .\../../../move-stdlib/sources\error.move:65:18+2
    assume {:print "$at(7,2778,2780)"} true;
    $t2 := 16;
    assume $IsValid'u8'($t2);

    // $t3 := <<($t0, $t2) on_abort goto L2 with $t4 at .\../../../move-stdlib/sources\error.move:65:5+16
    call $t3 := $ShlU64($t0, $t2);
    if ($abort_flag) {
        assume {:print "$at(7,2765,2781)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(1,2):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t5 := +($t3, $t1) on_abort goto L2 with $t4 at .\../../../move-stdlib/sources\error.move:65:5+25
    call $t5 := $AddU64($t3, $t1);
    if ($abort_flag) {
        assume {:print "$at(7,2765,2790)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(1,2):", $t4} $t4 == $t4;
        goto L2;
    }

    // trace_return[0]($t5) at .\../../../move-stdlib/sources\error.move:65:5+25
    assume {:print "$track_return(1,2,0):", $t5} $t5 == $t5;

    // label L1 at .\../../../move-stdlib/sources\error.move:66:3+1
    assume {:print "$at(7,2793,2794)"} true;
L1:

    // return $t5 at .\../../../move-stdlib/sources\error.move:66:3+1
    assume {:print "$at(7,2793,2794)"} true;
    $ret0 := $t5;
    return;

    // label L2 at .\../../../move-stdlib/sources\error.move:66:3+1
L2:

    // abort($t4) at .\../../../move-stdlib/sources\error.move:66:3+1
    assume {:print "$at(7,2793,2794)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// spec fun at .\../../../move-stdlib/sources\signer.move:26:5+77
function {:inline} $1_signer_$address_of(s: $signer): int {
    $1_signer_$borrow_address(s)
}

// fun signer::address_of [baseline] at .\../../../move-stdlib/sources\signer.move:26:5+77
procedure {:inline 1} $1_signer_address_of(_$t0: $signer) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t0: $signer;
    var $temp_0'address': int;
    var $temp_0'signer': $signer;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[s]($t0) at .\../../../move-stdlib/sources\signer.move:26:5+1
    assume {:print "$at(11,794,795)"} true;
    assume {:print "$track_local(2,0,0):", $t0} $t0 == $t0;

    // $t1 := signer::borrow_address($t0) on_abort goto L2 with $t2 at .\../../../move-stdlib/sources\signer.move:27:10+17
    assume {:print "$at(11,848,865)"} true;
    call $t1 := $1_signer_borrow_address($t0);
    if ($abort_flag) {
        assume {:print "$at(11,848,865)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(2,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_return[0]($t1) at .\../../../move-stdlib/sources\signer.move:27:9+18
    assume {:print "$track_return(2,0,0):", $t1} $t1 == $t1;

    // label L1 at .\../../../move-stdlib/sources\signer.move:28:5+1
    assume {:print "$at(11,870,871)"} true;
L1:

    // return $t1 at .\../../../move-stdlib/sources\signer.move:28:5+1
    assume {:print "$at(11,870,871)"} true;
    $ret0 := $t1;
    return;

    // label L2 at .\../../../move-stdlib/sources\signer.move:28:5+1
L2:

    // abort($t2) at .\../../../move-stdlib/sources\signer.move:28:5+1
    assume {:print "$at(11,870,871)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// struct BasicCoin::Balance<#0> at .\sources\BasicCoin.move:17:5+77
datatype $bc_BasicCoin_Balance'#0' {
    $bc_BasicCoin_Balance'#0'($coin: $bc_BasicCoin_Coin'#0')
}
function {:inline} $Update'$bc_BasicCoin_Balance'#0''_coin(s: $bc_BasicCoin_Balance'#0', x: $bc_BasicCoin_Coin'#0'): $bc_BasicCoin_Balance'#0' {
    $bc_BasicCoin_Balance'#0'(x)
}
function $IsValid'$bc_BasicCoin_Balance'#0''(s: $bc_BasicCoin_Balance'#0'): bool {
    $IsValid'$bc_BasicCoin_Coin'#0''(s->$coin)
}
function {:inline} $IsEqual'$bc_BasicCoin_Balance'#0''(s1: $bc_BasicCoin_Balance'#0', s2: $bc_BasicCoin_Balance'#0'): bool {
    s1 == s2
}
var $bc_BasicCoin_Balance'#0'_$memory: $Memory $bc_BasicCoin_Balance'#0';

// struct BasicCoin::Coin<#0> at .\sources\BasicCoin.move:13:5+66
datatype $bc_BasicCoin_Coin'#0' {
    $bc_BasicCoin_Coin'#0'($value: int)
}
function {:inline} $Update'$bc_BasicCoin_Coin'#0''_value(s: $bc_BasicCoin_Coin'#0', x: int): $bc_BasicCoin_Coin'#0' {
    $bc_BasicCoin_Coin'#0'(x)
}
function $IsValid'$bc_BasicCoin_Coin'#0''(s: $bc_BasicCoin_Coin'#0'): bool {
    $IsValid'u64'(s->$value)
}
function {:inline} $IsEqual'$bc_BasicCoin_Coin'#0''(s1: $bc_BasicCoin_Coin'#0', s2: $bc_BasicCoin_Coin'#0'): bool {
    s1 == s2
}

// fun BasicCoin::balance_of<#0> [baseline] at .\sources\BasicCoin.move:66:5+136
procedure {:inline 1} $bc_BasicCoin_balance_of'#0'(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: $bc_BasicCoin_Balance'#0';
    var $t2: int;
    var $t3: $bc_BasicCoin_Coin'#0';
    var $t4: int;
    var $t0: int;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[owner]($t0) at .\sources\BasicCoin.move:66:5+1
    assume {:print "$at(2,2215,2216)"} true;
    assume {:print "$track_local(3,0,0):", $t0} $t0 == $t0;

    // $t1 := get_global<0xbc::BasicCoin::Balance<#0>>($t0) on_abort goto L2 with $t2 at .\sources\BasicCoin.move:67:9+39
    assume {:print "$at(2,2295,2334)"} true;
    if (!$ResourceExists($bc_BasicCoin_Balance'#0'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t1 := $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $t0);
    }
    if ($abort_flag) {
        assume {:print "$at(2,2295,2334)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(3,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := get_field<0xbc::BasicCoin::Balance<#0>>.coin($t1) at .\sources\BasicCoin.move:67:9+44
    $t3 := $t1->$coin;

    // $t4 := get_field<0xbc::BasicCoin::Coin<#0>>.value($t3) at .\sources\BasicCoin.move:67:9+50
    $t4 := $t3->$value;

    // trace_return[0]($t4) at .\sources\BasicCoin.move:67:9+50
    assume {:print "$track_return(3,0,0):", $t4} $t4 == $t4;

    // label L1 at .\sources\BasicCoin.move:68:5+1
    assume {:print "$at(2,2350,2351)"} true;
L1:

    // return $t4 at .\sources\BasicCoin.move:68:5+1
    assume {:print "$at(2,2350,2351)"} true;
    $ret0 := $t4;
    return;

    // label L2 at .\sources\BasicCoin.move:68:5+1
L2:

    // abort($t2) at .\sources\BasicCoin.move:68:5+1
    assume {:print "$at(2,2350,2351)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun BasicCoin::balance_of [verification] at .\sources\BasicCoin.move:66:5+136
procedure {:timeLimit 40} $bc_BasicCoin_balance_of$verify(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: $bc_BasicCoin_Balance'#0';
    var $t2: int;
    var $t3: $bc_BasicCoin_Coin'#0';
    var $t4: int;
    var $t0: int;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    var $bc_BasicCoin_Balance'#0'_$memory#0: $Memory $bc_BasicCoin_Balance'#0';
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at .\sources\BasicCoin.move:66:5+1
    assume {:print "$at(2,2215,2216)"} true;
    assume $IsValid'address'($t0);

    // assume forall $rsc: 0xbc::BasicCoin::Balance<#0>: ResourceDomain<0xbc::BasicCoin::Balance<#0>>(): WellFormed($rsc) at .\sources\BasicCoin.move:66:5+1
    assume (forall $a_0: int :: {$ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $a_0)}(var $rsc := $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $a_0);
    ($IsValid'$bc_BasicCoin_Balance'#0''($rsc))));

    // @0 := save_mem(BasicCoin::Balance<#0>) at .\sources\BasicCoin.move:66:5+1
    $bc_BasicCoin_Balance'#0'_$memory#0 := $bc_BasicCoin_Balance'#0'_$memory;

    // trace_local[owner]($t0) at .\sources\BasicCoin.move:66:5+1
    assume {:print "$track_local(3,0,0):", $t0} $t0 == $t0;

    // $t1 := get_global<0xbc::BasicCoin::Balance<#0>>($t0) on_abort goto L2 with $t2 at .\sources\BasicCoin.move:67:9+39
    assume {:print "$at(2,2295,2334)"} true;
    if (!$ResourceExists($bc_BasicCoin_Balance'#0'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t1 := $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $t0);
    }
    if ($abort_flag) {
        assume {:print "$at(2,2295,2334)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(3,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := get_field<0xbc::BasicCoin::Balance<#0>>.coin($t1) at .\sources\BasicCoin.move:67:9+44
    $t3 := $t1->$coin;

    // $t4 := get_field<0xbc::BasicCoin::Coin<#0>>.value($t3) at .\sources\BasicCoin.move:67:9+50
    $t4 := $t3->$value;

    // trace_return[0]($t4) at .\sources\BasicCoin.move:67:9+50
    assume {:print "$track_return(3,0,0):", $t4} $t4 == $t4;

    // label L1 at .\sources\BasicCoin.move:68:5+1
    assume {:print "$at(2,2350,2351)"} true;
L1:

    // assert Not(Not(exists[@0]<0xbc::BasicCoin::Balance<#0>>($t0))) at .\sources\BasicCoin.move:72:9+44
    assume {:print "$at(2,2419,2463)"} true;
    assert {:msg "assert_failed(2,2419,2463): function does not abort under this condition"}
      !!$ResourceExists($bc_BasicCoin_Balance'#0'_$memory#0, $t0);

    // return $t4 at .\sources\BasicCoin.move:72:9+44
    $ret0 := $t4;
    return;

    // label L2 at .\sources\BasicCoin.move:68:5+1
    assume {:print "$at(2,2350,2351)"} true;
L2:

    // assert Not(exists[@0]<0xbc::BasicCoin::Balance<#0>>($t0)) at .\sources\BasicCoin.move:70:5+112
    assume {:print "$at(2,2357,2469)"} true;
    assert {:msg "assert_failed(2,2357,2469): abort not covered by any of the `aborts_if` clauses"}
      !$ResourceExists($bc_BasicCoin_Balance'#0'_$memory#0, $t0);

    // abort($t2) at .\sources\BasicCoin.move:70:5+112
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun BasicCoin::burn [verification] at .\sources\BasicCoin.move:56:5+244
procedure {:timeLimit 40} $bc_BasicCoin_burn$verify(_$t0: int, _$t1: int, _$t2: #0) returns ()
{
    // declare local variables
    var $t3: int;
    var $t4: $bc_BasicCoin_Coin'#0';
    var $t5: int;
    var $t6: int;
    var $t0: int;
    var $t1: int;
    var $t2: #0;
    var $temp_0'#0': #0;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at .\sources\BasicCoin.move:56:5+1
    assume {:print "$at(2,1926,1927)"} true;
    assume $IsValid'address'($t0);

    // assume WellFormed($t1) at .\sources\BasicCoin.move:56:5+1
    assume $IsValid'u64'($t1);

    // assume WellFormed($t2) at .\sources\BasicCoin.move:56:5+1
    assume $IsValid'#0'($t2);

    // assume forall $rsc: 0xbc::BasicCoin::Balance<#0>: ResourceDomain<0xbc::BasicCoin::Balance<#0>>(): WellFormed($rsc) at .\sources\BasicCoin.move:56:5+1
    assume (forall $a_0: int :: {$ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $a_0)}(var $rsc := $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $a_0);
    ($IsValid'$bc_BasicCoin_Balance'#0''($rsc))));

    // trace_local[burn_addr]($t0) at .\sources\BasicCoin.move:56:5+1
    assume {:print "$track_local(3,1,0):", $t0} $t0 == $t0;

    // trace_local[amount]($t1) at .\sources\BasicCoin.move:56:5+1
    assume {:print "$track_local(3,1,1):", $t1} $t1 == $t1;

    // trace_local[_witness]($t2) at .\sources\BasicCoin.move:56:5+1
    assume {:print "$track_local(3,1,2):", $t2} $t2 == $t2;

    // assume Identical($t3, select BasicCoin::Coin.value<0xbc::BasicCoin::Coin<#0>>(select BasicCoin::Balance.coin<0xbc::BasicCoin::Balance<#0>>(global<0xbc::BasicCoin::Balance<#0>>($t0)))) at .\sources\BasicCoin.move:111:9+57
    assume {:print "$at(2,4118,4175)"} true;
    assume ($t3 == $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $t0)->$coin->$value);

    // $t4 := BasicCoin::withdraw<#0>($t0, $t1) on_abort goto L2 with $t5 at .\sources\BasicCoin.move:58:33+37
    assume {:print "$at(2,2126,2163)"} true;
    call $t4 := $bc_BasicCoin_withdraw'#0'($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,2126,2163)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(3,1):", $t5} $t5 == $t5;
        goto L2;
    }

    // $t6 := unpack 0xbc::BasicCoin::Coin<#0>($t4) at .\sources\BasicCoin.move:58:13+17
    $t6 := $t4->$value;

    // drop($t6) at .\sources\BasicCoin.move:58:13+17

    // label L1 at .\sources\BasicCoin.move:59:5+1
    assume {:print "$at(2,2169,2170)"} true;
L1:

    // return () at .\sources\BasicCoin.move:59:5+1
    assume {:print "$at(2,2169,2170)"} true;
    return;

    // label L2 at .\sources\BasicCoin.move:59:5+1
L2:

    // abort($t5) at .\sources\BasicCoin.move:59:5+1
    assume {:print "$at(2,2169,2170)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun BasicCoin::deposit<#0> [baseline] at .\sources\BasicCoin.move:121:5+295
procedure {:inline 1} $bc_BasicCoin_deposit'#0'(_$t0: int, _$t1: $bc_BasicCoin_Coin'#0') returns ()
{
    // declare local variables
    var $t2: int;
    var $t3: $Mutation (int);
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: $Mutation ($bc_BasicCoin_Balance'#0');
    var $t10: $Mutation ($bc_BasicCoin_Coin'#0');
    var $t11: $Mutation (int);
    var $t12: int;
    var $t13: int;
    var $t0: int;
    var $t1: $bc_BasicCoin_Coin'#0';
    var $temp_0'$bc_BasicCoin_Coin'#0'': $bc_BasicCoin_Coin'#0';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // assume Identical($t5, select BasicCoin::Coin.value<0xbc::BasicCoin::Coin<#0>>(select BasicCoin::Balance.coin<0xbc::BasicCoin::Balance<#0>>(global<0xbc::BasicCoin::Balance<#0>>($t0)))) at .\sources\BasicCoin.move:129:9+57
    assume {:print "$at(2,4787,4844)"} true;
    assume ($t5 == $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $t0)->$coin->$value);

    // assume Identical($t6, select BasicCoin::Coin.value<0xbc::BasicCoin::Coin<#0>>($t1)) at .\sources\BasicCoin.move:130:9+30
    assume {:print "$at(2,4853,4883)"} true;
    assume ($t6 == $t1->$value);

    // trace_local[addr]($t0) at .\sources\BasicCoin.move:121:5+1
    assume {:print "$at(2,4463,4464)"} true;
    assume {:print "$track_local(3,2,0):", $t0} $t0 == $t0;

    // trace_local[check]($t1) at .\sources\BasicCoin.move:121:5+1
    assume {:print "$track_local(3,2,1):", $t1} $t1 == $t1;

    // $t7 := BasicCoin::balance_of<#0>($t0) on_abort goto L2 with $t8 at .\sources\BasicCoin.move:122:23+26
    assume {:print "$at(2,4563,4589)"} true;
    call $t7 := $bc_BasicCoin_balance_of'#0'($t0);
    if ($abort_flag) {
        assume {:print "$at(2,4563,4589)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(3,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // $t9 := borrow_global<0xbc::BasicCoin::Balance<#0>>($t0) on_abort goto L2 with $t8 at .\sources\BasicCoin.move:123:32+42
    assume {:print "$at(2,4622,4664)"} true;
    if (!$ResourceExists($bc_BasicCoin_Balance'#0'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t9 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(2,4622,4664)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(3,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // $t10 := borrow_field<0xbc::BasicCoin::Balance<#0>>.coin($t9) at .\sources\BasicCoin.move:123:32+47
    $t10 := $ChildMutation($t9, 0, $Dereference($t9)->$coin);

    // $t11 := borrow_field<0xbc::BasicCoin::Coin<#0>>.value($t10) at .\sources\BasicCoin.move:123:27+58
    $t11 := $ChildMutation($t10, 0, $Dereference($t10)->$value);

    // $t12 := unpack 0xbc::BasicCoin::Coin<#0>($t1) at .\sources\BasicCoin.move:124:13+14
    assume {:print "$at(2,4689,4703)"} true;
    $t12 := $t1->$value;

    // trace_local[value]($t12) at .\sources\BasicCoin.move:125:24+7
    assume {:print "$at(2,4736,4743)"} true;
    assume {:print "$track_local(3,2,2):", $t12} $t12 == $t12;

    // trace_local[balance_ref]($t11) at .\sources\BasicCoin.move:125:24+7
    $temp_0'u64' := $Dereference($t11);
    assume {:print "$track_local(3,2,3):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t13 := +($t7, $t12) on_abort goto L2 with $t8 at .\sources\BasicCoin.move:125:24+15
    call $t13 := $AddU64($t7, $t12);
    if ($abort_flag) {
        assume {:print "$at(2,4736,4751)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(3,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // write_ref($t11, $t13) at .\sources\BasicCoin.move:125:9+30
    $t11 := $UpdateMutation($t11, $t13);

    // write_back[Reference($t10).value (u64)]($t11) at .\sources\BasicCoin.move:125:9+30
    $t10 := $UpdateMutation($t10, $Update'$bc_BasicCoin_Coin'#0''_value($Dereference($t10), $Dereference($t11)));

    // write_back[Reference($t9).coin (0xbc::BasicCoin::Coin<#0>)]($t10) at .\sources\BasicCoin.move:125:9+30
    $t9 := $UpdateMutation($t9, $Update'$bc_BasicCoin_Balance'#0''_coin($Dereference($t9), $Dereference($t10)));

    // write_back[0xbc::BasicCoin::Balance<#0>@]($t9) at .\sources\BasicCoin.move:125:9+30
    $bc_BasicCoin_Balance'#0'_$memory := $ResourceUpdate($bc_BasicCoin_Balance'#0'_$memory, $GlobalLocationAddress($t9),
        $Dereference($t9));

    // label L1 at .\sources\BasicCoin.move:126:5+1
    assume {:print "$at(2,4757,4758)"} true;
L1:

    // return () at .\sources\BasicCoin.move:126:5+1
    assume {:print "$at(2,4757,4758)"} true;
    return;

    // label L2 at .\sources\BasicCoin.move:126:5+1
L2:

    // abort($t8) at .\sources\BasicCoin.move:126:5+1
    assume {:print "$at(2,4757,4758)"} true;
    $abort_code := $t8;
    $abort_flag := true;
    return;

}

// fun BasicCoin::deposit [verification] at .\sources\BasicCoin.move:121:5+295
procedure {:timeLimit 40} $bc_BasicCoin_deposit$verify(_$t0: int, _$t1: $bc_BasicCoin_Coin'#0') returns ()
{
    // declare local variables
    var $t2: int;
    var $t3: $Mutation (int);
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: $Mutation ($bc_BasicCoin_Balance'#0');
    var $t10: $Mutation ($bc_BasicCoin_Coin'#0');
    var $t11: $Mutation (int);
    var $t12: int;
    var $t13: int;
    var $t14: int;
    var $t0: int;
    var $t1: $bc_BasicCoin_Coin'#0';
    var $temp_0'$bc_BasicCoin_Coin'#0'': $bc_BasicCoin_Coin'#0';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    var $bc_BasicCoin_Balance'#0'_$memory#4: $Memory $bc_BasicCoin_Balance'#0';
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at .\sources\BasicCoin.move:121:5+1
    assume {:print "$at(2,4463,4464)"} true;
    assume $IsValid'address'($t0);

    // assume WellFormed($t1) at .\sources\BasicCoin.move:121:5+1
    assume $IsValid'$bc_BasicCoin_Coin'#0''($t1);

    // assume forall $rsc: 0xbc::BasicCoin::Balance<#0>: ResourceDomain<0xbc::BasicCoin::Balance<#0>>(): WellFormed($rsc) at .\sources\BasicCoin.move:121:5+1
    assume (forall $a_0: int :: {$ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $a_0)}(var $rsc := $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $a_0);
    ($IsValid'$bc_BasicCoin_Balance'#0''($rsc))));

    // assume Identical($t5, select BasicCoin::Coin.value<0xbc::BasicCoin::Coin<#0>>(select BasicCoin::Balance.coin<0xbc::BasicCoin::Balance<#0>>(global<0xbc::BasicCoin::Balance<#0>>($t0)))) at .\sources\BasicCoin.move:129:9+57
    assume {:print "$at(2,4787,4844)"} true;
    assume ($t5 == $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $t0)->$coin->$value);

    // assume Identical($t6, select BasicCoin::Coin.value<0xbc::BasicCoin::Coin<#0>>($t1)) at .\sources\BasicCoin.move:130:9+30
    assume {:print "$at(2,4853,4883)"} true;
    assume ($t6 == $t1->$value);

    // @4 := save_mem(BasicCoin::Balance<#0>) at .\sources\BasicCoin.move:121:5+1
    assume {:print "$at(2,4463,4464)"} true;
    $bc_BasicCoin_Balance'#0'_$memory#4 := $bc_BasicCoin_Balance'#0'_$memory;

    // trace_local[addr]($t0) at .\sources\BasicCoin.move:121:5+1
    assume {:print "$track_local(3,2,0):", $t0} $t0 == $t0;

    // trace_local[check]($t1) at .\sources\BasicCoin.move:121:5+1
    assume {:print "$track_local(3,2,1):", $t1} $t1 == $t1;

    // $t7 := BasicCoin::balance_of<#0>($t0) on_abort goto L2 with $t8 at .\sources\BasicCoin.move:122:23+26
    assume {:print "$at(2,4563,4589)"} true;
    call $t7 := $bc_BasicCoin_balance_of'#0'($t0);
    if ($abort_flag) {
        assume {:print "$at(2,4563,4589)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(3,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // $t9 := borrow_global<0xbc::BasicCoin::Balance<#0>>($t0) on_abort goto L2 with $t8 at .\sources\BasicCoin.move:123:32+42
    assume {:print "$at(2,4622,4664)"} true;
    if (!$ResourceExists($bc_BasicCoin_Balance'#0'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t9 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(2,4622,4664)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(3,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // $t10 := borrow_field<0xbc::BasicCoin::Balance<#0>>.coin($t9) at .\sources\BasicCoin.move:123:32+47
    $t10 := $ChildMutation($t9, 0, $Dereference($t9)->$coin);

    // $t11 := borrow_field<0xbc::BasicCoin::Coin<#0>>.value($t10) at .\sources\BasicCoin.move:123:27+58
    $t11 := $ChildMutation($t10, 0, $Dereference($t10)->$value);

    // $t12 := unpack 0xbc::BasicCoin::Coin<#0>($t1) at .\sources\BasicCoin.move:124:13+14
    assume {:print "$at(2,4689,4703)"} true;
    $t12 := $t1->$value;

    // trace_local[value]($t12) at .\sources\BasicCoin.move:125:24+7
    assume {:print "$at(2,4736,4743)"} true;
    assume {:print "$track_local(3,2,2):", $t12} $t12 == $t12;

    // trace_local[balance_ref]($t11) at .\sources\BasicCoin.move:125:24+7
    $temp_0'u64' := $Dereference($t11);
    assume {:print "$track_local(3,2,3):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t13 := +($t7, $t12) on_abort goto L2 with $t8 at .\sources\BasicCoin.move:125:24+15
    call $t13 := $AddU64($t7, $t12);
    if ($abort_flag) {
        assume {:print "$at(2,4736,4751)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(3,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // write_ref($t11, $t13) at .\sources\BasicCoin.move:125:9+30
    $t11 := $UpdateMutation($t11, $t13);

    // write_back[Reference($t10).value (u64)]($t11) at .\sources\BasicCoin.move:125:9+30
    $t10 := $UpdateMutation($t10, $Update'$bc_BasicCoin_Coin'#0''_value($Dereference($t10), $Dereference($t11)));

    // write_back[Reference($t9).coin (0xbc::BasicCoin::Coin<#0>)]($t10) at .\sources\BasicCoin.move:125:9+30
    $t9 := $UpdateMutation($t9, $Update'$bc_BasicCoin_Balance'#0''_coin($Dereference($t9), $Dereference($t10)));

    // write_back[0xbc::BasicCoin::Balance<#0>@]($t9) at .\sources\BasicCoin.move:125:9+30
    $bc_BasicCoin_Balance'#0'_$memory := $ResourceUpdate($bc_BasicCoin_Balance'#0'_$memory, $GlobalLocationAddress($t9),
        $Dereference($t9));

    // label L1 at .\sources\BasicCoin.move:126:5+1
    assume {:print "$at(2,4757,4758)"} true;
L1:

    // assume Identical($t14, select BasicCoin::Coin.value<0xbc::BasicCoin::Coin<#0>>(select BasicCoin::Balance.coin<0xbc::BasicCoin::Balance<#0>>(global<0xbc::BasicCoin::Balance<#0>>($t0)))) at .\sources\BasicCoin.move:135:9+67
    assume {:print "$at(2,4997,5064)"} true;
    assume ($t14 == $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $t0)->$coin->$value);

    // assert Not(Not(exists[@4]<0xbc::BasicCoin::Balance<#0>>($t0))) at .\sources\BasicCoin.move:132:9+43
    assume {:print "$at(2,4893,4936)"} true;
    assert {:msg "assert_failed(2,4893,4936): function does not abort under this condition"}
      !!$ResourceExists($bc_BasicCoin_Balance'#0'_$memory#4, $t0);

    // assert Not(Gt(Add($t5, $t6), 18446744073709551615)) at .\sources\BasicCoin.move:133:9+42
    assume {:print "$at(2,4945,4987)"} true;
    assert {:msg "assert_failed(2,4945,4987): function does not abort under this condition"}
      !(($t5 + $t6) > 18446744073709551615);

    // assert Eq<u64>($t14, Add($t5, $t6)) at .\sources\BasicCoin.move:136:9+46
    assume {:print "$at(2,5073,5119)"} true;
    assert {:msg "assert_failed(2,5073,5119): post-condition does not hold"}
      $IsEqual'u64'($t14, ($t5 + $t6));

    // return () at .\sources\BasicCoin.move:136:9+46
    return;

    // label L2 at .\sources\BasicCoin.move:126:5+1
    assume {:print "$at(2,4757,4758)"} true;
L2:

    // assert Or(Not(exists[@4]<0xbc::BasicCoin::Balance<#0>>($t0)), Gt(Add($t5, $t6), 18446744073709551615)) at .\sources\BasicCoin.move:128:5+361
    assume {:print "$at(2,4764,5125)"} true;
    assert {:msg "assert_failed(2,4764,5125): abort not covered by any of the `aborts_if` clauses"}
      (!$ResourceExists($bc_BasicCoin_Balance'#0'_$memory#4, $t0) || (($t5 + $t6) > 18446744073709551615));

    // abort($t8) at .\sources\BasicCoin.move:128:5+361
    $abort_code := $t8;
    $abort_flag := true;
    return;

}

// fun BasicCoin::mint [verification] at .\sources\BasicCoin.move:45:5+232
procedure {:timeLimit 40} $bc_BasicCoin_mint$verify(_$t0: int, _$t1: int, _$t2: #0) returns ()
{
    // declare local variables
    var $t3: int;
    var $t4: $bc_BasicCoin_Coin'#0';
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t0: int;
    var $t1: int;
    var $t2: #0;
    var $temp_0'#0': #0;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    var $bc_BasicCoin_Balance'#0'_$memory#6: $Memory $bc_BasicCoin_Balance'#0';
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at .\sources\BasicCoin.move:45:5+1
    assume {:print "$at(2,1425,1426)"} true;
    assume $IsValid'address'($t0);

    // assume WellFormed($t1) at .\sources\BasicCoin.move:45:5+1
    assume $IsValid'u64'($t1);

    // assume WellFormed($t2) at .\sources\BasicCoin.move:45:5+1
    assume $IsValid'#0'($t2);

    // assume forall $rsc: 0xbc::BasicCoin::Balance<#0>: ResourceDomain<0xbc::BasicCoin::Balance<#0>>(): WellFormed($rsc) at .\sources\BasicCoin.move:45:5+1
    assume (forall $a_0: int :: {$ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $a_0)}(var $rsc := $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $a_0);
    ($IsValid'$bc_BasicCoin_Balance'#0''($rsc))));

    // assume Identical($t3, select BasicCoin::Coin.value<0xbc::BasicCoin::Coin<#0>>(select BasicCoin::Balance.coin<0xbc::BasicCoin::Balance<#0>>(global<0xbc::BasicCoin::Balance<#0>>($t0)))) at .\sources\BasicCoin.move:142:9+57
    assume {:print "$at(2,5221,5278)"} true;
    assume ($t3 == $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $t0)->$coin->$value);

    // @6 := save_mem(BasicCoin::Balance<#0>) at .\sources\BasicCoin.move:45:5+1
    assume {:print "$at(2,1425,1426)"} true;
    $bc_BasicCoin_Balance'#0'_$memory#6 := $bc_BasicCoin_Balance'#0'_$memory;

    // trace_local[mint_addr]($t0) at .\sources\BasicCoin.move:45:5+1
    assume {:print "$track_local(3,3,0):", $t0} $t0 == $t0;

    // trace_local[amount]($t1) at .\sources\BasicCoin.move:45:5+1
    assume {:print "$track_local(3,3,1):", $t1} $t1 == $t1;

    // trace_local[_witness]($t2) at .\sources\BasicCoin.move:45:5+1
    assume {:print "$track_local(3,3,2):", $t2} $t2 == $t2;

    // $t4 := pack 0xbc::BasicCoin::Coin<#0>($t1) at .\sources\BasicCoin.move:47:28+32
    assume {:print "$at(2,1617,1649)"} true;
    $t4 := $bc_BasicCoin_Coin'#0'($t1);

    // assume Identical($t5, select BasicCoin::Coin.value<0xbc::BasicCoin::Coin<#0>>(select BasicCoin::Balance.coin<0xbc::BasicCoin::Balance<#0>>(global<0xbc::BasicCoin::Balance<#0>>($t0)))) at .\sources\BasicCoin.move:129:9+57
    assume {:print "$at(2,4787,4844)"} true;
    assume ($t5 == $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $t0)->$coin->$value);

    // assume Identical($t6, select BasicCoin::Coin.value<0xbc::BasicCoin::Coin<#0>>($t4)) at .\sources\BasicCoin.move:130:9+30
    assume {:print "$at(2,4853,4883)"} true;
    assume ($t6 == $t4->$value);

    // BasicCoin::deposit<#0>($t0, $t4) on_abort goto L2 with $t7 at .\sources\BasicCoin.move:47:9+52
    assume {:print "$at(2,1598,1650)"} true;
    call $bc_BasicCoin_deposit'#0'($t0, $t4);
    if ($abort_flag) {
        assume {:print "$at(2,1598,1650)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(3,3):", $t7} $t7 == $t7;
        goto L2;
    }

    // label L1 at .\sources\BasicCoin.move:48:5+1
    assume {:print "$at(2,1656,1657)"} true;
L1:

    // assume Identical($t8, select BasicCoin::Coin.value<0xbc::BasicCoin::Coin<#0>>(select BasicCoin::Balance.coin<0xbc::BasicCoin::Balance<#0>>(global<0xbc::BasicCoin::Balance<#0>>($t0)))) at .\sources\BasicCoin.move:147:9+67
    assume {:print "$at(2,5387,5454)"} true;
    assume ($t8 == $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $t0)->$coin->$value);

    // assert Not(Not(exists[@6]<0xbc::BasicCoin::Balance<#0>>($t0))) at .\sources\BasicCoin.move:144:9+43
    assume {:print "$at(2,5288,5331)"} true;
    assert {:msg "assert_failed(2,5288,5331): function does not abort under this condition"}
      !!$ResourceExists($bc_BasicCoin_Balance'#0'_$memory#6, $t0);

    // assert Not(Gt(Add($t3, $t1), 18446744073709551615)) at .\sources\BasicCoin.move:145:9+37
    assume {:print "$at(2,5340,5377)"} true;
    assert {:msg "assert_failed(2,5340,5377): function does not abort under this condition"}
      !(($t3 + $t1) > 18446744073709551615);

    // assert Eq<u64>($t8, Add($t3, $t1)) at .\sources\BasicCoin.move:148:9+41
    assume {:print "$at(2,5463,5504)"} true;
    assert {:msg "assert_failed(2,5463,5504): post-condition does not hold"}
      $IsEqual'u64'($t8, ($t3 + $t1));

    // return () at .\sources\BasicCoin.move:148:9+41
    return;

    // label L2 at .\sources\BasicCoin.move:48:5+1
    assume {:print "$at(2,1656,1657)"} true;
L2:

    // assert Or(Not(exists[@6]<0xbc::BasicCoin::Balance<#0>>($t0)), Gt(Add($t3, $t1), 18446744073709551615)) at .\sources\BasicCoin.move:50:5+84
    assume {:print "$at(2,1663,1747)"} true;
    assert {:msg "assert_failed(2,1663,1747): abort not covered by any of the `aborts_if` clauses"}
      (!$ResourceExists($bc_BasicCoin_Balance'#0'_$memory#6, $t0) || (($t3 + $t1) > 18446744073709551615));

    // abort($t7) at .\sources\BasicCoin.move:50:5+84
    $abort_code := $t7;
    $abort_flag := true;
    return;

}

// fun BasicCoin::publish_balance [verification] at .\sources\BasicCoin.move:21:5+302
procedure {:timeLimit 40} $bc_BasicCoin_publish_balance$verify(_$t0: $signer) returns ()
{
    // declare local variables
    var $t1: $bc_BasicCoin_Coin'#0';
    var $t2: int;
    var $t3: $bc_BasicCoin_Coin'#0';
    var $t4: int;
    var $t5: int;
    var $t6: bool;
    var $t7: $bc_BasicCoin_Balance'#0';
    var $t8: int;
    var $t9: int;
    var $t10: int;
    var $t0: $signer;
    var $temp_0'$bc_BasicCoin_Coin'#0'': $bc_BasicCoin_Coin'#0';
    var $temp_0'signer': $signer;
    var $bc_BasicCoin_Balance'#0'_$memory#7: $Memory $bc_BasicCoin_Balance'#0';
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at .\sources\BasicCoin.move:21:5+1
    assume {:print "$at(2,510,511)"} true;
    assume $IsValid'signer'($t0) && $1_signer_is_txn_signer($t0) && $1_signer_is_txn_signer_addr($t0->$addr);

    // assume forall $rsc: 0xbc::BasicCoin::Balance<#0>: ResourceDomain<0xbc::BasicCoin::Balance<#0>>(): WellFormed($rsc) at .\sources\BasicCoin.move:21:5+1
    assume (forall $a_0: int :: {$ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $a_0)}(var $rsc := $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $a_0);
    ($IsValid'$bc_BasicCoin_Balance'#0''($rsc))));

    // @7 := save_mem(BasicCoin::Balance<#0>) at .\sources\BasicCoin.move:21:5+1
    $bc_BasicCoin_Balance'#0'_$memory#7 := $bc_BasicCoin_Balance'#0'_$memory;

    // trace_local[account]($t0) at .\sources\BasicCoin.move:21:5+1
    assume {:print "$track_local(3,4,0):", $t0} $t0 == $t0;

    // $t2 := 0 at .\sources\BasicCoin.move:22:50+1
    assume {:print "$at(2,616,617)"} true;
    $t2 := 0;
    assume $IsValid'u64'($t2);

    // $t3 := pack 0xbc::BasicCoin::Coin<#0>($t2) at .\sources\BasicCoin.move:22:26+27
    $t3 := $bc_BasicCoin_Coin'#0'($t2);

    // trace_local[empty_coin]($t3) at .\sources\BasicCoin.move:22:26+27
    assume {:print "$track_local(3,4,1):", $t3} $t3 == $t3;

    // $t4 := signer::address_of($t0) on_abort goto L3 with $t5 at .\sources\BasicCoin.move:23:44+27
    assume {:print "$at(2,664,691)"} true;
    call $t4 := $1_signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(2,664,691)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(3,4):", $t5} $t5 == $t5;
        goto L3;
    }

    // $t6 := exists<0xbc::BasicCoin::Balance<#0>>($t4) at .\sources\BasicCoin.move:23:18+54
    $t6 := $ResourceExists($bc_BasicCoin_Balance'#0'_$memory, $t4);

    // if ($t6) goto L0 else goto L1 at .\sources\BasicCoin.move:23:17+55
    if ($t6) { goto L0; } else { goto L1; }

    // label L1 at .\sources\BasicCoin.move:24:17+7
    assume {:print "$at(2,756,763)"} true;
L1:

    // $t7 := pack 0xbc::BasicCoin::Balance<#0>($t3) at .\sources\BasicCoin.move:24:26+39
    assume {:print "$at(2,765,804)"} true;
    $t7 := $bc_BasicCoin_Balance'#0'($t3);

    // move_to<0xbc::BasicCoin::Balance<#0>>($t7, $t0) on_abort goto L3 with $t5 at .\sources\BasicCoin.move:24:9+57
    if ($ResourceExists($bc_BasicCoin_Balance'#0'_$memory, $t0->$addr)) {
        call $ExecFailureAbort();
    } else {
        $bc_BasicCoin_Balance'#0'_$memory := $ResourceUpdate($bc_BasicCoin_Balance'#0'_$memory, $t0->$addr, $t7);
    }
    if ($abort_flag) {
        assume {:print "$at(2,748,805)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(3,4):", $t5} $t5 == $t5;
        goto L3;
    }

    // goto L2 at .\sources\BasicCoin.move:21:60+247
    assume {:print "$at(2,565,812)"} true;
    goto L2;

    // label L0 at .\sources\BasicCoin.move:23:9+6
    assume {:print "$at(2,629,635)"} true;
L0:

    // $t8 := 2 at .\sources\BasicCoin.move:23:96+20
    assume {:print "$at(2,716,736)"} true;
    $t8 := 2;
    assume $IsValid'u64'($t8);

    // $t9 := error::already_exists($t8) on_abort goto L3 with $t5 at .\sources\BasicCoin.move:23:74+43
    call $t9 := $1_error_already_exists($t8);
    if ($abort_flag) {
        assume {:print "$at(2,694,737)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(3,4):", $t5} $t5 == $t5;
        goto L3;
    }

    // trace_abort($t9) at .\sources\BasicCoin.move:23:9+6
    assume {:print "$at(2,629,635)"} true;
    assume {:print "$track_abort(3,4):", $t9} $t9 == $t9;

    // $t5 := move($t9) at .\sources\BasicCoin.move:23:9+6
    $t5 := $t9;

    // goto L3 at .\sources\BasicCoin.move:23:9+6
    goto L3;

    // label L2 at .\sources\BasicCoin.move:25:5+1
    assume {:print "$at(2,811,812)"} true;
L2:

    // assume Identical($t10, select BasicCoin::Coin.value<0xbc::BasicCoin::Coin<#0>>(select BasicCoin::Balance.coin<0xbc::BasicCoin::Balance<#0>>(global<0xbc::BasicCoin::Balance<#0>>(signer::$address_of($t0))))) at .\sources\BasicCoin.move:38:9+67
    assume {:print "$at(2,1134,1201)"} true;
    assume ($t10 == $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $1_signer_$address_of($t0))->$coin->$value);

    // assert Not(exists[@7]<0xbc::BasicCoin::Balance<#0>>(signer::$address_of[]($t0))) at .\sources\BasicCoin.move:35:9+42
    assume {:print "$at(2,1033,1075)"} true;
    assert {:msg "assert_failed(2,1033,1075): function does not abort under this condition"}
      !$ResourceExists($bc_BasicCoin_Balance'#0'_$memory#7, $1_signer_$address_of($t0));

    // assert exists<0xbc::BasicCoin::Balance<#0>>(signer::$address_of($t0)) at .\sources\BasicCoin.move:37:9+40
    assume {:print "$at(2,1085,1125)"} true;
    assert {:msg "assert_failed(2,1085,1125): post-condition does not hold"}
      $ResourceExists($bc_BasicCoin_Balance'#0'_$memory, $1_signer_$address_of($t0));

    // assert Eq<u64>($t10, 0) at .\sources\BasicCoin.move:40:9+31
    assume {:print "$at(2,1211,1242)"} true;
    assert {:msg "assert_failed(2,1211,1242): post-condition does not hold"}
      $IsEqual'u64'($t10, 0);

    // return () at .\sources\BasicCoin.move:40:9+31
    return;

    // label L3 at .\sources\BasicCoin.move:25:5+1
    assume {:print "$at(2,811,812)"} true;
L3:

    // assert exists[@7]<0xbc::BasicCoin::Balance<#0>>(signer::$address_of[]($t0)) at .\sources\BasicCoin.move:27:5+117
    assume {:print "$at(2,818,935)"} true;
    assert {:msg "assert_failed(2,818,935): abort not covered by any of the `aborts_if` clauses"}
      $ResourceExists($bc_BasicCoin_Balance'#0'_$memory#7, $1_signer_$address_of($t0));

    // abort($t5) at .\sources\BasicCoin.move:27:5+117
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun BasicCoin::transfer [verification] at .\sources\BasicCoin.move:77:5+315
procedure {:timeLimit 40} $bc_BasicCoin_transfer$verify(_$t0: $signer, _$t1: int, _$t2: int, _$t3: #0) returns ()
{
    // declare local variables
    var $t4: int;
    var $t5: $bc_BasicCoin_Coin'#0';
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: int;
    var $t10: int;
    var $t11: bool;
    var $t12: int;
    var $t13: $bc_BasicCoin_Coin'#0';
    var $t14: int;
    var $t15: int;
    var $t16: int;
    var $t17: int;
    var $t18: int;
    var $t0: $signer;
    var $t1: int;
    var $t2: int;
    var $t3: #0;
    var $temp_0'#0': #0;
    var $temp_0'$bc_BasicCoin_Coin'#0'': $bc_BasicCoin_Coin'#0';
    var $temp_0'address': int;
    var $temp_0'signer': $signer;
    var $temp_0'u64': int;
    var $bc_BasicCoin_Balance'#0'_$memory#8: $Memory $bc_BasicCoin_Balance'#0';
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;
    $t3 := _$t3;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at .\sources\BasicCoin.move:77:5+1
    assume {:print "$at(2,2664,2665)"} true;
    assume $IsValid'signer'($t0) && $1_signer_is_txn_signer($t0) && $1_signer_is_txn_signer_addr($t0->$addr);

    // assume WellFormed($t1) at .\sources\BasicCoin.move:77:5+1
    assume $IsValid'address'($t1);

    // assume WellFormed($t2) at .\sources\BasicCoin.move:77:5+1
    assume $IsValid'u64'($t2);

    // assume WellFormed($t3) at .\sources\BasicCoin.move:77:5+1
    assume $IsValid'#0'($t3);

    // assume forall $rsc: 0xbc::BasicCoin::Balance<#0>: ResourceDomain<0xbc::BasicCoin::Balance<#0>>(): WellFormed($rsc) at .\sources\BasicCoin.move:77:5+1
    assume (forall $a_0: int :: {$ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $a_0)}(var $rsc := $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $a_0);
    ($IsValid'$bc_BasicCoin_Balance'#0''($rsc))));

    // assume Identical($t6, signer::$address_of($t0)) at .\sources\BasicCoin.move:85:9+41
    assume {:print "$at(2,3009,3050)"} true;
    assume ($t6 == $1_signer_$address_of($t0));

    // assume Identical($t7, select BasicCoin::Coin.value<0xbc::BasicCoin::Coin<#0>>(select BasicCoin::Balance.coin<0xbc::BasicCoin::Balance<#0>>(global<0xbc::BasicCoin::Balance<#0>>($t6)))) at .\sources\BasicCoin.move:87:9+67
    assume {:print "$at(2,3060,3127)"} true;
    assume ($t7 == $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $t6)->$coin->$value);

    // assume Identical($t8, select BasicCoin::Coin.value<0xbc::BasicCoin::Coin<#0>>(select BasicCoin::Balance.coin<0xbc::BasicCoin::Balance<#0>>(global<0xbc::BasicCoin::Balance<#0>>($t1)))) at .\sources\BasicCoin.move:88:9+58
    assume {:print "$at(2,3136,3194)"} true;
    assume ($t8 == $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $t1)->$coin->$value);

    // @8 := save_mem(BasicCoin::Balance<#0>) at .\sources\BasicCoin.move:77:5+1
    assume {:print "$at(2,2664,2665)"} true;
    $bc_BasicCoin_Balance'#0'_$memory#8 := $bc_BasicCoin_Balance'#0'_$memory;

    // trace_local[from]($t0) at .\sources\BasicCoin.move:77:5+1
    assume {:print "$track_local(3,5,0):", $t0} $t0 == $t0;

    // trace_local[to]($t1) at .\sources\BasicCoin.move:77:5+1
    assume {:print "$track_local(3,5,1):", $t1} $t1 == $t1;

    // trace_local[amount]($t2) at .\sources\BasicCoin.move:77:5+1
    assume {:print "$track_local(3,5,2):", $t2} $t2 == $t2;

    // trace_local[_witness]($t3) at .\sources\BasicCoin.move:77:5+1
    assume {:print "$track_local(3,5,3):", $t3} $t3 == $t3;

    // $t9 := signer::address_of($t0) on_abort goto L3 with $t10 at .\sources\BasicCoin.move:78:25+24
    assume {:print "$at(2,2804,2828)"} true;
    call $t9 := $1_signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(2,2804,2828)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(3,5):", $t10} $t10 == $t10;
        goto L3;
    }

    // trace_local[from_addr]($t9) at .\sources\BasicCoin.move:78:25+24
    assume {:print "$track_local(3,5,4):", $t9} $t9 == $t9;

    // $t11 := !=($t9, $t1) at .\sources\BasicCoin.move:79:17+15
    assume {:print "$at(2,2846,2861)"} true;
    $t11 := !$IsEqual'address'($t9, $t1);

    // if ($t11) goto L1 else goto L0 at .\sources\BasicCoin.move:79:9+6
    if ($t11) { goto L1; } else { goto L0; }

    // label L1 at .\sources\BasicCoin.move:80:40+9
    assume {:print "$at(2,2916,2925)"} true;
L1:

    // assume Identical($t12, select BasicCoin::Coin.value<0xbc::BasicCoin::Coin<#0>>(select BasicCoin::Balance.coin<0xbc::BasicCoin::Balance<#0>>(global<0xbc::BasicCoin::Balance<#0>>($t9)))) at .\sources\BasicCoin.move:111:9+57
    assume {:print "$at(2,4118,4175)"} true;
    assume ($t12 == $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $t9)->$coin->$value);

    // $t13 := BasicCoin::withdraw<#0>($t9, $t2) on_abort goto L3 with $t10 at .\sources\BasicCoin.move:80:21+37
    assume {:print "$at(2,2897,2934)"} true;
    call $t13 := $bc_BasicCoin_withdraw'#0'($t9, $t2);
    if ($abort_flag) {
        assume {:print "$at(2,2897,2934)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(3,5):", $t10} $t10 == $t10;
        goto L3;
    }

    // trace_local[check]($t13) at .\sources\BasicCoin.move:80:21+37
    assume {:print "$track_local(3,5,5):", $t13} $t13 == $t13;

    // assume Identical($t14, select BasicCoin::Coin.value<0xbc::BasicCoin::Coin<#0>>(select BasicCoin::Balance.coin<0xbc::BasicCoin::Balance<#0>>(global<0xbc::BasicCoin::Balance<#0>>($t1)))) at .\sources\BasicCoin.move:129:9+57
    assume {:print "$at(2,4787,4844)"} true;
    assume ($t14 == $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $t1)->$coin->$value);

    // assume Identical($t15, select BasicCoin::Coin.value<0xbc::BasicCoin::Coin<#0>>($t13)) at .\sources\BasicCoin.move:130:9+30
    assume {:print "$at(2,4853,4883)"} true;
    assume ($t15 == $t13->$value);

    // BasicCoin::deposit<#0>($t1, $t13) on_abort goto L3 with $t10 at .\sources\BasicCoin.move:81:9+28
    assume {:print "$at(2,2944,2972)"} true;
    call $bc_BasicCoin_deposit'#0'($t1, $t13);
    if ($abort_flag) {
        assume {:print "$at(2,2944,2972)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(3,5):", $t10} $t10 == $t10;
        goto L3;
    }

    // goto L2 at .\sources\BasicCoin.move:77:119+201
    assume {:print "$at(2,2778,2979)"} true;
    goto L2;

    // label L0 at .\sources\BasicCoin.move:79:34+11
    assume {:print "$at(2,2863,2874)"} true;
L0:

    // $t16 := 4 at .\sources\BasicCoin.move:79:34+11
    assume {:print "$at(2,2863,2874)"} true;
    $t16 := 4;
    assume $IsValid'u64'($t16);

    // trace_abort($t16) at .\sources\BasicCoin.move:79:9+6
    assume {:print "$at(2,2838,2844)"} true;
    assume {:print "$track_abort(3,5):", $t16} $t16 == $t16;

    // $t10 := move($t16) at .\sources\BasicCoin.move:79:9+6
    $t10 := $t16;

    // goto L3 at .\sources\BasicCoin.move:79:9+6
    goto L3;

    // label L2 at .\sources\BasicCoin.move:82:5+1
    assume {:print "$at(2,2978,2979)"} true;
L2:

    // assume Identical($t17, select BasicCoin::Coin.value<0xbc::BasicCoin::Coin<#0>>(select BasicCoin::Balance.coin<0xbc::BasicCoin::Balance<#0>>(global<0xbc::BasicCoin::Balance<#0>>($t6)))) at .\sources\BasicCoin.move:89:9+77
    assume {:print "$at(2,3203,3280)"} true;
    assume ($t17 == $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $t6)->$coin->$value);

    // assume Identical($t18, select BasicCoin::Coin.value<0xbc::BasicCoin::Coin<#0>>(select BasicCoin::Balance.coin<0xbc::BasicCoin::Balance<#0>>(global<0xbc::BasicCoin::Balance<#0>>($t1)))) at .\sources\BasicCoin.move:90:9+68
    assume {:print "$at(2,3289,3357)"} true;
    assume ($t18 == $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $t1)->$coin->$value);

    // assert Not(Not(exists[@8]<0xbc::BasicCoin::Balance<#0>>($t6))) at .\sources\BasicCoin.move:92:9+48
    assume {:print "$at(2,3367,3415)"} true;
    assert {:msg "assert_failed(2,3367,3415): function does not abort under this condition"}
      !!$ResourceExists($bc_BasicCoin_Balance'#0'_$memory#8, $t6);

    // assert Not(Not(exists[@8]<0xbc::BasicCoin::Balance<#0>>($t1))) at .\sources\BasicCoin.move:93:9+41
    assume {:print "$at(2,3424,3465)"} true;
    assert {:msg "assert_failed(2,3424,3465): function does not abort under this condition"}
      !!$ResourceExists($bc_BasicCoin_Balance'#0'_$memory#8, $t1);

    // assert Not(Lt($t7, $t2)) at .\sources\BasicCoin.move:94:9+32
    assume {:print "$at(2,3474,3506)"} true;
    assert {:msg "assert_failed(2,3474,3506): function does not abort under this condition"}
      !($t7 < $t2);

    // assert Not(Gt(Add($t8, $t2), 18446744073709551615)) at .\sources\BasicCoin.move:95:9+40
    assume {:print "$at(2,3515,3555)"} true;
    assert {:msg "assert_failed(2,3515,3555): function does not abort under this condition"}
      !(($t8 + $t2) > 18446744073709551615);

    // assert Not(Eq<address>($t6, $t1)) at .\sources\BasicCoin.move:96:9+26
    assume {:print "$at(2,3564,3590)"} true;
    assert {:msg "assert_failed(2,3564,3590): function does not abort under this condition"}
      !$IsEqual'address'($t6, $t1);

    // assert Eq<u64>($t17, Sub($t7, $t2)) at .\sources\BasicCoin.move:98:9+51
    assume {:print "$at(2,3600,3651)"} true;
    assert {:msg "assert_failed(2,3600,3651): post-condition does not hold"}
      $IsEqual'u64'($t17, ($t7 - $t2));

    // assert Eq<u64>($t18, Add($t8, $t2)) at .\sources\BasicCoin.move:99:9+47
    assume {:print "$at(2,3660,3707)"} true;
    assert {:msg "assert_failed(2,3660,3707): post-condition does not hold"}
      $IsEqual'u64'($t18, ($t8 + $t2));

    // return () at .\sources\BasicCoin.move:99:9+47
    return;

    // label L3 at .\sources\BasicCoin.move:82:5+1
    assume {:print "$at(2,2978,2979)"} true;
L3:

    // assert Or(Or(Or(Or(Not(exists[@8]<0xbc::BasicCoin::Balance<#0>>($t6)), Not(exists[@8]<0xbc::BasicCoin::Balance<#0>>($t1))), Lt($t7, $t2)), Gt(Add($t8, $t2), 18446744073709551615)), Eq<address>($t6, $t1)) at .\sources\BasicCoin.move:84:5+728
    assume {:print "$at(2,2985,3713)"} true;
    assert {:msg "assert_failed(2,2985,3713): abort not covered by any of the `aborts_if` clauses"}
      ((((!$ResourceExists($bc_BasicCoin_Balance'#0'_$memory#8, $t6) || !$ResourceExists($bc_BasicCoin_Balance'#0'_$memory#8, $t1)) || ($t7 < $t2)) || (($t8 + $t2) > 18446744073709551615)) || $IsEqual'address'($t6, $t1));

    // abort($t10) at .\sources\BasicCoin.move:84:5+728
    $abort_code := $t10;
    $abort_flag := true;
    return;

}

// fun BasicCoin::withdraw<#0> [baseline] at .\sources\BasicCoin.move:102:5+369
procedure {:inline 1} $bc_BasicCoin_withdraw'#0'(_$t0: int, _$t1: int) returns ($ret0: $bc_BasicCoin_Coin'#0')
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: $Mutation (int);
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: bool;
    var $t9: $Mutation ($bc_BasicCoin_Balance'#0');
    var $t10: $Mutation ($bc_BasicCoin_Coin'#0');
    var $t11: $Mutation (int);
    var $t12: int;
    var $t13: $bc_BasicCoin_Coin'#0';
    var $t14: int;
    var $t0: int;
    var $t1: int;
    var $temp_0'$bc_BasicCoin_Coin'#0'': $bc_BasicCoin_Coin'#0';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // assume Identical($t5, select BasicCoin::Coin.value<0xbc::BasicCoin::Coin<#0>>(select BasicCoin::Balance.coin<0xbc::BasicCoin::Balance<#0>>(global<0xbc::BasicCoin::Balance<#0>>($t0)))) at .\sources\BasicCoin.move:111:9+57
    assume {:print "$at(2,4118,4175)"} true;
    assume ($t5 == $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $t0)->$coin->$value);

    // trace_local[addr]($t0) at .\sources\BasicCoin.move:102:5+1
    assume {:print "$at(2,3719,3720)"} true;
    assume {:print "$track_local(3,6,0):", $t0} $t0 == $t0;

    // trace_local[amount]($t1) at .\sources\BasicCoin.move:102:5+1
    assume {:print "$track_local(3,6,1):", $t1} $t1 == $t1;

    // $t6 := BasicCoin::balance_of<#0>($t0) on_abort goto L3 with $t7 at .\sources\BasicCoin.move:103:23+26
    assume {:print "$at(2,3828,3854)"} true;
    call $t6 := $bc_BasicCoin_balance_of'#0'($t0);
    if ($abort_flag) {
        assume {:print "$at(2,3828,3854)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(3,6):", $t7} $t7 == $t7;
        goto L3;
    }

    // trace_local[balance]($t6) at .\sources\BasicCoin.move:103:23+26
    assume {:print "$track_local(3,6,2):", $t6} $t6 == $t6;

    // $t8 := >=($t6, $t1) at .\sources\BasicCoin.move:104:17+17
    assume {:print "$at(2,3872,3889)"} true;
    call $t8 := $Ge($t6, $t1);

    // if ($t8) goto L1 else goto L0 at .\sources\BasicCoin.move:104:9+6
    if ($t8) { goto L1; } else { goto L0; }

    // label L1 at .\sources\BasicCoin.move:105:32+42
    assume {:print "$at(2,3946,3988)"} true;
L1:

    // $t9 := borrow_global<0xbc::BasicCoin::Balance<#0>>($t0) on_abort goto L3 with $t7 at .\sources\BasicCoin.move:105:32+42
    assume {:print "$at(2,3946,3988)"} true;
    if (!$ResourceExists($bc_BasicCoin_Balance'#0'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t9 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(2,3946,3988)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(3,6):", $t7} $t7 == $t7;
        goto L3;
    }

    // $t10 := borrow_field<0xbc::BasicCoin::Balance<#0>>.coin($t9) at .\sources\BasicCoin.move:105:32+47
    $t10 := $ChildMutation($t9, 0, $Dereference($t9)->$coin);

    // $t11 := borrow_field<0xbc::BasicCoin::Coin<#0>>.value($t10) at .\sources\BasicCoin.move:105:27+58
    $t11 := $ChildMutation($t10, 0, $Dereference($t10)->$value);

    // $t12 := -($t6, $t1) on_abort goto L3 with $t7 at .\sources\BasicCoin.move:106:24+16
    assume {:print "$at(2,4024,4040)"} true;
    call $t12 := $SubU64($t6, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,4024,4040)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(3,6):", $t7} $t7 == $t7;
        goto L3;
    }

    // trace_local[$t5]($t12) at .\sources\BasicCoin.move:106:9+31
    assume {:print "$track_local(3,6,3):", $t12} $t12 == $t12;

    // trace_local[balance_ref]($t11) at .\sources\BasicCoin.move:106:9+31
    $temp_0'u64' := $Dereference($t11);
    assume {:print "$track_local(3,6,4):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // write_ref($t11, $t12) at .\sources\BasicCoin.move:106:9+31
    $t11 := $UpdateMutation($t11, $t12);

    // write_back[Reference($t10).value (u64)]($t11) at .\sources\BasicCoin.move:106:9+31
    $t10 := $UpdateMutation($t10, $Update'$bc_BasicCoin_Coin'#0''_value($Dereference($t10), $Dereference($t11)));

    // write_back[Reference($t9).coin (0xbc::BasicCoin::Coin<#0>)]($t10) at .\sources\BasicCoin.move:106:9+31
    $t9 := $UpdateMutation($t9, $Update'$bc_BasicCoin_Balance'#0''_coin($Dereference($t9), $Dereference($t10)));

    // write_back[0xbc::BasicCoin::Balance<#0>@]($t9) at .\sources\BasicCoin.move:106:9+31
    $bc_BasicCoin_Balance'#0'_$memory := $ResourceUpdate($bc_BasicCoin_Balance'#0'_$memory, $GlobalLocationAddress($t9),
        $Dereference($t9));

    // $t13 := pack 0xbc::BasicCoin::Coin<#0>($t1) at .\sources\BasicCoin.move:107:9+32
    assume {:print "$at(2,4050,4082)"} true;
    $t13 := $bc_BasicCoin_Coin'#0'($t1);

    // trace_return[0]($t13) at .\sources\BasicCoin.move:102:90+284
    assume {:print "$at(2,3804,4088)"} true;
    assume {:print "$track_return(3,6,0):", $t13} $t13 == $t13;

    // goto L2 at .\sources\BasicCoin.move:102:90+284
    goto L2;

    // label L0 at .\sources\BasicCoin.move:104:36+21
    assume {:print "$at(2,3891,3912)"} true;
L0:

    // $t14 := 1 at .\sources\BasicCoin.move:104:36+21
    assume {:print "$at(2,3891,3912)"} true;
    $t14 := 1;
    assume $IsValid'u64'($t14);

    // trace_abort($t14) at .\sources\BasicCoin.move:104:9+6
    assume {:print "$at(2,3864,3870)"} true;
    assume {:print "$track_abort(3,6):", $t14} $t14 == $t14;

    // $t7 := move($t14) at .\sources\BasicCoin.move:104:9+6
    $t7 := $t14;

    // goto L3 at .\sources\BasicCoin.move:104:9+6
    goto L3;

    // label L2 at .\sources\BasicCoin.move:108:5+1
    assume {:print "$at(2,4087,4088)"} true;
L2:

    // return $t13 at .\sources\BasicCoin.move:108:5+1
    assume {:print "$at(2,4087,4088)"} true;
    $ret0 := $t13;
    return;

    // label L3 at .\sources\BasicCoin.move:108:5+1
L3:

    // abort($t7) at .\sources\BasicCoin.move:108:5+1
    assume {:print "$at(2,4087,4088)"} true;
    $abort_code := $t7;
    $abort_flag := true;
    return;

}

// fun BasicCoin::withdraw [verification] at .\sources\BasicCoin.move:102:5+369
procedure {:timeLimit 40} $bc_BasicCoin_withdraw$verify(_$t0: int, _$t1: int) returns ($ret0: $bc_BasicCoin_Coin'#0')
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: $Mutation (int);
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: bool;
    var $t9: $Mutation ($bc_BasicCoin_Balance'#0');
    var $t10: $Mutation ($bc_BasicCoin_Coin'#0');
    var $t11: $Mutation (int);
    var $t12: int;
    var $t13: $bc_BasicCoin_Coin'#0';
    var $t14: int;
    var $t15: int;
    var $t0: int;
    var $t1: int;
    var $temp_0'$bc_BasicCoin_Coin'#0'': $bc_BasicCoin_Coin'#0';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    var $bc_BasicCoin_Balance'#0'_$memory#2: $Memory $bc_BasicCoin_Balance'#0';
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at .\sources\BasicCoin.move:102:5+1
    assume {:print "$at(2,3719,3720)"} true;
    assume $IsValid'address'($t0);

    // assume WellFormed($t1) at .\sources\BasicCoin.move:102:5+1
    assume $IsValid'u64'($t1);

    // assume forall $rsc: 0xbc::BasicCoin::Balance<#0>: ResourceDomain<0xbc::BasicCoin::Balance<#0>>(): WellFormed($rsc) at .\sources\BasicCoin.move:102:5+1
    assume (forall $a_0: int :: {$ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $a_0)}(var $rsc := $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $a_0);
    ($IsValid'$bc_BasicCoin_Balance'#0''($rsc))));

    // assume Identical($t5, select BasicCoin::Coin.value<0xbc::BasicCoin::Coin<#0>>(select BasicCoin::Balance.coin<0xbc::BasicCoin::Balance<#0>>(global<0xbc::BasicCoin::Balance<#0>>($t0)))) at .\sources\BasicCoin.move:111:9+57
    assume {:print "$at(2,4118,4175)"} true;
    assume ($t5 == $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $t0)->$coin->$value);

    // @2 := save_mem(BasicCoin::Balance<#0>) at .\sources\BasicCoin.move:102:5+1
    assume {:print "$at(2,3719,3720)"} true;
    $bc_BasicCoin_Balance'#0'_$memory#2 := $bc_BasicCoin_Balance'#0'_$memory;

    // trace_local[addr]($t0) at .\sources\BasicCoin.move:102:5+1
    assume {:print "$track_local(3,6,0):", $t0} $t0 == $t0;

    // trace_local[amount]($t1) at .\sources\BasicCoin.move:102:5+1
    assume {:print "$track_local(3,6,1):", $t1} $t1 == $t1;

    // $t6 := BasicCoin::balance_of<#0>($t0) on_abort goto L3 with $t7 at .\sources\BasicCoin.move:103:23+26
    assume {:print "$at(2,3828,3854)"} true;
    call $t6 := $bc_BasicCoin_balance_of'#0'($t0);
    if ($abort_flag) {
        assume {:print "$at(2,3828,3854)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(3,6):", $t7} $t7 == $t7;
        goto L3;
    }

    // trace_local[balance]($t6) at .\sources\BasicCoin.move:103:23+26
    assume {:print "$track_local(3,6,2):", $t6} $t6 == $t6;

    // $t8 := >=($t6, $t1) at .\sources\BasicCoin.move:104:17+17
    assume {:print "$at(2,3872,3889)"} true;
    call $t8 := $Ge($t6, $t1);

    // if ($t8) goto L1 else goto L0 at .\sources\BasicCoin.move:104:9+6
    if ($t8) { goto L1; } else { goto L0; }

    // label L1 at .\sources\BasicCoin.move:105:32+42
    assume {:print "$at(2,3946,3988)"} true;
L1:

    // $t9 := borrow_global<0xbc::BasicCoin::Balance<#0>>($t0) on_abort goto L3 with $t7 at .\sources\BasicCoin.move:105:32+42
    assume {:print "$at(2,3946,3988)"} true;
    if (!$ResourceExists($bc_BasicCoin_Balance'#0'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t9 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(2,3946,3988)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(3,6):", $t7} $t7 == $t7;
        goto L3;
    }

    // $t10 := borrow_field<0xbc::BasicCoin::Balance<#0>>.coin($t9) at .\sources\BasicCoin.move:105:32+47
    $t10 := $ChildMutation($t9, 0, $Dereference($t9)->$coin);

    // $t11 := borrow_field<0xbc::BasicCoin::Coin<#0>>.value($t10) at .\sources\BasicCoin.move:105:27+58
    $t11 := $ChildMutation($t10, 0, $Dereference($t10)->$value);

    // $t12 := -($t6, $t1) on_abort goto L3 with $t7 at .\sources\BasicCoin.move:106:24+16
    assume {:print "$at(2,4024,4040)"} true;
    call $t12 := $SubU64($t6, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,4024,4040)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(3,6):", $t7} $t7 == $t7;
        goto L3;
    }

    // trace_local[$t5]($t12) at .\sources\BasicCoin.move:106:9+31
    assume {:print "$track_local(3,6,3):", $t12} $t12 == $t12;

    // trace_local[balance_ref]($t11) at .\sources\BasicCoin.move:106:9+31
    $temp_0'u64' := $Dereference($t11);
    assume {:print "$track_local(3,6,4):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // write_ref($t11, $t12) at .\sources\BasicCoin.move:106:9+31
    $t11 := $UpdateMutation($t11, $t12);

    // write_back[Reference($t10).value (u64)]($t11) at .\sources\BasicCoin.move:106:9+31
    $t10 := $UpdateMutation($t10, $Update'$bc_BasicCoin_Coin'#0''_value($Dereference($t10), $Dereference($t11)));

    // write_back[Reference($t9).coin (0xbc::BasicCoin::Coin<#0>)]($t10) at .\sources\BasicCoin.move:106:9+31
    $t9 := $UpdateMutation($t9, $Update'$bc_BasicCoin_Balance'#0''_coin($Dereference($t9), $Dereference($t10)));

    // write_back[0xbc::BasicCoin::Balance<#0>@]($t9) at .\sources\BasicCoin.move:106:9+31
    $bc_BasicCoin_Balance'#0'_$memory := $ResourceUpdate($bc_BasicCoin_Balance'#0'_$memory, $GlobalLocationAddress($t9),
        $Dereference($t9));

    // $t13 := pack 0xbc::BasicCoin::Coin<#0>($t1) at .\sources\BasicCoin.move:107:9+32
    assume {:print "$at(2,4050,4082)"} true;
    $t13 := $bc_BasicCoin_Coin'#0'($t1);

    // trace_return[0]($t13) at .\sources\BasicCoin.move:102:90+284
    assume {:print "$at(2,3804,4088)"} true;
    assume {:print "$track_return(3,6,0):", $t13} $t13 == $t13;

    // goto L2 at .\sources\BasicCoin.move:102:90+284
    goto L2;

    // label L0 at .\sources\BasicCoin.move:104:36+21
    assume {:print "$at(2,3891,3912)"} true;
L0:

    // $t14 := 1 at .\sources\BasicCoin.move:104:36+21
    assume {:print "$at(2,3891,3912)"} true;
    $t14 := 1;
    assume $IsValid'u64'($t14);

    // trace_abort($t14) at .\sources\BasicCoin.move:104:9+6
    assume {:print "$at(2,3864,3870)"} true;
    assume {:print "$track_abort(3,6):", $t14} $t14 == $t14;

    // $t7 := move($t14) at .\sources\BasicCoin.move:104:9+6
    $t7 := $t14;

    // goto L3 at .\sources\BasicCoin.move:104:9+6
    goto L3;

    // label L2 at .\sources\BasicCoin.move:108:5+1
    assume {:print "$at(2,4087,4088)"} true;
L2:

    // assume Identical($t15, select BasicCoin::Coin.value<0xbc::BasicCoin::Coin<#0>>(select BasicCoin::Balance.coin<0xbc::BasicCoin::Balance<#0>>(global<0xbc::BasicCoin::Balance<#0>>($t0)))) at .\sources\BasicCoin.move:116:9+67
    assume {:print "$at(2,4274,4341)"} true;
    assume ($t15 == $ResourceValue($bc_BasicCoin_Balance'#0'_$memory, $t0)->$coin->$value);

    // assert Not(Not(exists[@2]<0xbc::BasicCoin::Balance<#0>>($t0))) at .\sources\BasicCoin.move:113:9+43
    assume {:print "$at(2,4185,4228)"} true;
    assert {:msg "assert_failed(2,4185,4228): function does not abort under this condition"}
      !!$ResourceExists($bc_BasicCoin_Balance'#0'_$memory#2, $t0);

    // assert Not(Lt($t5, $t1)) at .\sources\BasicCoin.move:114:9+27
    assume {:print "$at(2,4237,4264)"} true;
    assert {:msg "assert_failed(2,4237,4264): function does not abort under this condition"}
      !($t5 < $t1);

    // assert Eq<0xbc::BasicCoin::Coin<#0>>($t13, pack BasicCoin::Coin<#0>($t1)) at .\sources\BasicCoin.move:117:9+51
    assume {:print "$at(2,4350,4401)"} true;
    assert {:msg "assert_failed(2,4350,4401): post-condition does not hold"}
      $IsEqual'$bc_BasicCoin_Coin'#0''($t13, $bc_BasicCoin_Coin'#0'($t1));

    // assert Eq<u64>($t15, Sub($t5, $t1)) at .\sources\BasicCoin.move:118:9+41
    assume {:print "$at(2,4410,4451)"} true;
    assert {:msg "assert_failed(2,4410,4451): post-condition does not hold"}
      $IsEqual'u64'($t15, ($t5 - $t1));

    // return $t13 at .\sources\BasicCoin.move:118:9+41
    $ret0 := $t13;
    return;

    // label L3 at .\sources\BasicCoin.move:108:5+1
    assume {:print "$at(2,4087,4088)"} true;
L3:

    // assert Or(Not(exists[@2]<0xbc::BasicCoin::Balance<#0>>($t0)), Lt($t5, $t1)) at .\sources\BasicCoin.move:110:5+363
    assume {:print "$at(2,4094,4457)"} true;
    assert {:msg "assert_failed(2,4094,4457): abort not covered by any of the `aborts_if` clauses"}
      (!$ResourceExists($bc_BasicCoin_Balance'#0'_$memory#2, $t0) || ($t5 < $t1));

    // abort($t7) at .\sources\BasicCoin.move:110:5+363
    $abort_code := $t7;
    $abort_flag := true;
    return;

}

// struct ProphecyBenchmark::Node at .\sources\ConditionalBorrowChain.move:4:5+51
datatype $bc_ProphecyBenchmark_Node {
    $bc_ProphecyBenchmark_Node($v0: int)
}
function {:inline} $Update'$bc_ProphecyBenchmark_Node'_v0(s: $bc_ProphecyBenchmark_Node, x: int): $bc_ProphecyBenchmark_Node {
    $bc_ProphecyBenchmark_Node(x)
}
function $IsValid'$bc_ProphecyBenchmark_Node'(s: $bc_ProphecyBenchmark_Node): bool {
    $IsValid'u64'(s->$v0)
}
function {:inline} $IsEqual'$bc_ProphecyBenchmark_Node'(s1: $bc_ProphecyBenchmark_Node, s2: $bc_ProphecyBenchmark_Node): bool {
    s1 == s2
}

// fun ProphecyBenchmark::new_node [verification] at .\sources\ConditionalBorrowChain.move:9:5+58
procedure {:timeLimit 40} $bc_ProphecyBenchmark_new_node$verify() returns ($ret0: $bc_ProphecyBenchmark_Node)
{
    // declare local variables
    var $t0: int;
    var $t1: $bc_ProphecyBenchmark_Node;
    var $temp_0'$bc_ProphecyBenchmark_Node': $bc_ProphecyBenchmark_Node;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // $t0 := 0 at .\sources\ConditionalBorrowChain.move:10:20+1
    assume {:print "$at(3,252,253)"} true;
    $t0 := 0;
    assume $IsValid'u64'($t0);

    // $t1 := pack 0xbc::ProphecyBenchmark::Node($t0) at .\sources\ConditionalBorrowChain.move:10:9+14
    $t1 := $bc_ProphecyBenchmark_Node($t0);

    // trace_return[0]($t1) at .\sources\ConditionalBorrowChain.move:10:9+14
    assume {:print "$track_return(4,0,0):", $t1} $t1 == $t1;

    // label L1 at .\sources\ConditionalBorrowChain.move:11:5+1
    assume {:print "$at(3,260,261)"} true;
L1:

    // return $t1 at .\sources\ConditionalBorrowChain.move:11:5+1
    assume {:print "$at(3,260,261)"} true;
    $ret0 := $t1;
    return;

}

// fun ProphecyBenchmark::stress_test_10 [verification] at .\sources\ConditionalBorrowChain.move:42:5+439
procedure {:timeLimit 40} $bc_ProphecyBenchmark_stress_test_10$verify(_$t0: $bc_ProphecyBenchmark_Node, _$t1: int, _$t2: int, _$t3: int, _$t4: int, _$t5: int, _$t6: int, _$t7: int, _$t8: int, _$t9: int, _$t10: int) returns ($ret0: $bc_ProphecyBenchmark_Node)
{
    // declare local variables
    var $t11: $bc_ProphecyBenchmark_Node;
    var $t12: int;
    var $t13: $bc_ProphecyBenchmark_Node;
    var $t14: $bc_ProphecyBenchmark_Node;
    var $t15: $bc_ProphecyBenchmark_Node;
    var $t16: $bc_ProphecyBenchmark_Node;
    var $t17: $bc_ProphecyBenchmark_Node;
    var $t18: $bc_ProphecyBenchmark_Node;
    var $t0: $bc_ProphecyBenchmark_Node;
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: int;
    var $t10: int;
    var $temp_0'$bc_ProphecyBenchmark_Node': $bc_ProphecyBenchmark_Node;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;
    $t3 := _$t3;
    $t4 := _$t4;
    $t5 := _$t5;
    $t6 := _$t6;
    $t7 := _$t7;
    $t8 := _$t8;
    $t9 := _$t9;
    $t10 := _$t10;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at .\sources\ConditionalBorrowChain.move:42:5+1
    assume {:print "$at(3,1484,1485)"} true;
    assume $IsValid'$bc_ProphecyBenchmark_Node'($t0);

    // assume WellFormed($t1) at .\sources\ConditionalBorrowChain.move:42:5+1
    assume $IsValid'u64'($t1);

    // assume WellFormed($t2) at .\sources\ConditionalBorrowChain.move:42:5+1
    assume $IsValid'u64'($t2);

    // assume WellFormed($t3) at .\sources\ConditionalBorrowChain.move:42:5+1
    assume $IsValid'u64'($t3);

    // assume WellFormed($t4) at .\sources\ConditionalBorrowChain.move:42:5+1
    assume $IsValid'u64'($t4);

    // assume WellFormed($t5) at .\sources\ConditionalBorrowChain.move:42:5+1
    assume $IsValid'u64'($t5);

    // assume WellFormed($t6) at .\sources\ConditionalBorrowChain.move:42:5+1
    assume $IsValid'u64'($t6);

    // assume WellFormed($t7) at .\sources\ConditionalBorrowChain.move:42:5+1
    assume $IsValid'u64'($t7);

    // assume WellFormed($t8) at .\sources\ConditionalBorrowChain.move:42:5+1
    assume $IsValid'u64'($t8);

    // assume WellFormed($t9) at .\sources\ConditionalBorrowChain.move:42:5+1
    assume $IsValid'u64'($t9);

    // assume WellFormed($t10) at .\sources\ConditionalBorrowChain.move:42:5+1
    assume $IsValid'u64'($t10);

    // assume Eq<u64>(select ProphecyBenchmark::Node.v0<0xbc::ProphecyBenchmark::Node>($t0), 0) at .\sources\ConditionalBorrowChain.move:59:6+19
    assume {:print "$at(3,2020,2039)"} true;
    assume $IsEqual'u64'($t0->$v0, 0);

    // trace_local[n]($t0) at .\sources\ConditionalBorrowChain.move:42:5+1
    assume {:print "$at(3,1484,1485)"} true;
    assume {:print "$track_local(4,1,0):", $t0} $t0 == $t0;

    // trace_local[c0]($t1) at .\sources\ConditionalBorrowChain.move:42:5+1
    assume {:print "$track_local(4,1,1):", $t1} $t1 == $t1;

    // trace_local[c1]($t2) at .\sources\ConditionalBorrowChain.move:42:5+1
    assume {:print "$track_local(4,1,2):", $t2} $t2 == $t2;

    // trace_local[c2]($t3) at .\sources\ConditionalBorrowChain.move:42:5+1
    assume {:print "$track_local(4,1,3):", $t3} $t3 == $t3;

    // trace_local[c3]($t4) at .\sources\ConditionalBorrowChain.move:42:5+1
    assume {:print "$track_local(4,1,4):", $t4} $t4 == $t4;

    // trace_local[c4]($t5) at .\sources\ConditionalBorrowChain.move:42:5+1
    assume {:print "$track_local(4,1,5):", $t5} $t5 == $t5;

    // trace_local[c5]($t6) at .\sources\ConditionalBorrowChain.move:42:5+1
    assume {:print "$track_local(4,1,6):", $t6} $t6 == $t6;

    // trace_local[c6]($t7) at .\sources\ConditionalBorrowChain.move:42:5+1
    assume {:print "$track_local(4,1,7):", $t7} $t7 == $t7;

    // trace_local[c7]($t8) at .\sources\ConditionalBorrowChain.move:42:5+1
    assume {:print "$track_local(4,1,8):", $t8} $t8 == $t8;

    // trace_local[c8]($t9) at .\sources\ConditionalBorrowChain.move:42:5+1
    assume {:print "$track_local(4,1,9):", $t9} $t9 == $t9;

    // trace_local[c9]($t10) at .\sources\ConditionalBorrowChain.move:42:5+1
    assume {:print "$track_local(4,1,10):", $t10} $t10 == $t10;

    // assert Le(select ProphecyBenchmark::Node.v0<0xbc::ProphecyBenchmark::Node>($t0), 100) at .\sources\ConditionalBorrowChain.move:28:6+24
    assume {:print "$at(3,830,854)"} true;
    assert {:msg "assert_failed(3,830,854): precondition does not hold at this call"}
      ($t0->$v0 <= 100);

    // $t11 := ProphecyBenchmark::update_one($t0, $t1) on_abort goto L2 with $t12 at .\sources\ConditionalBorrowChain.move:47:18+17
    assume {:print "$at(3,1666,1683)"} true;
    call $t11 := $bc_ProphecyBenchmark_update_one($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(3,1666,1683)"} true;
        $t12 := $abort_code;
        assume {:print "$track_abort(4,1):", $t12} $t12 == $t12;
        goto L2;
    }

    // assert Le(select ProphecyBenchmark::Node.v0<0xbc::ProphecyBenchmark::Node>($t11), 100) at .\sources\ConditionalBorrowChain.move:28:6+24
    assume {:print "$at(3,830,854)"} true;
    assert {:msg "assert_failed(3,830,854): precondition does not hold at this call"}
      ($t11->$v0 <= 100);

    // $t13 := ProphecyBenchmark::update_one($t11, $t2) on_abort goto L2 with $t12 at .\sources\ConditionalBorrowChain.move:48:18+18
    assume {:print "$at(3,1702,1720)"} true;
    call $t13 := $bc_ProphecyBenchmark_update_one($t11, $t2);
    if ($abort_flag) {
        assume {:print "$at(3,1702,1720)"} true;
        $t12 := $abort_code;
        assume {:print "$track_abort(4,1):", $t12} $t12 == $t12;
        goto L2;
    }

    // assert Le(select ProphecyBenchmark::Node.v0<0xbc::ProphecyBenchmark::Node>($t13), 100) at .\sources\ConditionalBorrowChain.move:28:6+24
    assume {:print "$at(3,830,854)"} true;
    assert {:msg "assert_failed(3,830,854): precondition does not hold at this call"}
      ($t13->$v0 <= 100);

    // $t14 := ProphecyBenchmark::update_one($t13, $t3) on_abort goto L2 with $t12 at .\sources\ConditionalBorrowChain.move:49:18+18
    assume {:print "$at(3,1739,1757)"} true;
    call $t14 := $bc_ProphecyBenchmark_update_one($t13, $t3);
    if ($abort_flag) {
        assume {:print "$at(3,1739,1757)"} true;
        $t12 := $abort_code;
        assume {:print "$track_abort(4,1):", $t12} $t12 == $t12;
        goto L2;
    }

    // assert Le(select ProphecyBenchmark::Node.v0<0xbc::ProphecyBenchmark::Node>($t14), 100) at .\sources\ConditionalBorrowChain.move:28:6+24
    assume {:print "$at(3,830,854)"} true;
    assert {:msg "assert_failed(3,830,854): precondition does not hold at this call"}
      ($t14->$v0 <= 100);

    // $t15 := ProphecyBenchmark::update_one($t14, $t4) on_abort goto L2 with $t12 at .\sources\ConditionalBorrowChain.move:50:18+18
    assume {:print "$at(3,1776,1794)"} true;
    call $t15 := $bc_ProphecyBenchmark_update_one($t14, $t4);
    if ($abort_flag) {
        assume {:print "$at(3,1776,1794)"} true;
        $t12 := $abort_code;
        assume {:print "$track_abort(4,1):", $t12} $t12 == $t12;
        goto L2;
    }

    // assert Le(select ProphecyBenchmark::Node.v0<0xbc::ProphecyBenchmark::Node>($t15), 100) at .\sources\ConditionalBorrowChain.move:28:6+24
    assume {:print "$at(3,830,854)"} true;
    assert {:msg "assert_failed(3,830,854): precondition does not hold at this call"}
      ($t15->$v0 <= 100);

    // $t16 := ProphecyBenchmark::update_one($t15, $t5) on_abort goto L2 with $t12 at .\sources\ConditionalBorrowChain.move:51:18+18
    assume {:print "$at(3,1813,1831)"} true;
    call $t16 := $bc_ProphecyBenchmark_update_one($t15, $t5);
    if ($abort_flag) {
        assume {:print "$at(3,1813,1831)"} true;
        $t12 := $abort_code;
        assume {:print "$track_abort(4,1):", $t12} $t12 == $t12;
        goto L2;
    }

    // assert Le(select ProphecyBenchmark::Node.v0<0xbc::ProphecyBenchmark::Node>($t16), 100) at .\sources\ConditionalBorrowChain.move:28:6+24
    assume {:print "$at(3,830,854)"} true;
    assert {:msg "assert_failed(3,830,854): precondition does not hold at this call"}
      ($t16->$v0 <= 100);

    // $t17 := ProphecyBenchmark::update_one($t16, $t6) on_abort goto L2 with $t12 at .\sources\ConditionalBorrowChain.move:52:18+18
    assume {:print "$at(3,1850,1868)"} true;
    call $t17 := $bc_ProphecyBenchmark_update_one($t16, $t6);
    if ($abort_flag) {
        assume {:print "$at(3,1850,1868)"} true;
        $t12 := $abort_code;
        assume {:print "$track_abort(4,1):", $t12} $t12 == $t12;
        goto L2;
    }

    // assert Le(select ProphecyBenchmark::Node.v0<0xbc::ProphecyBenchmark::Node>($t17), 100) at .\sources\ConditionalBorrowChain.move:28:6+24
    assume {:print "$at(3,830,854)"} true;
    assert {:msg "assert_failed(3,830,854): precondition does not hold at this call"}
      ($t17->$v0 <= 100);

    // $t18 := ProphecyBenchmark::update_one($t17, $t7) on_abort goto L2 with $t12 at .\sources\ConditionalBorrowChain.move:53:18+18
    assume {:print "$at(3,1887,1905)"} true;
    call $t18 := $bc_ProphecyBenchmark_update_one($t17, $t7);
    if ($abort_flag) {
        assume {:print "$at(3,1887,1905)"} true;
        $t12 := $abort_code;
        assume {:print "$track_abort(4,1):", $t12} $t12 == $t12;
        goto L2;
    }

    // trace_return[0]($t18) at .\sources\ConditionalBorrowChain.move:54:9+2
    assume {:print "$at(3,1915,1917)"} true;
    assume {:print "$track_return(4,1,0):", $t18} $t18 == $t18;

    // label L1 at .\sources\ConditionalBorrowChain.move:55:5+1
    assume {:print "$at(3,1922,1923)"} true;
L1:

    // assert Le(select ProphecyBenchmark::Node.v0<0xbc::ProphecyBenchmark::Node>($t18), 10) at .\sources\ConditionalBorrowChain.move:62:9+24
    assume {:print "$at(3,2151,2175)"} true;
    assert {:msg "assert_failed(3,2151,2175): post-condition does not hold"}
      ($t18->$v0 <= 10);

    // return $t18 at .\sources\ConditionalBorrowChain.move:62:9+24
    $ret0 := $t18;
    return;

    // label L2 at .\sources\ConditionalBorrowChain.move:55:5+1
    assume {:print "$at(3,1922,1923)"} true;
L2:

    // abort($t12) at .\sources\ConditionalBorrowChain.move:55:5+1
    assume {:print "$at(3,1922,1923)"} true;
    $abort_code := $t12;
    $abort_flag := true;
    return;

}

// fun ProphecyBenchmark::update_one [baseline] at .\sources\ConditionalBorrowChain.move:14:5+412
procedure {:inline 1} $bc_ProphecyBenchmark_update_one(_$t0: $bc_ProphecyBenchmark_Node, _$t1: int) returns ($ret0: $bc_ProphecyBenchmark_Node)
{
    // declare local variables
    var $t2: $Mutation (int);
    var $t3: $Mutation ($bc_ProphecyBenchmark_Node);
    var $t4: $Mutation (int);
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: $bc_ProphecyBenchmark_Node;
    var $t0: $bc_ProphecyBenchmark_Node;
    var $t1: int;
    var $temp_0'$bc_ProphecyBenchmark_Node': $bc_ProphecyBenchmark_Node;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // assume Le(select ProphecyBenchmark::Node.v0<0xbc::ProphecyBenchmark::Node>($t0), 100) at .\sources\ConditionalBorrowChain.move:28:6+24
    assume {:print "$at(3,830,854)"} true;
    assume ($t0->$v0 <= 100);

    // trace_local[node]($t0) at .\sources\ConditionalBorrowChain.move:14:5+1
    assume {:print "$at(3,343,344)"} true;
    assume {:print "$track_local(4,2,0):", $t0} $t0 == $t0;

    // trace_local[choice]($t1) at .\sources\ConditionalBorrowChain.move:14:5+1
    assume {:print "$track_local(4,2,1):", $t1} $t1 == $t1;

    // $t3 := borrow_local($t0) at .\sources\ConditionalBorrowChain.move:16:21+9
    assume {:print "$at(3,486,495)"} true;
    $t3 := $Mutation($Local(0), EmptyVec(), $t0);

    // $t4 := borrow_field<0xbc::ProphecyBenchmark::Node>.v0($t3) at .\sources\ConditionalBorrowChain.move:19:22+13
    assume {:print "$at(3,629,642)"} true;
    $t4 := $ChildMutation($t3, 0, $Dereference($t3)->$v0);

    // trace_local[target]($t4) at .\sources\ConditionalBorrowChain.move:19:22+13
    $temp_0'u64' := $Dereference($t4);
    assume {:print "$track_local(4,2,2):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t5 := read_ref($t4) at .\sources\ConditionalBorrowChain.move:21:19+7
    assume {:print "$at(3,686,693)"} true;
    $t5 := $Dereference($t4);

    // $t6 := 1 at .\sources\ConditionalBorrowChain.move:21:29+1
    $t6 := 1;
    assume $IsValid'u64'($t6);

    // $t7 := +($t5, $t6) on_abort goto L2 with $t8 at .\sources\ConditionalBorrowChain.move:21:19+11
    call $t7 := $AddU64($t5, $t6);
    if ($abort_flag) {
        assume {:print "$at(3,686,697)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(4,2):", $t8} $t8 == $t8;
        goto L2;
    }

    // write_ref($t4, $t7) at .\sources\ConditionalBorrowChain.move:21:9+21
    $t4 := $UpdateMutation($t4, $t7);

    // write_back[Reference($t3).v0 (u64)]($t4) at .\sources\ConditionalBorrowChain.move:21:9+21
    $t3 := $UpdateMutation($t3, $Update'$bc_ProphecyBenchmark_Node'_v0($Dereference($t3), $Dereference($t4)));

    // write_back[LocalRoot($t0)@]($t3) at .\sources\ConditionalBorrowChain.move:21:9+21
    $t0 := $Dereference($t3);

    // trace_local[node]($t0) at .\sources\ConditionalBorrowChain.move:21:9+21
    assume {:print "$track_local(4,2,0):", $t0} $t0 == $t0;

    // $t9 := move($t0) at .\sources\ConditionalBorrowChain.move:23:9+4
    assume {:print "$at(3,745,749)"} true;
    $t9 := $t0;

    // trace_return[0]($t9) at .\sources\ConditionalBorrowChain.move:14:58+359
    assume {:print "$at(3,396,755)"} true;
    assume {:print "$track_return(4,2,0):", $t9} $t9 == $t9;

    // label L1 at .\sources\ConditionalBorrowChain.move:24:5+1
    assume {:print "$at(3,754,755)"} true;
L1:

    // return $t9 at .\sources\ConditionalBorrowChain.move:24:5+1
    assume {:print "$at(3,754,755)"} true;
    $ret0 := $t9;
    return;

    // label L2 at .\sources\ConditionalBorrowChain.move:24:5+1
L2:

    // abort($t8) at .\sources\ConditionalBorrowChain.move:24:5+1
    assume {:print "$at(3,754,755)"} true;
    $abort_code := $t8;
    $abort_flag := true;
    return;

}

// fun ProphecyBenchmark::update_one [verification] at .\sources\ConditionalBorrowChain.move:14:5+412
procedure {:timeLimit 40} $bc_ProphecyBenchmark_update_one$verify(_$t0: $bc_ProphecyBenchmark_Node, _$t1: int) returns ($ret0: $bc_ProphecyBenchmark_Node)
{
    // declare local variables
    var $t2: $Mutation (int);
    var $t3: $bc_ProphecyBenchmark_Node;
    var $t4: $Mutation ($bc_ProphecyBenchmark_Node);
    var $t5: $Mutation (int);
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: int;
    var $t10: $bc_ProphecyBenchmark_Node;
    var $t0: $bc_ProphecyBenchmark_Node;
    var $t1: int;
    var $temp_0'$bc_ProphecyBenchmark_Node': $bc_ProphecyBenchmark_Node;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at .\sources\ConditionalBorrowChain.move:14:5+1
    assume {:print "$at(3,343,344)"} true;
    assume $IsValid'$bc_ProphecyBenchmark_Node'($t0);

    // assume WellFormed($t1) at .\sources\ConditionalBorrowChain.move:14:5+1
    assume $IsValid'u64'($t1);

    // assume Le(select ProphecyBenchmark::Node.v0<0xbc::ProphecyBenchmark::Node>($t0), 100) at .\sources\ConditionalBorrowChain.move:28:6+24
    assume {:print "$at(3,830,854)"} true;
    assume ($t0->$v0 <= 100);

    // $t3 := copy($t0) at .\sources\ConditionalBorrowChain.move:28:6+24
    $t3 := $t0;

    // trace_local[node]($t0) at .\sources\ConditionalBorrowChain.move:14:5+1
    assume {:print "$at(3,343,344)"} true;
    assume {:print "$track_local(4,2,0):", $t0} $t0 == $t0;

    // trace_local[choice]($t1) at .\sources\ConditionalBorrowChain.move:14:5+1
    assume {:print "$track_local(4,2,1):", $t1} $t1 == $t1;

    // $t4 := borrow_local($t0) at .\sources\ConditionalBorrowChain.move:16:21+9
    assume {:print "$at(3,486,495)"} true;
    $t4 := $Mutation($Local(0), EmptyVec(), $t0);

    // $t5 := borrow_field<0xbc::ProphecyBenchmark::Node>.v0($t4) at .\sources\ConditionalBorrowChain.move:19:22+13
    assume {:print "$at(3,629,642)"} true;
    $t5 := $ChildMutation($t4, 0, $Dereference($t4)->$v0);

    // trace_local[target]($t5) at .\sources\ConditionalBorrowChain.move:19:22+13
    $temp_0'u64' := $Dereference($t5);
    assume {:print "$track_local(4,2,2):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t6 := read_ref($t5) at .\sources\ConditionalBorrowChain.move:21:19+7
    assume {:print "$at(3,686,693)"} true;
    $t6 := $Dereference($t5);

    // $t7 := 1 at .\sources\ConditionalBorrowChain.move:21:29+1
    $t7 := 1;
    assume $IsValid'u64'($t7);

    // $t8 := +($t6, $t7) on_abort goto L2 with $t9 at .\sources\ConditionalBorrowChain.move:21:19+11
    call $t8 := $AddU64($t6, $t7);
    if ($abort_flag) {
        assume {:print "$at(3,686,697)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(4,2):", $t9} $t9 == $t9;
        goto L2;
    }

    // write_ref($t5, $t8) at .\sources\ConditionalBorrowChain.move:21:9+21
    $t5 := $UpdateMutation($t5, $t8);

    // write_back[Reference($t4).v0 (u64)]($t5) at .\sources\ConditionalBorrowChain.move:21:9+21
    $t4 := $UpdateMutation($t4, $Update'$bc_ProphecyBenchmark_Node'_v0($Dereference($t4), $Dereference($t5)));

    // write_back[LocalRoot($t0)@]($t4) at .\sources\ConditionalBorrowChain.move:21:9+21
    $t0 := $Dereference($t4);

    // trace_local[node]($t0) at .\sources\ConditionalBorrowChain.move:21:9+21
    assume {:print "$track_local(4,2,0):", $t0} $t0 == $t0;

    // $t10 := move($t0) at .\sources\ConditionalBorrowChain.move:23:9+4
    assume {:print "$at(3,745,749)"} true;
    $t10 := $t0;

    // trace_return[0]($t10) at .\sources\ConditionalBorrowChain.move:14:58+359
    assume {:print "$at(3,396,755)"} true;
    assume {:print "$track_return(4,2,0):", $t10} $t10 == $t10;

    // label L1 at .\sources\ConditionalBorrowChain.move:24:5+1
    assume {:print "$at(3,754,755)"} true;
L1:

    // assert Not(false) at .\sources\ConditionalBorrowChain.move:38:9+16
    assume {:print "$at(3,1397,1413)"} true;
    assert {:msg "assert_failed(3,1397,1413): function does not abort under this condition"}
      !false;

    // assert Implies(Eq<u64>($t1, 0), Eq<u64>(select ProphecyBenchmark::Node.v0<0xbc::ProphecyBenchmark::Node>($t10), Add(select ProphecyBenchmark::Node.v0<0xbc::ProphecyBenchmark::Node>($t3), 1))) at .\sources\ConditionalBorrowChain.move:32:9+49
    assume {:print "$at(3,1026,1075)"} true;
    assert {:msg "assert_failed(3,1026,1075): post-condition does not hold"}
      ($IsEqual'u64'($t1, 0) ==> $IsEqual'u64'($t10->$v0, ($t3->$v0 + 1)));

    // assert Implies(Neq<u64>($t1, 0), Eq<u64>(select ProphecyBenchmark::Node.v0<0xbc::ProphecyBenchmark::Node>($t10), select ProphecyBenchmark::Node.v0<0xbc::ProphecyBenchmark::Node>($t10))) at .\sources\ConditionalBorrowChain.move:33:9+47
    assume {:print "$at(3,1084,1131)"} true;
    assert {:msg "assert_failed(3,1084,1131): post-condition does not hold"}
      (!$IsEqual'u64'($t1, 0) ==> $IsEqual'u64'($t10->$v0, $t10->$v0));

    // return $t10 at .\sources\ConditionalBorrowChain.move:33:9+47
    $ret0 := $t10;
    return;

    // label L2 at .\sources\ConditionalBorrowChain.move:24:5+1
    assume {:print "$at(3,754,755)"} true;
L2:

    // assert false at .\sources\ConditionalBorrowChain.move:26:5+659
    assume {:print "$at(3,761,1420)"} true;
    assert {:msg "assert_failed(3,761,1420): abort not covered by any of the `aborts_if` clauses"}
      false;

    // abort($t9) at .\sources\ConditionalBorrowChain.move:26:5+659
    $abort_code := $t9;
    $abort_flag := true;
    return;

}
