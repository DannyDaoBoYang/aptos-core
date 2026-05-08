(set-option :print-success false)
(set-info :smt-lib-version 2.6)
(set-option :produce-models true)
(set-option :model_validate true)
(set-option :smt.QI.EAGER_THRESHOLD 100)
(set-option :smt.QI.LAZY_THRESHOLD 100)
(set-option :smt.random_seed 1)
(set-option :smt.mbqi false)
(set-option :model.compact false)
(set-option :model.v2 true)
(set-option :pp.bv_literals false)
; done setting options


(declare-fun tickleBool (Bool) Bool)
(assert (and (tickleBool true) (tickleBool false)))
(declare-sort |T@[Int]Int| 0)
(declare-sort T@T_11045 0)
(declare-sort T@T2_11239 0)
(declare-datatypes ((T@$bc_ProphecyBenchmark3Levels5Fields_Node1 0)) ((($bc_ProphecyBenchmark3Levels5Fields_Node1 (|$v0#$bc_ProphecyBenchmark3Levels5Fields_Node1| Int) (|$v1#$bc_ProphecyBenchmark3Levels5Fields_Node1| Int) (|$v2#$bc_ProphecyBenchmark3Levels5Fields_Node1| Int) (|$v3#$bc_ProphecyBenchmark3Levels5Fields_Node1| Int) (|$v4#$bc_ProphecyBenchmark3Levels5Fields_Node1| Int) (|$v5#$bc_ProphecyBenchmark3Levels5Fields_Node1| Int) (|$v6#$bc_ProphecyBenchmark3Levels5Fields_Node1| Int) (|$v7#$bc_ProphecyBenchmark3Levels5Fields_Node1| Int) ) ) ))
(declare-datatypes ((T@$bc_ProphecyBenchmark3Levels5Fields_Node2 0)) ((($bc_ProphecyBenchmark3Levels5Fields_Node2 (|$v0#$bc_ProphecyBenchmark3Levels5Fields_Node2| T@$bc_ProphecyBenchmark3Levels5Fields_Node1) (|$v1#$bc_ProphecyBenchmark3Levels5Fields_Node2| T@$bc_ProphecyBenchmark3Levels5Fields_Node1) (|$v2#$bc_ProphecyBenchmark3Levels5Fields_Node2| T@$bc_ProphecyBenchmark3Levels5Fields_Node1) (|$v3#$bc_ProphecyBenchmark3Levels5Fields_Node2| T@$bc_ProphecyBenchmark3Levels5Fields_Node1) (|$v4#$bc_ProphecyBenchmark3Levels5Fields_Node2| T@$bc_ProphecyBenchmark3Levels5Fields_Node1) (|$v5#$bc_ProphecyBenchmark3Levels5Fields_Node2| T@$bc_ProphecyBenchmark3Levels5Fields_Node1) (|$v6#$bc_ProphecyBenchmark3Levels5Fields_Node2| T@$bc_ProphecyBenchmark3Levels5Fields_Node1) (|$v7#$bc_ProphecyBenchmark3Levels5Fields_Node2| T@$bc_ProphecyBenchmark3Levels5Fields_Node1) ) ) ))
(declare-datatypes ((T@$bc_ProphecyBenchmark3Levels5Fields_Node3 0)) ((($bc_ProphecyBenchmark3Levels5Fields_Node3 (|$v0#$bc_ProphecyBenchmark3Levels5Fields_Node3| T@$bc_ProphecyBenchmark3Levels5Fields_Node2) (|$v1#$bc_ProphecyBenchmark3Levels5Fields_Node3| T@$bc_ProphecyBenchmark3Levels5Fields_Node2) (|$v2#$bc_ProphecyBenchmark3Levels5Fields_Node3| T@$bc_ProphecyBenchmark3Levels5Fields_Node2) (|$v3#$bc_ProphecyBenchmark3Levels5Fields_Node3| T@$bc_ProphecyBenchmark3Levels5Fields_Node2) (|$v4#$bc_ProphecyBenchmark3Levels5Fields_Node3| T@$bc_ProphecyBenchmark3Levels5Fields_Node2) (|$v5#$bc_ProphecyBenchmark3Levels5Fields_Node3| T@$bc_ProphecyBenchmark3Levels5Fields_Node2) (|$v6#$bc_ProphecyBenchmark3Levels5Fields_Node3| T@$bc_ProphecyBenchmark3Levels5Fields_Node2) (|$v7#$bc_ProphecyBenchmark3Levels5Fields_Node3| T@$bc_ProphecyBenchmark3Levels5Fields_Node2) ) ) ))
(declare-datatypes ((T@Vec_11000 0)) (((Vec_11000 (|v#Vec_11000| |T@[Int]Int|) (|l#Vec_11000| Int) ) ) ))
(declare-datatypes ((T@$TypeParamInfo 0)) ((($TypeParamBool ) ($TypeParamU8 ) ($TypeParamU16 ) ($TypeParamU32 ) ($TypeParamU64 ) ($TypeParamU128 ) ($TypeParamU256 ) ($TypeParamI8 ) ($TypeParamI16 ) ($TypeParamI32 ) ($TypeParamI64 ) ($TypeParamI128 ) ($TypeParamI256 ) ($TypeParamAddress ) ($TypeParamSigner ) ($TypeParamVector (|e#$TypeParamVector| T@$TypeParamInfo) ) ($TypeParamStruct (|a#$TypeParamStruct| Int) (|m#$TypeParamStruct| T@Vec_11000) (|s#$TypeParamStruct| T@Vec_11000) ) ) ))
(declare-datatypes ((T@$signer 0)) ((($signer (|$addr#$signer| Int) ) ($permissioned_signer (|$addr#$permissioned_signer| Int) (|$permission_addr#$permissioned_signer| Int) ) ) ))
(declare-datatypes ((T@$Location 0)) ((($Global (|a#$Global| Int) ) ($Local (|i#$Local| Int) ) ($Param (|i#$Param| Int) ) ($Uninitialized ) ) ))
(declare-datatypes ((T@$Mutation_49963 0)) ((($Mutation_49963 (|l#$Mutation_49963| T@$Location) (|p#$Mutation_49963| T@Vec_11000) (|v#$Mutation_49963| T@$bc_ProphecyBenchmark3Levels5Fields_Node1) (|v_final#$Mutation_49963| T@$bc_ProphecyBenchmark3Levels5Fields_Node1) ) ) ))
(declare-datatypes ((T@$Mutation_49940 0)) ((($Mutation_49940 (|l#$Mutation_49940| T@$Location) (|p#$Mutation_49940| T@Vec_11000) (|v#$Mutation_49940| T@$bc_ProphecyBenchmark3Levels5Fields_Node2) (|v_final#$Mutation_49940| T@$bc_ProphecyBenchmark3Levels5Fields_Node2) ) ) ))
(declare-datatypes ((T@$Mutation_49917 0)) ((($Mutation_49917 (|l#$Mutation_49917| T@$Location) (|p#$Mutation_49917| T@Vec_11000) (|v#$Mutation_49917| T@$bc_ProphecyBenchmark3Levels5Fields_Node3) (|v_final#$Mutation_49917| T@$bc_ProphecyBenchmark3Levels5Fields_Node3) ) ) ))
(declare-datatypes ((T@$Mutation_20877 0)) ((($Mutation_20877 (|l#$Mutation_20877| T@$Location) (|p#$Mutation_20877| T@Vec_11000) (|v#$Mutation_20877| Int) (|v_final#$Mutation_20877| Int) ) ) ))
(declare-datatypes ((T@$Mutation_44127 0)) ((($Mutation_44127 (|l#$Mutation_44127| T@$Location) (|p#$Mutation_44127| T@Vec_11000) (|v#$Mutation_44127| T@Vec_11000) (|v_final#$Mutation_44127| T@Vec_11000) ) ) ))
(declare-datatypes ((T@$Mutation_31641 0)) ((($Mutation_31641 (|l#$Mutation_31641| T@$Location) (|p#$Mutation_31641| T@Vec_11000) (|v#$Mutation_31641| T@T2_11239) (|v_final#$Mutation_31641| T@T2_11239) ) ) ))
(declare-datatypes ((T@$Mutation_31508 0)) ((($Mutation_31508 (|l#$Mutation_31508| T@$Location) (|p#$Mutation_31508| T@Vec_11000) (|v#$Mutation_31508| T@T_11045) (|v_final#$Mutation_31508| T@T_11045) ) ) ))
(declare-datatypes ((T@$Range 0)) ((($Range (|lb#$Range| Int) (|ub#$Range| Int) ) ) ))
(declare-fun $MAX_U128 () Int)
(declare-fun $MAX_I128 () Int)
(declare-fun $MIN_I128 () Int)
(declare-fun |Select__T@[Int]Int_| (|T@[Int]Int| Int) Int)
(declare-fun |lambda#1| (Int Int |T@[Int]Int| Int Int Int) |T@[Int]Int|)
(declare-fun $shr (Int Int) Int)
(declare-fun $pow (Int Int) Int)
(declare-fun $shlU8 (Int Int) Int)
(declare-fun $MAX_U8 () Int)
(declare-fun $shlU16 (Int Int) Int)
(declare-fun $MAX_U16 () Int)
(declare-fun $shlU32 (Int Int) Int)
(declare-fun $MAX_U32 () Int)
(declare-fun $shlU64 (Int Int) Int)
(declare-fun $MAX_U64 () Int)
(declare-fun $shlU128 (Int Int) Int)
(declare-fun $shlU256 (Int Int) Int)
(declare-fun $MAX_U256 () Int)
(declare-sort |T@[Int]Bool| 0)
(declare-fun $ConstMemoryDomain (Bool) |T@[Int]Bool|)
(declare-fun |lambda#4| (Bool) |T@[Int]Bool|)
(declare-fun |$IsEqual'vec'u8''| (T@Vec_11000 T@Vec_11000) Bool)
(declare-fun InRangeVec_19336 (T@Vec_11000 Int) Bool)
(declare-fun |$IsPrefix'vec'u8''| (T@Vec_11000 T@Vec_11000) Bool)
(declare-fun DefaultTableKeyExistsArray_990 () |T@[Int]Bool|)
(declare-fun IndexOfVec_11000 (T@Vec_11000 Int) Int)
(declare-fun $1_Signature_$ed25519_verify (T@Vec_11000 T@Vec_11000 T@Vec_11000) Bool)
(declare-fun |lambda#0| (Int Int Int |T@[Int]Int| |T@[Int]Int| Int Int) |T@[Int]Int|)
(declare-fun |lambda#3| (Int Int Int |T@[Int]Int| |T@[Int]Int| Int Int) |T@[Int]Int|)
(declare-fun |$IsValid'bv32'| ((_ BitVec 32)) Bool)
(declare-fun |$IsValid'address'| (Int) Bool)
(declare-fun |$IsSuffix'vec'u8''| (T@Vec_11000 T@Vec_11000) Bool)
(declare-fun |lambda#2| (Int Int |T@[Int]Int| Int Int) |T@[Int]Int|)
(declare-fun $shl (Int Int) Int)
(declare-fun $castBv256to64 ((_ BitVec 256)) (_ BitVec 64))
(declare-fun |$Arbitrary_value_of'bv64'| () (_ BitVec 64))
(declare-fun $MAX_I32 () Int)
(declare-fun $MIN_I32 () Int)
(declare-fun $shlBv8From16 ((_ BitVec 8) (_ BitVec 16)) (_ BitVec 8))
(declare-fun $shrBv8From16 ((_ BitVec 8) (_ BitVec 16)) (_ BitVec 8))
(declare-fun $shlBv8From32 ((_ BitVec 8) (_ BitVec 32)) (_ BitVec 8))
(declare-fun $shrBv8From32 ((_ BitVec 8) (_ BitVec 32)) (_ BitVec 8))
(declare-fun $shlBv8From64 ((_ BitVec 8) (_ BitVec 64)) (_ BitVec 8))
(declare-fun $shrBv8From64 ((_ BitVec 8) (_ BitVec 64)) (_ BitVec 8))
(declare-fun $shlBv8From128 ((_ BitVec 8) (_ BitVec 128)) (_ BitVec 8))
(declare-fun $shrBv8From128 ((_ BitVec 8) (_ BitVec 128)) (_ BitVec 8))
(declare-fun $shlBv8From256 ((_ BitVec 8) (_ BitVec 256)) (_ BitVec 8))
(declare-fun $shrBv8From256 ((_ BitVec 8) (_ BitVec 256)) (_ BitVec 8))
(declare-fun $shlBv16From32 ((_ BitVec 16) (_ BitVec 32)) (_ BitVec 16))
(declare-fun $shrBv16From32 ((_ BitVec 16) (_ BitVec 32)) (_ BitVec 16))
(declare-fun $shlBv16From64 ((_ BitVec 16) (_ BitVec 64)) (_ BitVec 16))
(declare-fun $shrBv16From64 ((_ BitVec 16) (_ BitVec 64)) (_ BitVec 16))
(declare-fun $shlBv16From128 ((_ BitVec 16) (_ BitVec 128)) (_ BitVec 16))
(declare-fun $shrBv16From128 ((_ BitVec 16) (_ BitVec 128)) (_ BitVec 16))
(declare-fun $shlBv16From256 ((_ BitVec 16) (_ BitVec 256)) (_ BitVec 16))
(declare-fun $shrBv16From256 ((_ BitVec 16) (_ BitVec 256)) (_ BitVec 16))
(declare-fun $shlBv32From64 ((_ BitVec 32) (_ BitVec 64)) (_ BitVec 32))
(declare-fun $shrBv32From64 ((_ BitVec 32) (_ BitVec 64)) (_ BitVec 32))
(declare-fun $shlBv32From128 ((_ BitVec 32) (_ BitVec 128)) (_ BitVec 32))
(declare-fun $shrBv32From128 ((_ BitVec 32) (_ BitVec 128)) (_ BitVec 32))
(declare-fun $shlBv32From256 ((_ BitVec 32) (_ BitVec 256)) (_ BitVec 32))
(declare-fun $shrBv32From256 ((_ BitVec 32) (_ BitVec 256)) (_ BitVec 32))
(declare-fun $shlBv64From128 ((_ BitVec 64) (_ BitVec 128)) (_ BitVec 64))
(declare-fun $shrBv64From128 ((_ BitVec 64) (_ BitVec 128)) (_ BitVec 64))
(declare-fun $shlBv64From256 ((_ BitVec 64) (_ BitVec 256)) (_ BitVec 64))
(declare-fun $shrBv64From256 ((_ BitVec 64) (_ BitVec 256)) (_ BitVec 64))
(declare-fun $shlBv128From256 ((_ BitVec 128) (_ BitVec 256)) (_ BitVec 128))
(declare-fun $shrBv128From256 ((_ BitVec 128) (_ BitVec 256)) (_ BitVec 128))
(declare-fun |$IsValid'vec'u8''| (T@Vec_11000) Bool)
(declare-fun |$IsValid'u64'| (Int) Bool)
(declare-fun |$IsValid'u8'| (Int) Bool)
(declare-fun |Select__T@[Int]Bool_| (|T@[Int]Bool| Int) Bool)
(declare-fun |$IsValid'num'| (Int) Bool)
(declare-fun $castBv64to256 ((_ BitVec 64)) (_ BitVec 256))
(declare-fun $undefined_int () Int)
(declare-fun $shlBv16From8 ((_ BitVec 16) (_ BitVec 8)) (_ BitVec 16))
(declare-fun $shrBv16From8 ((_ BitVec 16) (_ BitVec 8)) (_ BitVec 16))
(declare-fun $shlBv32From16 ((_ BitVec 32) (_ BitVec 16)) (_ BitVec 32))
(declare-fun $shrBv32From16 ((_ BitVec 32) (_ BitVec 16)) (_ BitVec 32))
(declare-fun $shlBv32From8 ((_ BitVec 32) (_ BitVec 8)) (_ BitVec 32))
(declare-fun $shrBv32From8 ((_ BitVec 32) (_ BitVec 8)) (_ BitVec 32))
(declare-fun $shlBv64From32 ((_ BitVec 64) (_ BitVec 32)) (_ BitVec 64))
(declare-fun $shrBv64From32 ((_ BitVec 64) (_ BitVec 32)) (_ BitVec 64))
(declare-fun $shlBv64From16 ((_ BitVec 64) (_ BitVec 16)) (_ BitVec 64))
(declare-fun $shrBv64From16 ((_ BitVec 64) (_ BitVec 16)) (_ BitVec 64))
(declare-fun $shlBv64From8 ((_ BitVec 64) (_ BitVec 8)) (_ BitVec 64))
(declare-fun $shrBv64From8 ((_ BitVec 64) (_ BitVec 8)) (_ BitVec 64))
(declare-fun $shlBv128From64 ((_ BitVec 128) (_ BitVec 64)) (_ BitVec 128))
(declare-fun $shrBv128From64 ((_ BitVec 128) (_ BitVec 64)) (_ BitVec 128))
(declare-fun $shlBv128From32 ((_ BitVec 128) (_ BitVec 32)) (_ BitVec 128))
(declare-fun $shrBv128From32 ((_ BitVec 128) (_ BitVec 32)) (_ BitVec 128))
(declare-fun $shlBv128From16 ((_ BitVec 128) (_ BitVec 16)) (_ BitVec 128))
(declare-fun $shrBv128From16 ((_ BitVec 128) (_ BitVec 16)) (_ BitVec 128))
(declare-fun $shlBv128From8 ((_ BitVec 128) (_ BitVec 8)) (_ BitVec 128))
(declare-fun $shrBv128From8 ((_ BitVec 128) (_ BitVec 8)) (_ BitVec 128))
(declare-fun $shlBv256From128 ((_ BitVec 256) (_ BitVec 128)) (_ BitVec 256))
(declare-fun $shrBv256From128 ((_ BitVec 256) (_ BitVec 128)) (_ BitVec 256))
(declare-fun $shlBv256From64 ((_ BitVec 256) (_ BitVec 64)) (_ BitVec 256))
(declare-fun $shrBv256From64 ((_ BitVec 256) (_ BitVec 64)) (_ BitVec 256))
(declare-fun $shlBv256From32 ((_ BitVec 256) (_ BitVec 32)) (_ BitVec 256))
(declare-fun $shrBv256From32 ((_ BitVec 256) (_ BitVec 32)) (_ BitVec 256))
(declare-fun $shlBv256From16 ((_ BitVec 256) (_ BitVec 16)) (_ BitVec 256))
(declare-fun $shrBv256From16 ((_ BitVec 256) (_ BitVec 16)) (_ BitVec 256))
(declare-fun $shlBv256From8 ((_ BitVec 256) (_ BitVec 8)) (_ BitVec 256))
(declare-fun $shrBv256From8 ((_ BitVec 256) (_ BitVec 8)) (_ BitVec 256))
(declare-fun |$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node1'| (T@$bc_ProphecyBenchmark3Levels5Fields_Node1) Bool)
(declare-fun |$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node2'| (T@$bc_ProphecyBenchmark3Levels5Fields_Node2) Bool)
(declare-fun |$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node3'| (T@$bc_ProphecyBenchmark3Levels5Fields_Node3) Bool)
(declare-fun $castBv64to64 ((_ BitVec 64)) (_ BitVec 64))
(declare-fun $castBv256to256 ((_ BitVec 256)) (_ BitVec 256))
(declare-fun $shlBv8From8 ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
(declare-fun $shrBv8From8 ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
(declare-fun $shlBv16From16 ((_ BitVec 16) (_ BitVec 16)) (_ BitVec 16))
(declare-fun $shrBv16From16 ((_ BitVec 16) (_ BitVec 16)) (_ BitVec 16))
(declare-fun $shlBv32From32 ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))
(declare-fun $shrBv32From32 ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))
(declare-fun $shlBv64From64 ((_ BitVec 64) (_ BitVec 64)) (_ BitVec 64))
(declare-fun $shrBv64From64 ((_ BitVec 64) (_ BitVec 64)) (_ BitVec 64))
(declare-fun $shlBv128From128 ((_ BitVec 128) (_ BitVec 128)) (_ BitVec 128))
(declare-fun $shrBv128From128 ((_ BitVec 128) (_ BitVec 128)) (_ BitVec 128))
(declare-fun $shlBv256From256 ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))
(declare-fun $shrBv256From256 ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))
(declare-fun $1_Signature_$ed25519_validate_pubkey (T@Vec_11000) Bool)
(declare-fun |$IsValid'bv8'| ((_ BitVec 8)) Bool)
(declare-fun |$IsValid'bv64'| ((_ BitVec 64)) Bool)
(declare-fun |$IsValid'bv16'| ((_ BitVec 16)) Bool)
(declare-fun |$IsValid'bv256'| ((_ BitVec 256)) Bool)
(declare-fun |$IndexOfVec'u8'| (T@Vec_11000 Int) Int)
(declare-fun |$IsValid'bv128'| ((_ BitVec 128)) Bool)
(declare-fun $1_hash_sha2 (T@Vec_11000) T@Vec_11000)
(declare-fun $1_hash_sha3 (T@Vec_11000) T@Vec_11000)
(declare-fun $MIN_U8 () Int)
(declare-fun |$IsValid'u16'| (Int) Bool)
(declare-fun $MIN_U16 () Int)
(declare-fun |$IsValid'u32'| (Int) Bool)
(declare-fun $MIN_U32 () Int)
(declare-fun $MIN_U64 () Int)
(declare-fun |$IsValid'u128'| (Int) Bool)
(declare-fun $MIN_U128 () Int)
(declare-fun |$IsValid'u256'| (Int) Bool)
(declare-fun $MIN_U256 () Int)
(declare-fun |$IsValid'i8'| (Int) Bool)
(declare-fun $MIN_I8 () Int)
(declare-fun $MAX_I8 () Int)
(declare-fun |$IsValid'i16'| (Int) Bool)
(declare-fun $MIN_I16 () Int)
(declare-fun $MAX_I16 () Int)
(declare-fun |$IsValid'i32'| (Int) Bool)
(declare-fun |$IsValid'i64'| (Int) Bool)
(declare-fun $MIN_I64 () Int)
(declare-fun $MAX_I64 () Int)
(declare-fun |$IsValid'i128'| (Int) Bool)
(declare-fun |$IsValid'i256'| (Int) Bool)
(declare-fun $MIN_I256 () Int)
(declare-fun $MAX_I256 () Int)
(declare-fun $InRange (T@$Range Int) Bool)
(declare-fun $EXEC_FAILURE_CODE () Int)
(assert (= $MAX_U128 340282366920938463463374607431768211455))
(assert (= $MAX_I128 170141183460469231731687303715884105727))
(assert (= $MIN_I128 (- 0 170141183460469231731687303715884105728)))
(assert (forall ((|l#0| Int) (|l#1| Int) (|l#2| |T@[Int]Int|) (|l#3| Int) (|l#4| Int) (|l#5| Int) (i Int) ) (! (= (|Select__T@[Int]Int_| (|lambda#1| |l#0| |l#1| |l#2| |l#3| |l#4| |l#5|) i) (ite  (and (<= |l#0| i) (< i |l#1|)) (|Select__T@[Int]Int_| |l#2| (- (- |l#3| i) |l#4|)) |l#5|))
 :qid |outputbpl.83:30|
 :skolemid |136|
 :pattern ( (|Select__T@[Int]Int_| (|lambda#1| |l#0| |l#1| |l#2| |l#3| |l#4| |l#5|) i))
)))
(assert (forall ((src1 Int) (p Int) ) (! (= ($shr src1 p) (div src1 ($pow 2 p)))
 :qid |outputbpl.982:15|
 :skolemid |22|
 :pattern ( ($shr src1 p))
)))
(assert (forall ((src1@@0 Int) (p@@0 Int) ) (! (= ($shlU8 src1@@0 p@@0) (mod (* src1@@0 ($pow 2 p@@0)) (+ $MAX_U8 1)))
 :qid |outputbpl.997:17|
 :skolemid |23|
 :pattern ( ($shlU8 src1@@0 p@@0))
)))
(assert (forall ((src1@@1 Int) (p@@1 Int) ) (! (= ($shlU16 src1@@1 p@@1) (mod (* src1@@1 ($pow 2 p@@1)) (+ $MAX_U16 1)))
 :qid |outputbpl.1028:18|
 :skolemid |24|
 :pattern ( ($shlU16 src1@@1 p@@1))
)))
(assert (forall ((src1@@2 Int) (p@@2 Int) ) (! (= ($shlU32 src1@@2 p@@2) (mod (* src1@@2 ($pow 2 p@@2)) (+ $MAX_U32 1)))
 :qid |outputbpl.1059:18|
 :skolemid |25|
 :pattern ( ($shlU32 src1@@2 p@@2))
)))
(assert (forall ((src1@@3 Int) (p@@3 Int) ) (! (= ($shlU64 src1@@3 p@@3) (mod (* src1@@3 ($pow 2 p@@3)) (+ $MAX_U64 1)))
 :qid |outputbpl.1090:18|
 :skolemid |26|
 :pattern ( ($shlU64 src1@@3 p@@3))
)))
(assert (forall ((src1@@4 Int) (p@@4 Int) ) (! (= ($shlU128 src1@@4 p@@4) (mod (* src1@@4 ($pow 2 p@@4)) (+ $MAX_U128 1)))
 :qid |outputbpl.1121:19|
 :skolemid |27|
 :pattern ( ($shlU128 src1@@4 p@@4))
)))
(assert (forall ((src1@@5 Int) (p@@5 Int) ) (! (= ($shlU256 src1@@5 p@@5) (mod (* src1@@5 ($pow 2 p@@5)) (+ $MAX_U256 1)))
 :qid |outputbpl.1152:19|
 :skolemid |28|
 :pattern ( ($shlU256 src1@@5 p@@5))
)))
(assert (= ($ConstMemoryDomain false) (|lambda#4| false)))
(assert (= ($ConstMemoryDomain true) (|lambda#4| true)))
(assert (forall ((v1 T@Vec_11000) (v2 T@Vec_11000) ) (! (= (|$IsEqual'vec'u8''| v1 v2)  (and (= (|l#Vec_11000| v1) (|l#Vec_11000| v2)) (forall ((i@@0 Int) ) (!  (=> (InRangeVec_19336 v1 i@@0) (= (|Select__T@[Int]Int_| (|v#Vec_11000| v1) i@@0) (|Select__T@[Int]Int_| (|v#Vec_11000| v2) i@@0)))
 :qid |outputbpl.3766:13|
 :skolemid |117|
))))
 :qid |outputbpl.3764:28|
 :skolemid |118|
 :pattern ( (|$IsEqual'vec'u8''| v1 v2))
)))
(assert (forall ((v T@Vec_11000) (prefix T@Vec_11000) ) (! (= (|$IsPrefix'vec'u8''| v prefix)  (and (>= (|l#Vec_11000| v) (|l#Vec_11000| prefix)) (forall ((i@@1 Int) ) (!  (=> (InRangeVec_19336 prefix i@@1) (= (|Select__T@[Int]Int_| (|v#Vec_11000| v) i@@1) (|Select__T@[Int]Int_| (|v#Vec_11000| prefix) i@@1)))
 :qid |outputbpl.3772:13|
 :skolemid |119|
))))
 :qid |outputbpl.3770:29|
 :skolemid |120|
 :pattern ( (|$IsPrefix'vec'u8''| v prefix))
)))
(assert (= DefaultTableKeyExistsArray_990 (|lambda#4| false)))
(assert (forall ((v@@0 T@Vec_11000) (e Int) ) (! (let ((i@@2 (IndexOfVec_11000 v@@0 e)))
(ite  (not (exists ((i@@3 Int) ) (!  (and (InRangeVec_19336 v@@0 i@@3) (= (|Select__T@[Int]Int_| (|v#Vec_11000| v@@0) i@@3) e))
 :qid |outputbpl.110:13|
 :skolemid |0|
))) (= i@@2 (- 0 1))  (and (and (InRangeVec_19336 v@@0 i@@2) (= (|Select__T@[Int]Int_| (|v#Vec_11000| v@@0) i@@2) e)) (forall ((j Int) ) (!  (=> (and (>= j 0) (< j i@@2)) (not (= (|Select__T@[Int]Int_| (|v#Vec_11000| v@@0) j) e)))
 :qid |outputbpl.118:17|
 :skolemid |1|
)))))
 :qid |outputbpl.114:32|
 :skolemid |2|
 :pattern ( (IndexOfVec_11000 v@@0 e))
)))
(assert (forall ((s1 T@Vec_11000) (s2 T@Vec_11000) (k1 T@Vec_11000) (k2 T@Vec_11000) (m1 T@Vec_11000) (m2 T@Vec_11000) ) (!  (=> (and (and (|$IsEqual'vec'u8''| s1 s2) (|$IsEqual'vec'u8''| k1 k2)) (|$IsEqual'vec'u8''| m1 m2)) (= ($1_Signature_$ed25519_verify s1 k1 m1) ($1_Signature_$ed25519_verify s2 k2 m2)))
 :qid |outputbpl.4218:15|
 :skolemid |131|
 :pattern ( ($1_Signature_$ed25519_verify s1 k1 m1) ($1_Signature_$ed25519_verify s2 k2 m2))
)))
(assert (forall ((|l#0@@0| Int) (|l#1@@0| Int) (|l#2@@0| Int) (|l#3@@0| |T@[Int]Int|) (|l#4@@0| |T@[Int]Int|) (|l#5@@0| Int) (|l#6| Int) (i@@4 Int) ) (! (= (|Select__T@[Int]Int_| (|lambda#0| |l#0@@0| |l#1@@0| |l#2@@0| |l#3@@0| |l#4@@0| |l#5@@0| |l#6|) i@@4) (ite  (and (>= i@@4 |l#0@@0|) (< i@@4 |l#1@@0|)) (ite (< i@@4 |l#2@@0|) (|Select__T@[Int]Int_| |l#3@@0| i@@4) (|Select__T@[Int]Int_| |l#4@@0| (- i@@4 |l#5@@0|))) |l#6|))
 :qid |outputbpl.74:19|
 :skolemid |135|
 :pattern ( (|Select__T@[Int]Int_| (|lambda#0| |l#0@@0| |l#1@@0| |l#2@@0| |l#3@@0| |l#4@@0| |l#5@@0| |l#6|) i@@4))
)))
(assert (forall ((|l#0@@1| Int) (|l#1@@1| Int) (|l#2@@1| Int) (|l#3@@1| |T@[Int]Int|) (|l#4@@1| |T@[Int]Int|) (|l#5@@1| Int) (|l#6@@0| Int) (j@@0 Int) ) (! (= (|Select__T@[Int]Int_| (|lambda#3| |l#0@@1| |l#1@@1| |l#2@@1| |l#3@@1| |l#4@@1| |l#5@@1| |l#6@@0|) j@@0) (ite  (and (>= j@@0 |l#0@@1|) (< j@@0 |l#1@@1|)) (ite (< j@@0 |l#2@@1|) (|Select__T@[Int]Int_| |l#3@@1| j@@0) (|Select__T@[Int]Int_| |l#4@@1| (+ j@@0 |l#5@@1|))) |l#6@@0|))
 :qid |outputbpl.64:20|
 :skolemid |138|
 :pattern ( (|Select__T@[Int]Int_| (|lambda#3| |l#0@@1| |l#1@@1| |l#2@@1| |l#3@@1| |l#4@@1| |l#5@@1| |l#6@@0|) j@@0))
)))
(assert (forall ((v@@1 (_ BitVec 32)) ) (! (= (|$IsValid'bv32'| v@@1)  (and (bvuge v@@1 #x00000000) (bvule v@@1 #x7fffffff)))
 :qid |outputbpl.1629:25|
 :skolemid |31|
 :pattern ( (|$IsValid'bv32'| v@@1))
)))
(assert (forall ((v@@2 Int) ) (! (= (|$IsValid'address'| v@@2) (>= v@@2 0))
 :qid |outputbpl.2041:28|
 :skolemid |36|
 :pattern ( (|$IsValid'address'| v@@2))
)))
(assert (forall ((v@@3 T@Vec_11000) (suffix T@Vec_11000) ) (! (= (|$IsSuffix'vec'u8''| v@@3 suffix)  (and (>= (|l#Vec_11000| v@@3) (|l#Vec_11000| suffix)) (forall ((i@@5 Int) ) (!  (=> (InRangeVec_19336 suffix i@@5) (= (|Select__T@[Int]Int_| (|v#Vec_11000| v@@3) (+ (- (|l#Vec_11000| v@@3) (|l#Vec_11000| suffix)) i@@5)) (|Select__T@[Int]Int_| (|v#Vec_11000| suffix) i@@5)))
 :qid |outputbpl.3778:13|
 :skolemid |121|
))))
 :qid |outputbpl.3776:29|
 :skolemid |122|
 :pattern ( (|$IsSuffix'vec'u8''| v@@3 suffix))
)))
(assert (forall ((|l#0@@2| Int) (|l#1@@2| Int) (|l#2@@2| |T@[Int]Int|) (|l#3@@2| Int) (|l#4@@2| Int) (k Int) ) (! (= (|Select__T@[Int]Int_| (|lambda#2| |l#0@@2| |l#1@@2| |l#2@@2| |l#3@@2| |l#4@@2|) k) (ite  (and (<= |l#0@@2| k) (< k |l#1@@2|)) (|Select__T@[Int]Int_| |l#2@@2| (+ |l#3@@2| k)) |l#4@@2|))
 :qid |outputbpl.91:14|
 :skolemid |137|
 :pattern ( (|Select__T@[Int]Int_| (|lambda#2| |l#0@@2| |l#1@@2| |l#2@@2| |l#3@@2| |l#4@@2|) k))
)))
(assert (forall ((src1@@6 Int) (p@@6 Int) ) (! (= ($shl src1@@6 p@@6) (* src1@@6 ($pow 2 p@@6)))
 :qid |outputbpl.978:15|
 :skolemid |21|
 :pattern ( ($shl src1@@6 p@@6))
)))
(assert (forall ((src (_ BitVec 256)) ) (! (= ($castBv256to64 src) (ite (bvugt src #x000000000000000000000000000000000000000000000000ffffffffffffffff) |$Arbitrary_value_of'bv64'| ((_ extract 63 0) src)))
 :qid |outputbpl.3261:25|
 :skolemid |88|
 :pattern ( ($castBv256to64 src))
)))
(assert (= $MAX_I32 2147483647))
(assert (= $MIN_I32 (- 0 2147483648)))
(assert (forall ((src1@@7 (_ BitVec 8)) (src2 (_ BitVec 16)) ) (! (= ($shlBv8From16 src1@@7 src2) (bvshl src1@@7 ((_ extract 7 0) src2)))
 :qid |outputbpl.2391:24|
 :skolemid |43|
 :pattern ( ($shlBv8From16 src1@@7 src2))
)))
(assert (forall ((src1@@8 (_ BitVec 8)) (src2@@0 (_ BitVec 16)) ) (! (= ($shrBv8From16 src1@@8 src2@@0) (bvlshr src1@@8 ((_ extract 7 0) src2@@0)))
 :qid |outputbpl.2406:24|
 :skolemid |44|
 :pattern ( ($shrBv8From16 src1@@8 src2@@0))
)))
(assert (forall ((src1@@9 (_ BitVec 8)) (src2@@1 (_ BitVec 32)) ) (! (= ($shlBv8From32 src1@@9 src2@@1) (bvshl src1@@9 ((_ extract 7 0) src2@@1)))
 :qid |outputbpl.2432:24|
 :skolemid |45|
 :pattern ( ($shlBv8From32 src1@@9 src2@@1))
)))
(assert (forall ((src1@@10 (_ BitVec 8)) (src2@@2 (_ BitVec 32)) ) (! (= ($shrBv8From32 src1@@10 src2@@2) (bvlshr src1@@10 ((_ extract 7 0) src2@@2)))
 :qid |outputbpl.2447:24|
 :skolemid |46|
 :pattern ( ($shrBv8From32 src1@@10 src2@@2))
)))
(assert (forall ((src1@@11 (_ BitVec 8)) (src2@@3 (_ BitVec 64)) ) (! (= ($shlBv8From64 src1@@11 src2@@3) (bvshl src1@@11 ((_ extract 7 0) src2@@3)))
 :qid |outputbpl.2473:24|
 :skolemid |47|
 :pattern ( ($shlBv8From64 src1@@11 src2@@3))
)))
(assert (forall ((src1@@12 (_ BitVec 8)) (src2@@4 (_ BitVec 64)) ) (! (= ($shrBv8From64 src1@@12 src2@@4) (bvlshr src1@@12 ((_ extract 7 0) src2@@4)))
 :qid |outputbpl.2488:24|
 :skolemid |48|
 :pattern ( ($shrBv8From64 src1@@12 src2@@4))
)))
(assert (forall ((src1@@13 (_ BitVec 8)) (src2@@5 (_ BitVec 128)) ) (! (= ($shlBv8From128 src1@@13 src2@@5) (bvshl src1@@13 ((_ extract 7 0) src2@@5)))
 :qid |outputbpl.2514:25|
 :skolemid |49|
 :pattern ( ($shlBv8From128 src1@@13 src2@@5))
)))
(assert (forall ((src1@@14 (_ BitVec 8)) (src2@@6 (_ BitVec 128)) ) (! (= ($shrBv8From128 src1@@14 src2@@6) (bvlshr src1@@14 ((_ extract 7 0) src2@@6)))
 :qid |outputbpl.2529:25|
 :skolemid |50|
 :pattern ( ($shrBv8From128 src1@@14 src2@@6))
)))
(assert (forall ((src1@@15 (_ BitVec 8)) (src2@@7 (_ BitVec 256)) ) (! (= ($shlBv8From256 src1@@15 src2@@7) (bvshl src1@@15 ((_ extract 7 0) src2@@7)))
 :qid |outputbpl.2555:25|
 :skolemid |51|
 :pattern ( ($shlBv8From256 src1@@15 src2@@7))
)))
(assert (forall ((src1@@16 (_ BitVec 8)) (src2@@8 (_ BitVec 256)) ) (! (= ($shrBv8From256 src1@@16 src2@@8) (bvlshr src1@@16 ((_ extract 7 0) src2@@8)))
 :qid |outputbpl.2570:25|
 :skolemid |52|
 :pattern ( ($shrBv8From256 src1@@16 src2@@8))
)))
(assert (forall ((src1@@17 (_ BitVec 16)) (src2@@9 (_ BitVec 32)) ) (! (= ($shlBv16From32 src1@@17 src2@@9) (bvshl src1@@17 ((_ extract 15 0) src2@@9)))
 :qid |outputbpl.2670:25|
 :skolemid |57|
 :pattern ( ($shlBv16From32 src1@@17 src2@@9))
)))
(assert (forall ((src1@@18 (_ BitVec 16)) (src2@@10 (_ BitVec 32)) ) (! (= ($shrBv16From32 src1@@18 src2@@10) (bvlshr src1@@18 ((_ extract 15 0) src2@@10)))
 :qid |outputbpl.2685:25|
 :skolemid |58|
 :pattern ( ($shrBv16From32 src1@@18 src2@@10))
)))
(assert (forall ((src1@@19 (_ BitVec 16)) (src2@@11 (_ BitVec 64)) ) (! (= ($shlBv16From64 src1@@19 src2@@11) (bvshl src1@@19 ((_ extract 15 0) src2@@11)))
 :qid |outputbpl.2711:25|
 :skolemid |59|
 :pattern ( ($shlBv16From64 src1@@19 src2@@11))
)))
(assert (forall ((src1@@20 (_ BitVec 16)) (src2@@12 (_ BitVec 64)) ) (! (= ($shrBv16From64 src1@@20 src2@@12) (bvlshr src1@@20 ((_ extract 15 0) src2@@12)))
 :qid |outputbpl.2726:25|
 :skolemid |60|
 :pattern ( ($shrBv16From64 src1@@20 src2@@12))
)))
(assert (forall ((src1@@21 (_ BitVec 16)) (src2@@13 (_ BitVec 128)) ) (! (= ($shlBv16From128 src1@@21 src2@@13) (bvshl src1@@21 ((_ extract 15 0) src2@@13)))
 :qid |outputbpl.2752:26|
 :skolemid |61|
 :pattern ( ($shlBv16From128 src1@@21 src2@@13))
)))
(assert (forall ((src1@@22 (_ BitVec 16)) (src2@@14 (_ BitVec 128)) ) (! (= ($shrBv16From128 src1@@22 src2@@14) (bvlshr src1@@22 ((_ extract 15 0) src2@@14)))
 :qid |outputbpl.2767:26|
 :skolemid |62|
 :pattern ( ($shrBv16From128 src1@@22 src2@@14))
)))
(assert (forall ((src1@@23 (_ BitVec 16)) (src2@@15 (_ BitVec 256)) ) (! (= ($shlBv16From256 src1@@23 src2@@15) (bvshl src1@@23 ((_ extract 15 0) src2@@15)))
 :qid |outputbpl.2793:26|
 :skolemid |63|
 :pattern ( ($shlBv16From256 src1@@23 src2@@15))
)))
(assert (forall ((src1@@24 (_ BitVec 16)) (src2@@16 (_ BitVec 256)) ) (! (= ($shrBv16From256 src1@@24 src2@@16) (bvlshr src1@@24 ((_ extract 15 0) src2@@16)))
 :qid |outputbpl.2808:26|
 :skolemid |64|
 :pattern ( ($shrBv16From256 src1@@24 src2@@16))
)))
(assert (forall ((src1@@25 (_ BitVec 32)) (src2@@17 (_ BitVec 64)) ) (! (= ($shlBv32From64 src1@@25 src2@@17) (bvshl src1@@25 ((_ extract 31 0) src2@@17)))
 :qid |outputbpl.2945:25|
 :skolemid |71|
 :pattern ( ($shlBv32From64 src1@@25 src2@@17))
)))
(assert (forall ((src1@@26 (_ BitVec 32)) (src2@@18 (_ BitVec 64)) ) (! (= ($shrBv32From64 src1@@26 src2@@18) (bvlshr src1@@26 ((_ extract 31 0) src2@@18)))
 :qid |outputbpl.2960:25|
 :skolemid |72|
 :pattern ( ($shrBv32From64 src1@@26 src2@@18))
)))
(assert (forall ((src1@@27 (_ BitVec 32)) (src2@@19 (_ BitVec 128)) ) (! (= ($shlBv32From128 src1@@27 src2@@19) (bvshl src1@@27 ((_ extract 31 0) src2@@19)))
 :qid |outputbpl.2986:26|
 :skolemid |73|
 :pattern ( ($shlBv32From128 src1@@27 src2@@19))
)))
(assert (forall ((src1@@28 (_ BitVec 32)) (src2@@20 (_ BitVec 128)) ) (! (= ($shrBv32From128 src1@@28 src2@@20) (bvlshr src1@@28 ((_ extract 31 0) src2@@20)))
 :qid |outputbpl.3001:26|
 :skolemid |74|
 :pattern ( ($shrBv32From128 src1@@28 src2@@20))
)))
(assert (forall ((src1@@29 (_ BitVec 32)) (src2@@21 (_ BitVec 256)) ) (! (= ($shlBv32From256 src1@@29 src2@@21) (bvshl src1@@29 ((_ extract 31 0) src2@@21)))
 :qid |outputbpl.3027:26|
 :skolemid |75|
 :pattern ( ($shlBv32From256 src1@@29 src2@@21))
)))
(assert (forall ((src1@@30 (_ BitVec 32)) (src2@@22 (_ BitVec 256)) ) (! (= ($shrBv32From256 src1@@30 src2@@22) (bvlshr src1@@30 ((_ extract 31 0) src2@@22)))
 :qid |outputbpl.3042:26|
 :skolemid |76|
 :pattern ( ($shrBv32From256 src1@@30 src2@@22))
)))
(assert (forall ((src1@@31 (_ BitVec 64)) (src2@@23 (_ BitVec 128)) ) (! (= ($shlBv64From128 src1@@31 src2@@23) (bvshl src1@@31 ((_ extract 63 0) src2@@23)))
 :qid |outputbpl.3221:26|
 :skolemid |86|
 :pattern ( ($shlBv64From128 src1@@31 src2@@23))
)))
(assert (forall ((src1@@32 (_ BitVec 64)) (src2@@24 (_ BitVec 128)) ) (! (= ($shrBv64From128 src1@@32 src2@@24) (bvlshr src1@@32 ((_ extract 63 0) src2@@24)))
 :qid |outputbpl.3236:26|
 :skolemid |87|
 :pattern ( ($shrBv64From128 src1@@32 src2@@24))
)))
(assert (forall ((src1@@33 (_ BitVec 64)) (src2@@25 (_ BitVec 256)) ) (! (= ($shlBv64From256 src1@@33 src2@@25) (bvshl src1@@33 ((_ extract 63 0) src2@@25)))
 :qid |outputbpl.3270:26|
 :skolemid |89|
 :pattern ( ($shlBv64From256 src1@@33 src2@@25))
)))
(assert (forall ((src1@@34 (_ BitVec 64)) (src2@@26 (_ BitVec 256)) ) (! (= ($shrBv64From256 src1@@34 src2@@26) (bvlshr src1@@34 ((_ extract 63 0) src2@@26)))
 :qid |outputbpl.3285:26|
 :skolemid |90|
 :pattern ( ($shrBv64From256 src1@@34 src2@@26))
)))
(assert (forall ((src1@@35 (_ BitVec 128)) (src2@@27 (_ BitVec 256)) ) (! (= ($shlBv128From256 src1@@35 src2@@27) (bvshl src1@@35 ((_ extract 127 0) src2@@27)))
 :qid |outputbpl.3496:27|
 :skolemid |101|
 :pattern ( ($shlBv128From256 src1@@35 src2@@27))
)))
(assert (forall ((src1@@36 (_ BitVec 128)) (src2@@28 (_ BitVec 256)) ) (! (= ($shrBv128From256 src1@@36 src2@@28) (bvlshr src1@@36 ((_ extract 127 0) src2@@28)))
 :qid |outputbpl.3511:27|
 :skolemid |102|
 :pattern ( ($shrBv128From256 src1@@36 src2@@28))
)))
(assert (forall ((v@@4 T@Vec_11000) ) (! (= (|$IsValid'vec'u8''| v@@4)  (and (|$IsValid'u64'| (|l#Vec_11000| v@@4)) (forall ((i@@6 Int) ) (!  (=> (InRangeVec_19336 v@@4 i@@6) (|$IsValid'u8'| (|Select__T@[Int]Int_| (|v#Vec_11000| v@@4) i@@6)))
 :qid |outputbpl.3784:13|
 :skolemid |123|
))))
 :qid |outputbpl.3782:28|
 :skolemid |124|
 :pattern ( (|$IsValid'vec'u8''| v@@4))
)))
(assert (forall ((|l#0@@3| Bool) (i@@7 Int) ) (! (= (|Select__T@[Int]Bool_| (|lambda#4| |l#0@@3|) i@@7) |l#0@@3|)
 :qid |outputbpl.194:57|
 :skolemid |139|
 :pattern ( (|Select__T@[Int]Bool_| (|lambda#4| |l#0@@3|) i@@7))
)))
(assert (forall ((v@@5 Int) ) (! (= (|$IsValid'num'| v@@5) true)
 :qid |outputbpl.2037:24|
 :skolemid |35|
 :pattern ( (|$IsValid'num'| v@@5))
)))
(assert (forall ((src@@0 (_ BitVec 64)) ) (! (= ($castBv64to256 src@@0) (concat #x000000000000000000000000000000000000000000000000 src@@0))
 :qid |outputbpl.3635:25|
 :skolemid |109|
 :pattern ( ($castBv64to256 src@@0))
)))
(assert (forall ((n Int) (e@@0 Int) ) (! (= ($pow n e@@0) (ite  (and (not (= n 0)) (= e@@0 0)) 1 (ite (> e@@0 0) (* n ($pow n (- e@@0 1))) $undefined_int)))
 :qid |outputbpl.972:15|
 :skolemid |20|
 :pattern ( ($pow n e@@0))
)))
(assert (forall ((src1@@37 (_ BitVec 16)) (src2@@29 (_ BitVec 8)) ) (! (= ($shlBv16From8 src1@@37 src2@@29) (bvshl src1@@37 (concat #x00 src2@@29)))
 :qid |outputbpl.2592:24|
 :skolemid |53|
 :pattern ( ($shlBv16From8 src1@@37 src2@@29))
)))
(assert (forall ((src1@@38 (_ BitVec 16)) (src2@@30 (_ BitVec 8)) ) (! (= ($shrBv16From8 src1@@38 src2@@30) (bvlshr src1@@38 (concat #x00 src2@@30)))
 :qid |outputbpl.2607:24|
 :skolemid |54|
 :pattern ( ($shrBv16From8 src1@@38 src2@@30))
)))
(assert (forall ((src1@@39 (_ BitVec 32)) (src2@@31 (_ BitVec 16)) ) (! (= ($shlBv32From16 src1@@39 src2@@31) (bvshl src1@@39 (concat #x0000 src2@@31)))
 :qid |outputbpl.2867:25|
 :skolemid |67|
 :pattern ( ($shlBv32From16 src1@@39 src2@@31))
)))
(assert (forall ((src1@@40 (_ BitVec 32)) (src2@@32 (_ BitVec 16)) ) (! (= ($shrBv32From16 src1@@40 src2@@32) (bvlshr src1@@40 (concat #x0000 src2@@32)))
 :qid |outputbpl.2882:25|
 :skolemid |68|
 :pattern ( ($shrBv32From16 src1@@40 src2@@32))
)))
(assert (forall ((src1@@41 (_ BitVec 32)) (src2@@33 (_ BitVec 8)) ) (! (= ($shlBv32From8 src1@@41 src2@@33) (bvshl src1@@41 (concat #x000000 src2@@33)))
 :qid |outputbpl.2830:24|
 :skolemid |65|
 :pattern ( ($shlBv32From8 src1@@41 src2@@33))
)))
(assert (forall ((src1@@42 (_ BitVec 32)) (src2@@34 (_ BitVec 8)) ) (! (= ($shrBv32From8 src1@@42 src2@@34) (bvlshr src1@@42 (concat #x000000 src2@@34)))
 :qid |outputbpl.2845:24|
 :skolemid |66|
 :pattern ( ($shrBv32From8 src1@@42 src2@@34))
)))
(assert (forall ((src1@@43 (_ BitVec 64)) (src2@@35 (_ BitVec 32)) ) (! (= ($shlBv64From32 src1@@43 src2@@35) (bvshl src1@@43 (concat #x00000000 src2@@35)))
 :qid |outputbpl.3138:25|
 :skolemid |81|
 :pattern ( ($shlBv64From32 src1@@43 src2@@35))
)))
(assert (forall ((src1@@44 (_ BitVec 64)) (src2@@36 (_ BitVec 32)) ) (! (= ($shrBv64From32 src1@@44 src2@@36) (bvlshr src1@@44 (concat #x00000000 src2@@36)))
 :qid |outputbpl.3153:25|
 :skolemid |82|
 :pattern ( ($shrBv64From32 src1@@44 src2@@36))
)))
(assert (forall ((src1@@45 (_ BitVec 64)) (src2@@37 (_ BitVec 16)) ) (! (= ($shlBv64From16 src1@@45 src2@@37) (bvshl src1@@45 (concat #x000000000000 src2@@37)))
 :qid |outputbpl.3101:25|
 :skolemid |79|
 :pattern ( ($shlBv64From16 src1@@45 src2@@37))
)))
(assert (forall ((src1@@46 (_ BitVec 64)) (src2@@38 (_ BitVec 16)) ) (! (= ($shrBv64From16 src1@@46 src2@@38) (bvlshr src1@@46 (concat #x000000000000 src2@@38)))
 :qid |outputbpl.3116:25|
 :skolemid |80|
 :pattern ( ($shrBv64From16 src1@@46 src2@@38))
)))
(assert (forall ((src1@@47 (_ BitVec 64)) (src2@@39 (_ BitVec 8)) ) (! (= ($shlBv64From8 src1@@47 src2@@39) (bvshl src1@@47 (concat #x00000000000000 src2@@39)))
 :qid |outputbpl.3064:24|
 :skolemid |77|
 :pattern ( ($shlBv64From8 src1@@47 src2@@39))
)))
(assert (forall ((src1@@48 (_ BitVec 64)) (src2@@40 (_ BitVec 8)) ) (! (= ($shrBv64From8 src1@@48 src2@@40) (bvlshr src1@@48 (concat #x00000000000000 src2@@40)))
 :qid |outputbpl.3079:24|
 :skolemid |78|
 :pattern ( ($shrBv64From8 src1@@48 src2@@40))
)))
(assert (forall ((src1@@49 (_ BitVec 128)) (src2@@41 (_ BitVec 64)) ) (! (= ($shlBv128From64 src1@@49 src2@@41) (bvshl src1@@49 (concat #x0000000000000000 src2@@41)))
 :qid |outputbpl.3418:26|
 :skolemid |97|
 :pattern ( ($shlBv128From64 src1@@49 src2@@41))
)))
(assert (forall ((src1@@50 (_ BitVec 128)) (src2@@42 (_ BitVec 64)) ) (! (= ($shrBv128From64 src1@@50 src2@@42) (bvlshr src1@@50 (concat #x0000000000000000 src2@@42)))
 :qid |outputbpl.3433:26|
 :skolemid |98|
 :pattern ( ($shrBv128From64 src1@@50 src2@@42))
)))
(assert (forall ((src1@@51 (_ BitVec 128)) (src2@@43 (_ BitVec 32)) ) (! (= ($shlBv128From32 src1@@51 src2@@43) (bvshl src1@@51 (concat #x000000000000000000000000 src2@@43)))
 :qid |outputbpl.3381:26|
 :skolemid |95|
 :pattern ( ($shlBv128From32 src1@@51 src2@@43))
)))
(assert (forall ((src1@@52 (_ BitVec 128)) (src2@@44 (_ BitVec 32)) ) (! (= ($shrBv128From32 src1@@52 src2@@44) (bvlshr src1@@52 (concat #x000000000000000000000000 src2@@44)))
 :qid |outputbpl.3396:26|
 :skolemid |96|
 :pattern ( ($shrBv128From32 src1@@52 src2@@44))
)))
(assert (forall ((src1@@53 (_ BitVec 128)) (src2@@45 (_ BitVec 16)) ) (! (= ($shlBv128From16 src1@@53 src2@@45) (bvshl src1@@53 (concat #x0000000000000000000000000000 src2@@45)))
 :qid |outputbpl.3344:26|
 :skolemid |93|
 :pattern ( ($shlBv128From16 src1@@53 src2@@45))
)))
(assert (forall ((src1@@54 (_ BitVec 128)) (src2@@46 (_ BitVec 16)) ) (! (= ($shrBv128From16 src1@@54 src2@@46) (bvlshr src1@@54 (concat #x0000000000000000000000000000 src2@@46)))
 :qid |outputbpl.3359:26|
 :skolemid |94|
 :pattern ( ($shrBv128From16 src1@@54 src2@@46))
)))
(assert (forall ((src1@@55 (_ BitVec 128)) (src2@@47 (_ BitVec 8)) ) (! (= ($shlBv128From8 src1@@55 src2@@47) (bvshl src1@@55 (concat #x000000000000000000000000000000 src2@@47)))
 :qid |outputbpl.3307:25|
 :skolemid |91|
 :pattern ( ($shlBv128From8 src1@@55 src2@@47))
)))
(assert (forall ((src1@@56 (_ BitVec 128)) (src2@@48 (_ BitVec 8)) ) (! (= ($shrBv128From8 src1@@56 src2@@48) (bvlshr src1@@56 (concat #x000000000000000000000000000000 src2@@48)))
 :qid |outputbpl.3322:25|
 :skolemid |92|
 :pattern ( ($shrBv128From8 src1@@56 src2@@48))
)))
(assert (forall ((src1@@57 (_ BitVec 256)) (src2@@49 (_ BitVec 128)) ) (! (= ($shlBv256From128 src1@@57 src2@@49) (bvshl src1@@57 (concat #x00000000000000000000000000000000 src2@@49)))
 :qid |outputbpl.3678:27|
 :skolemid |112|
 :pattern ( ($shlBv256From128 src1@@57 src2@@49))
)))
(assert (forall ((src1@@58 (_ BitVec 256)) (src2@@50 (_ BitVec 128)) ) (! (= ($shrBv256From128 src1@@58 src2@@50) (bvlshr src1@@58 (concat #x00000000000000000000000000000000 src2@@50)))
 :qid |outputbpl.3693:27|
 :skolemid |113|
 :pattern ( ($shrBv256From128 src1@@58 src2@@50))
)))
(assert (forall ((src1@@59 (_ BitVec 256)) (src2@@51 (_ BitVec 64)) ) (! (= ($shlBv256From64 src1@@59 src2@@51) (bvshl src1@@59 (concat #x000000000000000000000000000000000000000000000000 src2@@51)))
 :qid |outputbpl.3641:26|
 :skolemid |110|
 :pattern ( ($shlBv256From64 src1@@59 src2@@51))
)))
(assert (forall ((src1@@60 (_ BitVec 256)) (src2@@52 (_ BitVec 64)) ) (! (= ($shrBv256From64 src1@@60 src2@@52) (bvlshr src1@@60 (concat #x000000000000000000000000000000000000000000000000 src2@@52)))
 :qid |outputbpl.3656:26|
 :skolemid |111|
 :pattern ( ($shrBv256From64 src1@@60 src2@@52))
)))
(assert (forall ((src1@@61 (_ BitVec 256)) (src2@@53 (_ BitVec 32)) ) (! (= ($shlBv256From32 src1@@61 src2@@53) (bvshl src1@@61 (concat #x00000000000000000000000000000000000000000000000000000000 src2@@53)))
 :qid |outputbpl.3599:26|
 :skolemid |107|
 :pattern ( ($shlBv256From32 src1@@61 src2@@53))
)))
(assert (forall ((src1@@62 (_ BitVec 256)) (src2@@54 (_ BitVec 32)) ) (! (= ($shrBv256From32 src1@@62 src2@@54) (bvlshr src1@@62 (concat #x00000000000000000000000000000000000000000000000000000000 src2@@54)))
 :qid |outputbpl.3614:26|
 :skolemid |108|
 :pattern ( ($shrBv256From32 src1@@62 src2@@54))
)))
(assert (forall ((src1@@63 (_ BitVec 256)) (src2@@55 (_ BitVec 16)) ) (! (= ($shlBv256From16 src1@@63 src2@@55) (bvshl src1@@63 (concat #x000000000000000000000000000000000000000000000000000000000000 src2@@55)))
 :qid |outputbpl.3562:26|
 :skolemid |105|
 :pattern ( ($shlBv256From16 src1@@63 src2@@55))
)))
(assert (forall ((src1@@64 (_ BitVec 256)) (src2@@56 (_ BitVec 16)) ) (! (= ($shrBv256From16 src1@@64 src2@@56) (bvlshr src1@@64 (concat #x000000000000000000000000000000000000000000000000000000000000 src2@@56)))
 :qid |outputbpl.3577:26|
 :skolemid |106|
 :pattern ( ($shrBv256From16 src1@@64 src2@@56))
)))
(assert (forall ((src1@@65 (_ BitVec 256)) (src2@@57 (_ BitVec 8)) ) (! (= ($shlBv256From8 src1@@65 src2@@57) (bvshl src1@@65 (concat #x00000000000000000000000000000000000000000000000000000000000000 src2@@57)))
 :qid |outputbpl.3533:25|
 :skolemid |103|
 :pattern ( ($shlBv256From8 src1@@65 src2@@57))
)))
(assert (forall ((src1@@66 (_ BitVec 256)) (src2@@58 (_ BitVec 8)) ) (! (= ($shrBv256From8 src1@@66 src2@@58) (bvlshr src1@@66 (concat #x00000000000000000000000000000000000000000000000000000000000000 src2@@58)))
 :qid |outputbpl.3544:25|
 :skolemid |104|
 :pattern ( ($shrBv256From8 src1@@66 src2@@58))
)))
(assert (forall ((s T@$bc_ProphecyBenchmark3Levels5Fields_Node1) ) (! (= (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node1'| s)  (and (and (and (and (and (and (and (|$IsValid'u64'| (|$v0#$bc_ProphecyBenchmark3Levels5Fields_Node1| s)) (|$IsValid'u64'| (|$v1#$bc_ProphecyBenchmark3Levels5Fields_Node1| s))) (|$IsValid'u64'| (|$v2#$bc_ProphecyBenchmark3Levels5Fields_Node1| s))) (|$IsValid'u64'| (|$v3#$bc_ProphecyBenchmark3Levels5Fields_Node1| s))) (|$IsValid'u64'| (|$v4#$bc_ProphecyBenchmark3Levels5Fields_Node1| s))) (|$IsValid'u64'| (|$v5#$bc_ProphecyBenchmark3Levels5Fields_Node1| s))) (|$IsValid'u64'| (|$v6#$bc_ProphecyBenchmark3Levels5Fields_Node1| s))) (|$IsValid'u64'| (|$v7#$bc_ProphecyBenchmark3Levels5Fields_Node1| s))))
 :qid |outputbpl.4311:62|
 :skolemid |132|
 :pattern ( (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node1'| s))
)))
(assert (forall ((s@@0 T@$bc_ProphecyBenchmark3Levels5Fields_Node2) ) (! (= (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node2'| s@@0)  (and (and (and (and (and (and (and (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node1'| (|$v0#$bc_ProphecyBenchmark3Levels5Fields_Node2| s@@0)) (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node1'| (|$v1#$bc_ProphecyBenchmark3Levels5Fields_Node2| s@@0))) (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node1'| (|$v2#$bc_ProphecyBenchmark3Levels5Fields_Node2| s@@0))) (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node1'| (|$v3#$bc_ProphecyBenchmark3Levels5Fields_Node2| s@@0))) (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node1'| (|$v4#$bc_ProphecyBenchmark3Levels5Fields_Node2| s@@0))) (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node1'| (|$v5#$bc_ProphecyBenchmark3Levels5Fields_Node2| s@@0))) (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node1'| (|$v6#$bc_ProphecyBenchmark3Levels5Fields_Node2| s@@0))) (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node1'| (|$v7#$bc_ProphecyBenchmark3Levels5Fields_Node2| s@@0))))
 :qid |outputbpl.4353:62|
 :skolemid |133|
 :pattern ( (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node2'| s@@0))
)))
(assert (forall ((s@@1 T@$bc_ProphecyBenchmark3Levels5Fields_Node3) ) (! (= (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node3'| s@@1)  (and (and (and (and (and (and (and (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node2'| (|$v0#$bc_ProphecyBenchmark3Levels5Fields_Node3| s@@1)) (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node2'| (|$v1#$bc_ProphecyBenchmark3Levels5Fields_Node3| s@@1))) (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node2'| (|$v2#$bc_ProphecyBenchmark3Levels5Fields_Node3| s@@1))) (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node2'| (|$v3#$bc_ProphecyBenchmark3Levels5Fields_Node3| s@@1))) (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node2'| (|$v4#$bc_ProphecyBenchmark3Levels5Fields_Node3| s@@1))) (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node2'| (|$v5#$bc_ProphecyBenchmark3Levels5Fields_Node3| s@@1))) (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node2'| (|$v6#$bc_ProphecyBenchmark3Levels5Fields_Node3| s@@1))) (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node2'| (|$v7#$bc_ProphecyBenchmark3Levels5Fields_Node3| s@@1))))
 :qid |outputbpl.4395:62|
 :skolemid |134|
 :pattern ( (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node3'| s@@1))
)))
(assert (forall ((src@@1 (_ BitVec 64)) ) (! (= ($castBv64to64 src@@1) src@@1)
 :qid |outputbpl.3174:24|
 :skolemid |83|
 :pattern ( ($castBv64to64 src@@1))
)))
(assert (forall ((src@@2 (_ BitVec 256)) ) (! (= ($castBv256to256 src@@2) src@@2)
 :qid |outputbpl.3714:26|
 :skolemid |114|
 :pattern ( ($castBv256to256 src@@2))
)))
(assert (forall ((src1@@67 (_ BitVec 8)) (src2@@59 (_ BitVec 8)) ) (! (= ($shlBv8From8 src1@@67 src2@@59) (bvshl src1@@67 src2@@59))
 :qid |outputbpl.2350:23|
 :skolemid |41|
 :pattern ( ($shlBv8From8 src1@@67 src2@@59))
)))
(assert (forall ((src1@@68 (_ BitVec 8)) (src2@@60 (_ BitVec 8)) ) (! (= ($shrBv8From8 src1@@68 src2@@60) (bvlshr src1@@68 src2@@60))
 :qid |outputbpl.2365:23|
 :skolemid |42|
 :pattern ( ($shrBv8From8 src1@@68 src2@@60))
)))
(assert (forall ((src1@@69 (_ BitVec 16)) (src2@@61 (_ BitVec 16)) ) (! (= ($shlBv16From16 src1@@69 src2@@61) (bvshl src1@@69 src2@@61))
 :qid |outputbpl.2629:25|
 :skolemid |55|
 :pattern ( ($shlBv16From16 src1@@69 src2@@61))
)))
(assert (forall ((src1@@70 (_ BitVec 16)) (src2@@62 (_ BitVec 16)) ) (! (= ($shrBv16From16 src1@@70 src2@@62) (bvlshr src1@@70 src2@@62))
 :qid |outputbpl.2644:25|
 :skolemid |56|
 :pattern ( ($shrBv16From16 src1@@70 src2@@62))
)))
(assert (forall ((src1@@71 (_ BitVec 32)) (src2@@63 (_ BitVec 32)) ) (! (= ($shlBv32From32 src1@@71 src2@@63) (bvshl src1@@71 src2@@63))
 :qid |outputbpl.2904:25|
 :skolemid |69|
 :pattern ( ($shlBv32From32 src1@@71 src2@@63))
)))
(assert (forall ((src1@@72 (_ BitVec 32)) (src2@@64 (_ BitVec 32)) ) (! (= ($shrBv32From32 src1@@72 src2@@64) (bvlshr src1@@72 src2@@64))
 :qid |outputbpl.2919:25|
 :skolemid |70|
 :pattern ( ($shrBv32From32 src1@@72 src2@@64))
)))
(assert (forall ((src1@@73 (_ BitVec 64)) (src2@@65 (_ BitVec 64)) ) (! (= ($shlBv64From64 src1@@73 src2@@65) (bvshl src1@@73 src2@@65))
 :qid |outputbpl.3180:25|
 :skolemid |84|
 :pattern ( ($shlBv64From64 src1@@73 src2@@65))
)))
(assert (forall ((src1@@74 (_ BitVec 64)) (src2@@66 (_ BitVec 64)) ) (! (= ($shrBv64From64 src1@@74 src2@@66) (bvlshr src1@@74 src2@@66))
 :qid |outputbpl.3195:25|
 :skolemid |85|
 :pattern ( ($shrBv64From64 src1@@74 src2@@66))
)))
(assert (forall ((src1@@75 (_ BitVec 128)) (src2@@67 (_ BitVec 128)) ) (! (= ($shlBv128From128 src1@@75 src2@@67) (bvshl src1@@75 src2@@67))
 :qid |outputbpl.3455:27|
 :skolemid |99|
 :pattern ( ($shlBv128From128 src1@@75 src2@@67))
)))
(assert (forall ((src1@@76 (_ BitVec 128)) (src2@@68 (_ BitVec 128)) ) (! (= ($shrBv128From128 src1@@76 src2@@68) (bvlshr src1@@76 src2@@68))
 :qid |outputbpl.3470:27|
 :skolemid |100|
 :pattern ( ($shrBv128From128 src1@@76 src2@@68))
)))
(assert (forall ((src1@@77 (_ BitVec 256)) (src2@@69 (_ BitVec 256)) ) (! (= ($shlBv256From256 src1@@77 src2@@69) (bvshl src1@@77 src2@@69))
 :qid |outputbpl.3720:27|
 :skolemid |115|
 :pattern ( ($shlBv256From256 src1@@77 src2@@69))
)))
(assert (forall ((src1@@78 (_ BitVec 256)) (src2@@70 (_ BitVec 256)) ) (! (= ($shrBv256From256 src1@@78 src2@@70) (bvlshr src1@@78 src2@@70))
 :qid |outputbpl.3735:27|
 :skolemid |116|
 :pattern ( ($shrBv256From256 src1@@78 src2@@70))
)))
(assert (forall ((k1@@0 T@Vec_11000) (k2@@0 T@Vec_11000) ) (!  (=> (|$IsEqual'vec'u8''| k1@@0 k2@@0) (= ($1_Signature_$ed25519_validate_pubkey k1@@0) ($1_Signature_$ed25519_validate_pubkey k2@@0)))
 :qid |outputbpl.4215:15|
 :skolemid |130|
 :pattern ( ($1_Signature_$ed25519_validate_pubkey k1@@0) ($1_Signature_$ed25519_validate_pubkey k2@@0))
)))
(assert (forall ((v@@6 (_ BitVec 8)) ) (! (= (|$IsValid'bv8'| v@@6)  (and (bvuge v@@6 #x00) (bvule v@@6 #xff)))
 :qid |outputbpl.1379:24|
 :skolemid |29|
 :pattern ( (|$IsValid'bv8'| v@@6))
)))
(assert (forall ((v@@7 (_ BitVec 64)) ) (! (= (|$IsValid'bv64'| v@@7)  (and (bvuge v@@7 #x0000000000000000) (bvule v@@7 #xffffffffffffffff)))
 :qid |outputbpl.1754:25|
 :skolemid |32|
 :pattern ( (|$IsValid'bv64'| v@@7))
)))
(assert (forall ((v@@8 (_ BitVec 16)) ) (! (= (|$IsValid'bv16'| v@@8)  (and (bvuge v@@8 #x0000) (bvule v@@8 #xffff)))
 :qid |outputbpl.1504:25|
 :skolemid |30|
 :pattern ( (|$IsValid'bv16'| v@@8))
)))
(assert (forall ((v@@9 (_ BitVec 256)) ) (! (= (|$IsValid'bv256'| v@@9)  (and (bvuge v@@9 #x0000000000000000000000000000000000000000000000000000000000000000) (bvule v@@9 #xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)))
 :qid |outputbpl.2004:26|
 :skolemid |34|
 :pattern ( (|$IsValid'bv256'| v@@9))
)))
(assert (forall ((v@@10 T@Vec_11000) (e@@1 Int) ) (! (let ((i@@8 (|$IndexOfVec'u8'| v@@10 e@@1)))
(ite  (not (exists ((i@@9 Int) ) (!  (and (and (|$IsValid'u64'| i@@9) (InRangeVec_19336 v@@10 i@@9)) (= (|Select__T@[Int]Int_| (|v#Vec_11000| v@@10) i@@9) e@@1))
 :qid |outputbpl.3789:13|
 :skolemid |125|
))) (= i@@8 (- 0 1))  (and (and (and (|$IsValid'u64'| i@@8) (InRangeVec_19336 v@@10 i@@8)) (= (|Select__T@[Int]Int_| (|v#Vec_11000| v@@10) i@@8) e@@1)) (forall ((j@@1 Int) ) (!  (=> (and (and (|$IsValid'u64'| j@@1) (>= j@@1 0)) (< j@@1 i@@8)) (not (= (|Select__T@[Int]Int_| (|v#Vec_11000| v@@10) j@@1) e@@1)))
 :qid |outputbpl.3797:17|
 :skolemid |126|
)))))
 :qid |outputbpl.3793:15|
 :skolemid |127|
 :pattern ( (|$IndexOfVec'u8'| v@@10 e@@1))
)))
(assert (forall ((v@@11 (_ BitVec 128)) ) (! (= (|$IsValid'bv128'| v@@11)  (and (bvuge v@@11 #x00000000000000000000000000000000) (bvule v@@11 #xffffffffffffffffffffffffffffffff)))
 :qid |outputbpl.1879:26|
 :skolemid |33|
 :pattern ( (|$IsValid'bv128'| v@@11))
)))
(assert (forall ((v1@@0 T@Vec_11000) (v2@@0 T@Vec_11000) ) (! (= (|$IsEqual'vec'u8''| v1@@0 v2@@0) (|$IsEqual'vec'u8''| ($1_hash_sha2 v1@@0) ($1_hash_sha2 v2@@0)))
 :qid |outputbpl.4090:15|
 :skolemid |128|
 :pattern ( ($1_hash_sha2 v1@@0) ($1_hash_sha2 v2@@0))
)))
(assert (forall ((v1@@1 T@Vec_11000) (v2@@1 T@Vec_11000) ) (! (= (|$IsEqual'vec'u8''| v1@@1 v2@@1) (|$IsEqual'vec'u8''| ($1_hash_sha3 v1@@1) ($1_hash_sha3 v2@@1)))
 :qid |outputbpl.4106:15|
 :skolemid |129|
 :pattern ( ($1_hash_sha3 v1@@1) ($1_hash_sha3 v2@@1))
)))
(assert (forall ((v@@12 Int) ) (! (= (|$IsValid'u8'| v@@12)  (and (>= v@@12 $MIN_U8) (<= v@@12 $MAX_U8)))
 :qid |outputbpl.287:23|
 :skolemid |8|
 :pattern ( (|$IsValid'u8'| v@@12))
)))
(assert (forall ((v@@13 Int) ) (! (= (|$IsValid'u16'| v@@13)  (and (>= v@@13 $MIN_U16) (<= v@@13 $MAX_U16)))
 :qid |outputbpl.342:24|
 :skolemid |9|
 :pattern ( (|$IsValid'u16'| v@@13))
)))
(assert (forall ((v@@14 Int) ) (! (= (|$IsValid'u32'| v@@14)  (and (>= v@@14 $MIN_U32) (<= v@@14 $MAX_U32)))
 :qid |outputbpl.397:24|
 :skolemid |10|
 :pattern ( (|$IsValid'u32'| v@@14))
)))
(assert (forall ((v@@15 Int) ) (! (= (|$IsValid'u64'| v@@15)  (and (>= v@@15 $MIN_U64) (<= v@@15 $MAX_U64)))
 :qid |outputbpl.452:24|
 :skolemid |11|
 :pattern ( (|$IsValid'u64'| v@@15))
)))
(assert (forall ((v@@16 Int) ) (! (= (|$IsValid'u128'| v@@16)  (and (>= v@@16 $MIN_U128) (<= v@@16 $MAX_U128)))
 :qid |outputbpl.507:25|
 :skolemid |12|
 :pattern ( (|$IsValid'u128'| v@@16))
)))
(assert (forall ((v@@17 Int) ) (! (= (|$IsValid'u256'| v@@17)  (and (>= v@@17 $MIN_U256) (<= v@@17 $MAX_U256)))
 :qid |outputbpl.562:25|
 :skolemid |13|
 :pattern ( (|$IsValid'u256'| v@@17))
)))
(assert (forall ((v@@18 Int) ) (! (= (|$IsValid'i8'| v@@18)  (and (>= v@@18 $MIN_I8) (<= v@@18 $MAX_I8)))
 :qid |outputbpl.617:23|
 :skolemid |14|
 :pattern ( (|$IsValid'i8'| v@@18))
)))
(assert (forall ((v@@19 Int) ) (! (= (|$IsValid'i16'| v@@19)  (and (>= v@@19 $MIN_I16) (<= v@@19 $MAX_I16)))
 :qid |outputbpl.672:24|
 :skolemid |15|
 :pattern ( (|$IsValid'i16'| v@@19))
)))
(assert (forall ((v@@20 Int) ) (! (= (|$IsValid'i32'| v@@20)  (and (>= v@@20 $MIN_I32) (<= v@@20 $MAX_I32)))
 :qid |outputbpl.727:24|
 :skolemid |16|
 :pattern ( (|$IsValid'i32'| v@@20))
)))
(assert (forall ((v@@21 Int) ) (! (= (|$IsValid'i64'| v@@21)  (and (>= v@@21 $MIN_I64) (<= v@@21 $MAX_I64)))
 :qid |outputbpl.782:24|
 :skolemid |17|
 :pattern ( (|$IsValid'i64'| v@@21))
)))
(assert (forall ((v@@22 Int) ) (! (= (|$IsValid'i128'| v@@22)  (and (>= v@@22 $MIN_I128) (<= v@@22 $MAX_I128)))
 :qid |outputbpl.837:25|
 :skolemid |18|
 :pattern ( (|$IsValid'i128'| v@@22))
)))
(assert (forall ((v@@23 Int) ) (! (= (|$IsValid'i256'| v@@23)  (and (>= v@@23 $MIN_I256) (<= v@@23 $MAX_I256)))
 :qid |outputbpl.892:25|
 :skolemid |19|
 :pattern ( (|$IsValid'i256'| v@@23))
)))
(assert (forall ((v@@24 T@Vec_11000) (i@@10 Int) ) (! (= (InRangeVec_19336 v@@24 i@@10)  (and (>= i@@10 0) (< i@@10 (|l#Vec_11000| v@@24))))
 :qid |outputbpl.123:24|
 :skolemid |3|
 :pattern ( (InRangeVec_19336 v@@24 i@@10))
)))
(assert (forall ((r T@$Range) (i@@11 Int) ) (! (= ($InRange r i@@11)  (and (<= (|lb#$Range| r) i@@11) (< i@@11 (|ub#$Range| r))))
 :qid |outputbpl.2051:19|
 :skolemid |37|
 :pattern ( ($InRange r i@@11))
)))
(assert (= $MAX_U32 4294967295))
(assert (= $MIN_U8 0))
(assert (= $MIN_U16 0))
(assert (= $MIN_U32 0))
(assert (= $MIN_U64 0))
(assert (= $MIN_U128 0))
(assert (= $MIN_U256 0))
(assert (= $MAX_I8 127))
(assert (= $MAX_U8 255))
(assert (= $MAX_U64 18446744073709551615))
(assert (= $MAX_I64 9223372036854775807))
(assert (= $MAX_I16 32767))
(assert (= $MAX_U16 65535))
(assert (= $MAX_U256 115792089237316195423570985008687907853269984665640564039457584007913129639935))
(assert (= $MAX_I256 57896044618658097711785492504343953926634992332820282019728792003956564819967))
(assert (= $EXEC_FAILURE_CODE (- 0 1)))
(assert (= $MIN_I8 (- 0 128)))
(assert (= $MIN_I64 (- 0 9223372036854775808)))
(assert (= $MIN_I16 (- 0 32768)))
(assert (= $MIN_I256 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)))
(push 1)
(declare-fun ControlFlow (Int Int) Int)
(set-info :boogie-vc-id $bc_ProphecyBenchmark3Levels5Fields_new_node2$verify)
(set-option :timeout 40000)
(set-option :rlimit 0)
(set-option :model_validate true)
(set-option :smt.QI.EAGER_THRESHOLD 100)
(set-option :smt.QI.LAZY_THRESHOLD 100)
(set-option :smt.random_seed 1)
(set-option :smt.mbqi false)
(set-option :model.compact false)
(set-option :model.v2 true)
(set-option :pp.bv_literals false)
(assert (not
 (=> (= (ControlFlow 0 0) 28) true)
))
(check-sat)
(get-info :rlimit)
(pop 1)
; Valid
(reset)
(set-option :print-success false)
(set-info :smt-lib-version 2.6)
(set-option :produce-models true)
(set-option :model_validate true)
(set-option :smt.QI.EAGER_THRESHOLD 100)
(set-option :smt.QI.LAZY_THRESHOLD 100)
(set-option :smt.random_seed 1)
(set-option :smt.mbqi false)
(set-option :model.compact false)
(set-option :model.v2 true)
(set-option :pp.bv_literals false)
; done setting options


(declare-fun tickleBool (Bool) Bool)
(assert (and (tickleBool true) (tickleBool false)))
(declare-sort |T@[Int]Int| 0)
(declare-sort T@T_11045 0)
(declare-sort T@T2_11239 0)
(declare-datatypes ((T@$bc_ProphecyBenchmark3Levels5Fields_Node1 0)) ((($bc_ProphecyBenchmark3Levels5Fields_Node1 (|$v0#$bc_ProphecyBenchmark3Levels5Fields_Node1| Int) (|$v1#$bc_ProphecyBenchmark3Levels5Fields_Node1| Int) (|$v2#$bc_ProphecyBenchmark3Levels5Fields_Node1| Int) (|$v3#$bc_ProphecyBenchmark3Levels5Fields_Node1| Int) (|$v4#$bc_ProphecyBenchmark3Levels5Fields_Node1| Int) (|$v5#$bc_ProphecyBenchmark3Levels5Fields_Node1| Int) (|$v6#$bc_ProphecyBenchmark3Levels5Fields_Node1| Int) (|$v7#$bc_ProphecyBenchmark3Levels5Fields_Node1| Int) ) ) ))
(declare-datatypes ((T@$bc_ProphecyBenchmark3Levels5Fields_Node2 0)) ((($bc_ProphecyBenchmark3Levels5Fields_Node2 (|$v0#$bc_ProphecyBenchmark3Levels5Fields_Node2| T@$bc_ProphecyBenchmark3Levels5Fields_Node1) (|$v1#$bc_ProphecyBenchmark3Levels5Fields_Node2| T@$bc_ProphecyBenchmark3Levels5Fields_Node1) (|$v2#$bc_ProphecyBenchmark3Levels5Fields_Node2| T@$bc_ProphecyBenchmark3Levels5Fields_Node1) (|$v3#$bc_ProphecyBenchmark3Levels5Fields_Node2| T@$bc_ProphecyBenchmark3Levels5Fields_Node1) (|$v4#$bc_ProphecyBenchmark3Levels5Fields_Node2| T@$bc_ProphecyBenchmark3Levels5Fields_Node1) (|$v5#$bc_ProphecyBenchmark3Levels5Fields_Node2| T@$bc_ProphecyBenchmark3Levels5Fields_Node1) (|$v6#$bc_ProphecyBenchmark3Levels5Fields_Node2| T@$bc_ProphecyBenchmark3Levels5Fields_Node1) (|$v7#$bc_ProphecyBenchmark3Levels5Fields_Node2| T@$bc_ProphecyBenchmark3Levels5Fields_Node1) ) ) ))
(declare-datatypes ((T@$bc_ProphecyBenchmark3Levels5Fields_Node3 0)) ((($bc_ProphecyBenchmark3Levels5Fields_Node3 (|$v0#$bc_ProphecyBenchmark3Levels5Fields_Node3| T@$bc_ProphecyBenchmark3Levels5Fields_Node2) (|$v1#$bc_ProphecyBenchmark3Levels5Fields_Node3| T@$bc_ProphecyBenchmark3Levels5Fields_Node2) (|$v2#$bc_ProphecyBenchmark3Levels5Fields_Node3| T@$bc_ProphecyBenchmark3Levels5Fields_Node2) (|$v3#$bc_ProphecyBenchmark3Levels5Fields_Node3| T@$bc_ProphecyBenchmark3Levels5Fields_Node2) (|$v4#$bc_ProphecyBenchmark3Levels5Fields_Node3| T@$bc_ProphecyBenchmark3Levels5Fields_Node2) (|$v5#$bc_ProphecyBenchmark3Levels5Fields_Node3| T@$bc_ProphecyBenchmark3Levels5Fields_Node2) (|$v6#$bc_ProphecyBenchmark3Levels5Fields_Node3| T@$bc_ProphecyBenchmark3Levels5Fields_Node2) (|$v7#$bc_ProphecyBenchmark3Levels5Fields_Node3| T@$bc_ProphecyBenchmark3Levels5Fields_Node2) ) ) ))
(declare-datatypes ((T@Vec_11000 0)) (((Vec_11000 (|v#Vec_11000| |T@[Int]Int|) (|l#Vec_11000| Int) ) ) ))
(declare-datatypes ((T@$TypeParamInfo 0)) ((($TypeParamBool ) ($TypeParamU8 ) ($TypeParamU16 ) ($TypeParamU32 ) ($TypeParamU64 ) ($TypeParamU128 ) ($TypeParamU256 ) ($TypeParamI8 ) ($TypeParamI16 ) ($TypeParamI32 ) ($TypeParamI64 ) ($TypeParamI128 ) ($TypeParamI256 ) ($TypeParamAddress ) ($TypeParamSigner ) ($TypeParamVector (|e#$TypeParamVector| T@$TypeParamInfo) ) ($TypeParamStruct (|a#$TypeParamStruct| Int) (|m#$TypeParamStruct| T@Vec_11000) (|s#$TypeParamStruct| T@Vec_11000) ) ) ))
(declare-datatypes ((T@$signer 0)) ((($signer (|$addr#$signer| Int) ) ($permissioned_signer (|$addr#$permissioned_signer| Int) (|$permission_addr#$permissioned_signer| Int) ) ) ))
(declare-datatypes ((T@$Location 0)) ((($Global (|a#$Global| Int) ) ($Local (|i#$Local| Int) ) ($Param (|i#$Param| Int) ) ($Uninitialized ) ) ))
(declare-datatypes ((T@$Mutation_49963 0)) ((($Mutation_49963 (|l#$Mutation_49963| T@$Location) (|p#$Mutation_49963| T@Vec_11000) (|v#$Mutation_49963| T@$bc_ProphecyBenchmark3Levels5Fields_Node1) (|v_final#$Mutation_49963| T@$bc_ProphecyBenchmark3Levels5Fields_Node1) ) ) ))
(declare-datatypes ((T@$Mutation_49940 0)) ((($Mutation_49940 (|l#$Mutation_49940| T@$Location) (|p#$Mutation_49940| T@Vec_11000) (|v#$Mutation_49940| T@$bc_ProphecyBenchmark3Levels5Fields_Node2) (|v_final#$Mutation_49940| T@$bc_ProphecyBenchmark3Levels5Fields_Node2) ) ) ))
(declare-datatypes ((T@$Mutation_49917 0)) ((($Mutation_49917 (|l#$Mutation_49917| T@$Location) (|p#$Mutation_49917| T@Vec_11000) (|v#$Mutation_49917| T@$bc_ProphecyBenchmark3Levels5Fields_Node3) (|v_final#$Mutation_49917| T@$bc_ProphecyBenchmark3Levels5Fields_Node3) ) ) ))
(declare-datatypes ((T@$Mutation_20877 0)) ((($Mutation_20877 (|l#$Mutation_20877| T@$Location) (|p#$Mutation_20877| T@Vec_11000) (|v#$Mutation_20877| Int) (|v_final#$Mutation_20877| Int) ) ) ))
(declare-datatypes ((T@$Mutation_44127 0)) ((($Mutation_44127 (|l#$Mutation_44127| T@$Location) (|p#$Mutation_44127| T@Vec_11000) (|v#$Mutation_44127| T@Vec_11000) (|v_final#$Mutation_44127| T@Vec_11000) ) ) ))
(declare-datatypes ((T@$Mutation_31641 0)) ((($Mutation_31641 (|l#$Mutation_31641| T@$Location) (|p#$Mutation_31641| T@Vec_11000) (|v#$Mutation_31641| T@T2_11239) (|v_final#$Mutation_31641| T@T2_11239) ) ) ))
(declare-datatypes ((T@$Mutation_31508 0)) ((($Mutation_31508 (|l#$Mutation_31508| T@$Location) (|p#$Mutation_31508| T@Vec_11000) (|v#$Mutation_31508| T@T_11045) (|v_final#$Mutation_31508| T@T_11045) ) ) ))
(declare-datatypes ((T@$Range 0)) ((($Range (|lb#$Range| Int) (|ub#$Range| Int) ) ) ))
(declare-fun $MAX_U128 () Int)
(declare-fun $MAX_I128 () Int)
(declare-fun $MIN_I128 () Int)
(declare-fun |Select__T@[Int]Int_| (|T@[Int]Int| Int) Int)
(declare-fun |lambda#1| (Int Int |T@[Int]Int| Int Int Int) |T@[Int]Int|)
(declare-fun $shr (Int Int) Int)
(declare-fun $pow (Int Int) Int)
(declare-fun $shlU8 (Int Int) Int)
(declare-fun $MAX_U8 () Int)
(declare-fun $shlU16 (Int Int) Int)
(declare-fun $MAX_U16 () Int)
(declare-fun $shlU32 (Int Int) Int)
(declare-fun $MAX_U32 () Int)
(declare-fun $shlU64 (Int Int) Int)
(declare-fun $MAX_U64 () Int)
(declare-fun $shlU128 (Int Int) Int)
(declare-fun $shlU256 (Int Int) Int)
(declare-fun $MAX_U256 () Int)
(declare-sort |T@[Int]Bool| 0)
(declare-fun $ConstMemoryDomain (Bool) |T@[Int]Bool|)
(declare-fun |lambda#4| (Bool) |T@[Int]Bool|)
(declare-fun |$IsEqual'vec'u8''| (T@Vec_11000 T@Vec_11000) Bool)
(declare-fun InRangeVec_19336 (T@Vec_11000 Int) Bool)
(declare-fun |$IsPrefix'vec'u8''| (T@Vec_11000 T@Vec_11000) Bool)
(declare-fun DefaultTableKeyExistsArray_990 () |T@[Int]Bool|)
(declare-fun IndexOfVec_11000 (T@Vec_11000 Int) Int)
(declare-fun $1_Signature_$ed25519_verify (T@Vec_11000 T@Vec_11000 T@Vec_11000) Bool)
(declare-fun |lambda#0| (Int Int Int |T@[Int]Int| |T@[Int]Int| Int Int) |T@[Int]Int|)
(declare-fun |lambda#3| (Int Int Int |T@[Int]Int| |T@[Int]Int| Int Int) |T@[Int]Int|)
(declare-fun |$IsValid'bv32'| ((_ BitVec 32)) Bool)
(declare-fun |$IsValid'address'| (Int) Bool)
(declare-fun |$IsSuffix'vec'u8''| (T@Vec_11000 T@Vec_11000) Bool)
(declare-fun |lambda#2| (Int Int |T@[Int]Int| Int Int) |T@[Int]Int|)
(declare-fun $shl (Int Int) Int)
(declare-fun $castBv256to64 ((_ BitVec 256)) (_ BitVec 64))
(declare-fun |$Arbitrary_value_of'bv64'| () (_ BitVec 64))
(declare-fun $MAX_I32 () Int)
(declare-fun $MIN_I32 () Int)
(declare-fun $shlBv8From16 ((_ BitVec 8) (_ BitVec 16)) (_ BitVec 8))
(declare-fun $shrBv8From16 ((_ BitVec 8) (_ BitVec 16)) (_ BitVec 8))
(declare-fun $shlBv8From32 ((_ BitVec 8) (_ BitVec 32)) (_ BitVec 8))
(declare-fun $shrBv8From32 ((_ BitVec 8) (_ BitVec 32)) (_ BitVec 8))
(declare-fun $shlBv8From64 ((_ BitVec 8) (_ BitVec 64)) (_ BitVec 8))
(declare-fun $shrBv8From64 ((_ BitVec 8) (_ BitVec 64)) (_ BitVec 8))
(declare-fun $shlBv8From128 ((_ BitVec 8) (_ BitVec 128)) (_ BitVec 8))
(declare-fun $shrBv8From128 ((_ BitVec 8) (_ BitVec 128)) (_ BitVec 8))
(declare-fun $shlBv8From256 ((_ BitVec 8) (_ BitVec 256)) (_ BitVec 8))
(declare-fun $shrBv8From256 ((_ BitVec 8) (_ BitVec 256)) (_ BitVec 8))
(declare-fun $shlBv16From32 ((_ BitVec 16) (_ BitVec 32)) (_ BitVec 16))
(declare-fun $shrBv16From32 ((_ BitVec 16) (_ BitVec 32)) (_ BitVec 16))
(declare-fun $shlBv16From64 ((_ BitVec 16) (_ BitVec 64)) (_ BitVec 16))
(declare-fun $shrBv16From64 ((_ BitVec 16) (_ BitVec 64)) (_ BitVec 16))
(declare-fun $shlBv16From128 ((_ BitVec 16) (_ BitVec 128)) (_ BitVec 16))
(declare-fun $shrBv16From128 ((_ BitVec 16) (_ BitVec 128)) (_ BitVec 16))
(declare-fun $shlBv16From256 ((_ BitVec 16) (_ BitVec 256)) (_ BitVec 16))
(declare-fun $shrBv16From256 ((_ BitVec 16) (_ BitVec 256)) (_ BitVec 16))
(declare-fun $shlBv32From64 ((_ BitVec 32) (_ BitVec 64)) (_ BitVec 32))
(declare-fun $shrBv32From64 ((_ BitVec 32) (_ BitVec 64)) (_ BitVec 32))
(declare-fun $shlBv32From128 ((_ BitVec 32) (_ BitVec 128)) (_ BitVec 32))
(declare-fun $shrBv32From128 ((_ BitVec 32) (_ BitVec 128)) (_ BitVec 32))
(declare-fun $shlBv32From256 ((_ BitVec 32) (_ BitVec 256)) (_ BitVec 32))
(declare-fun $shrBv32From256 ((_ BitVec 32) (_ BitVec 256)) (_ BitVec 32))
(declare-fun $shlBv64From128 ((_ BitVec 64) (_ BitVec 128)) (_ BitVec 64))
(declare-fun $shrBv64From128 ((_ BitVec 64) (_ BitVec 128)) (_ BitVec 64))
(declare-fun $shlBv64From256 ((_ BitVec 64) (_ BitVec 256)) (_ BitVec 64))
(declare-fun $shrBv64From256 ((_ BitVec 64) (_ BitVec 256)) (_ BitVec 64))
(declare-fun $shlBv128From256 ((_ BitVec 128) (_ BitVec 256)) (_ BitVec 128))
(declare-fun $shrBv128From256 ((_ BitVec 128) (_ BitVec 256)) (_ BitVec 128))
(declare-fun |$IsValid'vec'u8''| (T@Vec_11000) Bool)
(declare-fun |$IsValid'u64'| (Int) Bool)
(declare-fun |$IsValid'u8'| (Int) Bool)
(declare-fun |Select__T@[Int]Bool_| (|T@[Int]Bool| Int) Bool)
(declare-fun |$IsValid'num'| (Int) Bool)
(declare-fun $castBv64to256 ((_ BitVec 64)) (_ BitVec 256))
(declare-fun $undefined_int () Int)
(declare-fun $shlBv16From8 ((_ BitVec 16) (_ BitVec 8)) (_ BitVec 16))
(declare-fun $shrBv16From8 ((_ BitVec 16) (_ BitVec 8)) (_ BitVec 16))
(declare-fun $shlBv32From16 ((_ BitVec 32) (_ BitVec 16)) (_ BitVec 32))
(declare-fun $shrBv32From16 ((_ BitVec 32) (_ BitVec 16)) (_ BitVec 32))
(declare-fun $shlBv32From8 ((_ BitVec 32) (_ BitVec 8)) (_ BitVec 32))
(declare-fun $shrBv32From8 ((_ BitVec 32) (_ BitVec 8)) (_ BitVec 32))
(declare-fun $shlBv64From32 ((_ BitVec 64) (_ BitVec 32)) (_ BitVec 64))
(declare-fun $shrBv64From32 ((_ BitVec 64) (_ BitVec 32)) (_ BitVec 64))
(declare-fun $shlBv64From16 ((_ BitVec 64) (_ BitVec 16)) (_ BitVec 64))
(declare-fun $shrBv64From16 ((_ BitVec 64) (_ BitVec 16)) (_ BitVec 64))
(declare-fun $shlBv64From8 ((_ BitVec 64) (_ BitVec 8)) (_ BitVec 64))
(declare-fun $shrBv64From8 ((_ BitVec 64) (_ BitVec 8)) (_ BitVec 64))
(declare-fun $shlBv128From64 ((_ BitVec 128) (_ BitVec 64)) (_ BitVec 128))
(declare-fun $shrBv128From64 ((_ BitVec 128) (_ BitVec 64)) (_ BitVec 128))
(declare-fun $shlBv128From32 ((_ BitVec 128) (_ BitVec 32)) (_ BitVec 128))
(declare-fun $shrBv128From32 ((_ BitVec 128) (_ BitVec 32)) (_ BitVec 128))
(declare-fun $shlBv128From16 ((_ BitVec 128) (_ BitVec 16)) (_ BitVec 128))
(declare-fun $shrBv128From16 ((_ BitVec 128) (_ BitVec 16)) (_ BitVec 128))
(declare-fun $shlBv128From8 ((_ BitVec 128) (_ BitVec 8)) (_ BitVec 128))
(declare-fun $shrBv128From8 ((_ BitVec 128) (_ BitVec 8)) (_ BitVec 128))
(declare-fun $shlBv256From128 ((_ BitVec 256) (_ BitVec 128)) (_ BitVec 256))
(declare-fun $shrBv256From128 ((_ BitVec 256) (_ BitVec 128)) (_ BitVec 256))
(declare-fun $shlBv256From64 ((_ BitVec 256) (_ BitVec 64)) (_ BitVec 256))
(declare-fun $shrBv256From64 ((_ BitVec 256) (_ BitVec 64)) (_ BitVec 256))
(declare-fun $shlBv256From32 ((_ BitVec 256) (_ BitVec 32)) (_ BitVec 256))
(declare-fun $shrBv256From32 ((_ BitVec 256) (_ BitVec 32)) (_ BitVec 256))
(declare-fun $shlBv256From16 ((_ BitVec 256) (_ BitVec 16)) (_ BitVec 256))
(declare-fun $shrBv256From16 ((_ BitVec 256) (_ BitVec 16)) (_ BitVec 256))
(declare-fun $shlBv256From8 ((_ BitVec 256) (_ BitVec 8)) (_ BitVec 256))
(declare-fun $shrBv256From8 ((_ BitVec 256) (_ BitVec 8)) (_ BitVec 256))
(declare-fun |$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node1'| (T@$bc_ProphecyBenchmark3Levels5Fields_Node1) Bool)
(declare-fun |$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node2'| (T@$bc_ProphecyBenchmark3Levels5Fields_Node2) Bool)
(declare-fun |$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node3'| (T@$bc_ProphecyBenchmark3Levels5Fields_Node3) Bool)
(declare-fun $castBv64to64 ((_ BitVec 64)) (_ BitVec 64))
(declare-fun $castBv256to256 ((_ BitVec 256)) (_ BitVec 256))
(declare-fun $shlBv8From8 ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
(declare-fun $shrBv8From8 ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
(declare-fun $shlBv16From16 ((_ BitVec 16) (_ BitVec 16)) (_ BitVec 16))
(declare-fun $shrBv16From16 ((_ BitVec 16) (_ BitVec 16)) (_ BitVec 16))
(declare-fun $shlBv32From32 ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))
(declare-fun $shrBv32From32 ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))
(declare-fun $shlBv64From64 ((_ BitVec 64) (_ BitVec 64)) (_ BitVec 64))
(declare-fun $shrBv64From64 ((_ BitVec 64) (_ BitVec 64)) (_ BitVec 64))
(declare-fun $shlBv128From128 ((_ BitVec 128) (_ BitVec 128)) (_ BitVec 128))
(declare-fun $shrBv128From128 ((_ BitVec 128) (_ BitVec 128)) (_ BitVec 128))
(declare-fun $shlBv256From256 ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))
(declare-fun $shrBv256From256 ((_ BitVec 256) (_ BitVec 256)) (_ BitVec 256))
(declare-fun $1_Signature_$ed25519_validate_pubkey (T@Vec_11000) Bool)
(declare-fun |$IsValid'bv8'| ((_ BitVec 8)) Bool)
(declare-fun |$IsValid'bv64'| ((_ BitVec 64)) Bool)
(declare-fun |$IsValid'bv16'| ((_ BitVec 16)) Bool)
(declare-fun |$IsValid'bv256'| ((_ BitVec 256)) Bool)
(declare-fun |$IndexOfVec'u8'| (T@Vec_11000 Int) Int)
(declare-fun |$IsValid'bv128'| ((_ BitVec 128)) Bool)
(declare-fun $1_hash_sha2 (T@Vec_11000) T@Vec_11000)
(declare-fun $1_hash_sha3 (T@Vec_11000) T@Vec_11000)
(declare-fun $MIN_U8 () Int)
(declare-fun |$IsValid'u16'| (Int) Bool)
(declare-fun $MIN_U16 () Int)
(declare-fun |$IsValid'u32'| (Int) Bool)
(declare-fun $MIN_U32 () Int)
(declare-fun $MIN_U64 () Int)
(declare-fun |$IsValid'u128'| (Int) Bool)
(declare-fun $MIN_U128 () Int)
(declare-fun |$IsValid'u256'| (Int) Bool)
(declare-fun $MIN_U256 () Int)
(declare-fun |$IsValid'i8'| (Int) Bool)
(declare-fun $MIN_I8 () Int)
(declare-fun $MAX_I8 () Int)
(declare-fun |$IsValid'i16'| (Int) Bool)
(declare-fun $MIN_I16 () Int)
(declare-fun $MAX_I16 () Int)
(declare-fun |$IsValid'i32'| (Int) Bool)
(declare-fun |$IsValid'i64'| (Int) Bool)
(declare-fun $MIN_I64 () Int)
(declare-fun $MAX_I64 () Int)
(declare-fun |$IsValid'i128'| (Int) Bool)
(declare-fun |$IsValid'i256'| (Int) Bool)
(declare-fun $MIN_I256 () Int)
(declare-fun $MAX_I256 () Int)
(declare-fun $InRange (T@$Range Int) Bool)
(declare-fun $EXEC_FAILURE_CODE () Int)
(assert (= $MAX_U128 340282366920938463463374607431768211455))
(assert (= $MAX_I128 170141183460469231731687303715884105727))
(assert (= $MIN_I128 (- 0 170141183460469231731687303715884105728)))
(assert (forall ((|l#0| Int) (|l#1| Int) (|l#2| |T@[Int]Int|) (|l#3| Int) (|l#4| Int) (|l#5| Int) (i Int) ) (! (= (|Select__T@[Int]Int_| (|lambda#1| |l#0| |l#1| |l#2| |l#3| |l#4| |l#5|) i) (ite  (and (<= |l#0| i) (< i |l#1|)) (|Select__T@[Int]Int_| |l#2| (- (- |l#3| i) |l#4|)) |l#5|))
 :qid |outputbpl.83:30|
 :skolemid |136|
 :pattern ( (|Select__T@[Int]Int_| (|lambda#1| |l#0| |l#1| |l#2| |l#3| |l#4| |l#5|) i))
)))
(assert (forall ((src1 Int) (p Int) ) (! (= ($shr src1 p) (div src1 ($pow 2 p)))
 :qid |outputbpl.982:15|
 :skolemid |22|
 :pattern ( ($shr src1 p))
)))
(assert (forall ((src1@@0 Int) (p@@0 Int) ) (! (= ($shlU8 src1@@0 p@@0) (mod (* src1@@0 ($pow 2 p@@0)) (+ $MAX_U8 1)))
 :qid |outputbpl.997:17|
 :skolemid |23|
 :pattern ( ($shlU8 src1@@0 p@@0))
)))
(assert (forall ((src1@@1 Int) (p@@1 Int) ) (! (= ($shlU16 src1@@1 p@@1) (mod (* src1@@1 ($pow 2 p@@1)) (+ $MAX_U16 1)))
 :qid |outputbpl.1028:18|
 :skolemid |24|
 :pattern ( ($shlU16 src1@@1 p@@1))
)))
(assert (forall ((src1@@2 Int) (p@@2 Int) ) (! (= ($shlU32 src1@@2 p@@2) (mod (* src1@@2 ($pow 2 p@@2)) (+ $MAX_U32 1)))
 :qid |outputbpl.1059:18|
 :skolemid |25|
 :pattern ( ($shlU32 src1@@2 p@@2))
)))
(assert (forall ((src1@@3 Int) (p@@3 Int) ) (! (= ($shlU64 src1@@3 p@@3) (mod (* src1@@3 ($pow 2 p@@3)) (+ $MAX_U64 1)))
 :qid |outputbpl.1090:18|
 :skolemid |26|
 :pattern ( ($shlU64 src1@@3 p@@3))
)))
(assert (forall ((src1@@4 Int) (p@@4 Int) ) (! (= ($shlU128 src1@@4 p@@4) (mod (* src1@@4 ($pow 2 p@@4)) (+ $MAX_U128 1)))
 :qid |outputbpl.1121:19|
 :skolemid |27|
 :pattern ( ($shlU128 src1@@4 p@@4))
)))
(assert (forall ((src1@@5 Int) (p@@5 Int) ) (! (= ($shlU256 src1@@5 p@@5) (mod (* src1@@5 ($pow 2 p@@5)) (+ $MAX_U256 1)))
 :qid |outputbpl.1152:19|
 :skolemid |28|
 :pattern ( ($shlU256 src1@@5 p@@5))
)))
(assert (= ($ConstMemoryDomain false) (|lambda#4| false)))
(assert (= ($ConstMemoryDomain true) (|lambda#4| true)))
(assert (forall ((v1 T@Vec_11000) (v2 T@Vec_11000) ) (! (= (|$IsEqual'vec'u8''| v1 v2)  (and (= (|l#Vec_11000| v1) (|l#Vec_11000| v2)) (forall ((i@@0 Int) ) (!  (=> (InRangeVec_19336 v1 i@@0) (= (|Select__T@[Int]Int_| (|v#Vec_11000| v1) i@@0) (|Select__T@[Int]Int_| (|v#Vec_11000| v2) i@@0)))
 :qid |outputbpl.3766:13|
 :skolemid |117|
))))
 :qid |outputbpl.3764:28|
 :skolemid |118|
 :pattern ( (|$IsEqual'vec'u8''| v1 v2))
)))
(assert (forall ((v T@Vec_11000) (prefix T@Vec_11000) ) (! (= (|$IsPrefix'vec'u8''| v prefix)  (and (>= (|l#Vec_11000| v) (|l#Vec_11000| prefix)) (forall ((i@@1 Int) ) (!  (=> (InRangeVec_19336 prefix i@@1) (= (|Select__T@[Int]Int_| (|v#Vec_11000| v) i@@1) (|Select__T@[Int]Int_| (|v#Vec_11000| prefix) i@@1)))
 :qid |outputbpl.3772:13|
 :skolemid |119|
))))
 :qid |outputbpl.3770:29|
 :skolemid |120|
 :pattern ( (|$IsPrefix'vec'u8''| v prefix))
)))
(assert (= DefaultTableKeyExistsArray_990 (|lambda#4| false)))
(assert (forall ((v@@0 T@Vec_11000) (e Int) ) (! (let ((i@@2 (IndexOfVec_11000 v@@0 e)))
(ite  (not (exists ((i@@3 Int) ) (!  (and (InRangeVec_19336 v@@0 i@@3) (= (|Select__T@[Int]Int_| (|v#Vec_11000| v@@0) i@@3) e))
 :qid |outputbpl.110:13|
 :skolemid |0|
))) (= i@@2 (- 0 1))  (and (and (InRangeVec_19336 v@@0 i@@2) (= (|Select__T@[Int]Int_| (|v#Vec_11000| v@@0) i@@2) e)) (forall ((j Int) ) (!  (=> (and (>= j 0) (< j i@@2)) (not (= (|Select__T@[Int]Int_| (|v#Vec_11000| v@@0) j) e)))
 :qid |outputbpl.118:17|
 :skolemid |1|
)))))
 :qid |outputbpl.114:32|
 :skolemid |2|
 :pattern ( (IndexOfVec_11000 v@@0 e))
)))
(assert (forall ((s1 T@Vec_11000) (s2 T@Vec_11000) (k1 T@Vec_11000) (k2 T@Vec_11000) (m1 T@Vec_11000) (m2 T@Vec_11000) ) (!  (=> (and (and (|$IsEqual'vec'u8''| s1 s2) (|$IsEqual'vec'u8''| k1 k2)) (|$IsEqual'vec'u8''| m1 m2)) (= ($1_Signature_$ed25519_verify s1 k1 m1) ($1_Signature_$ed25519_verify s2 k2 m2)))
 :qid |outputbpl.4218:15|
 :skolemid |131|
 :pattern ( ($1_Signature_$ed25519_verify s1 k1 m1) ($1_Signature_$ed25519_verify s2 k2 m2))
)))
(assert (forall ((|l#0@@0| Int) (|l#1@@0| Int) (|l#2@@0| Int) (|l#3@@0| |T@[Int]Int|) (|l#4@@0| |T@[Int]Int|) (|l#5@@0| Int) (|l#6| Int) (i@@4 Int) ) (! (= (|Select__T@[Int]Int_| (|lambda#0| |l#0@@0| |l#1@@0| |l#2@@0| |l#3@@0| |l#4@@0| |l#5@@0| |l#6|) i@@4) (ite  (and (>= i@@4 |l#0@@0|) (< i@@4 |l#1@@0|)) (ite (< i@@4 |l#2@@0|) (|Select__T@[Int]Int_| |l#3@@0| i@@4) (|Select__T@[Int]Int_| |l#4@@0| (- i@@4 |l#5@@0|))) |l#6|))
 :qid |outputbpl.74:19|
 :skolemid |135|
 :pattern ( (|Select__T@[Int]Int_| (|lambda#0| |l#0@@0| |l#1@@0| |l#2@@0| |l#3@@0| |l#4@@0| |l#5@@0| |l#6|) i@@4))
)))
(assert (forall ((|l#0@@1| Int) (|l#1@@1| Int) (|l#2@@1| Int) (|l#3@@1| |T@[Int]Int|) (|l#4@@1| |T@[Int]Int|) (|l#5@@1| Int) (|l#6@@0| Int) (j@@0 Int) ) (! (= (|Select__T@[Int]Int_| (|lambda#3| |l#0@@1| |l#1@@1| |l#2@@1| |l#3@@1| |l#4@@1| |l#5@@1| |l#6@@0|) j@@0) (ite  (and (>= j@@0 |l#0@@1|) (< j@@0 |l#1@@1|)) (ite (< j@@0 |l#2@@1|) (|Select__T@[Int]Int_| |l#3@@1| j@@0) (|Select__T@[Int]Int_| |l#4@@1| (+ j@@0 |l#5@@1|))) |l#6@@0|))
 :qid |outputbpl.64:20|
 :skolemid |138|
 :pattern ( (|Select__T@[Int]Int_| (|lambda#3| |l#0@@1| |l#1@@1| |l#2@@1| |l#3@@1| |l#4@@1| |l#5@@1| |l#6@@0|) j@@0))
)))
(assert (forall ((v@@1 (_ BitVec 32)) ) (! (= (|$IsValid'bv32'| v@@1)  (and (bvuge v@@1 #x00000000) (bvule v@@1 #x7fffffff)))
 :qid |outputbpl.1629:25|
 :skolemid |31|
 :pattern ( (|$IsValid'bv32'| v@@1))
)))
(assert (forall ((v@@2 Int) ) (! (= (|$IsValid'address'| v@@2) (>= v@@2 0))
 :qid |outputbpl.2041:28|
 :skolemid |36|
 :pattern ( (|$IsValid'address'| v@@2))
)))
(assert (forall ((v@@3 T@Vec_11000) (suffix T@Vec_11000) ) (! (= (|$IsSuffix'vec'u8''| v@@3 suffix)  (and (>= (|l#Vec_11000| v@@3) (|l#Vec_11000| suffix)) (forall ((i@@5 Int) ) (!  (=> (InRangeVec_19336 suffix i@@5) (= (|Select__T@[Int]Int_| (|v#Vec_11000| v@@3) (+ (- (|l#Vec_11000| v@@3) (|l#Vec_11000| suffix)) i@@5)) (|Select__T@[Int]Int_| (|v#Vec_11000| suffix) i@@5)))
 :qid |outputbpl.3778:13|
 :skolemid |121|
))))
 :qid |outputbpl.3776:29|
 :skolemid |122|
 :pattern ( (|$IsSuffix'vec'u8''| v@@3 suffix))
)))
(assert (forall ((|l#0@@2| Int) (|l#1@@2| Int) (|l#2@@2| |T@[Int]Int|) (|l#3@@2| Int) (|l#4@@2| Int) (k Int) ) (! (= (|Select__T@[Int]Int_| (|lambda#2| |l#0@@2| |l#1@@2| |l#2@@2| |l#3@@2| |l#4@@2|) k) (ite  (and (<= |l#0@@2| k) (< k |l#1@@2|)) (|Select__T@[Int]Int_| |l#2@@2| (+ |l#3@@2| k)) |l#4@@2|))
 :qid |outputbpl.91:14|
 :skolemid |137|
 :pattern ( (|Select__T@[Int]Int_| (|lambda#2| |l#0@@2| |l#1@@2| |l#2@@2| |l#3@@2| |l#4@@2|) k))
)))
(assert (forall ((src1@@6 Int) (p@@6 Int) ) (! (= ($shl src1@@6 p@@6) (* src1@@6 ($pow 2 p@@6)))
 :qid |outputbpl.978:15|
 :skolemid |21|
 :pattern ( ($shl src1@@6 p@@6))
)))
(assert (forall ((src (_ BitVec 256)) ) (! (= ($castBv256to64 src) (ite (bvugt src #x000000000000000000000000000000000000000000000000ffffffffffffffff) |$Arbitrary_value_of'bv64'| ((_ extract 63 0) src)))
 :qid |outputbpl.3261:25|
 :skolemid |88|
 :pattern ( ($castBv256to64 src))
)))
(assert (= $MAX_I32 2147483647))
(assert (= $MIN_I32 (- 0 2147483648)))
(assert (forall ((src1@@7 (_ BitVec 8)) (src2 (_ BitVec 16)) ) (! (= ($shlBv8From16 src1@@7 src2) (bvshl src1@@7 ((_ extract 7 0) src2)))
 :qid |outputbpl.2391:24|
 :skolemid |43|
 :pattern ( ($shlBv8From16 src1@@7 src2))
)))
(assert (forall ((src1@@8 (_ BitVec 8)) (src2@@0 (_ BitVec 16)) ) (! (= ($shrBv8From16 src1@@8 src2@@0) (bvlshr src1@@8 ((_ extract 7 0) src2@@0)))
 :qid |outputbpl.2406:24|
 :skolemid |44|
 :pattern ( ($shrBv8From16 src1@@8 src2@@0))
)))
(assert (forall ((src1@@9 (_ BitVec 8)) (src2@@1 (_ BitVec 32)) ) (! (= ($shlBv8From32 src1@@9 src2@@1) (bvshl src1@@9 ((_ extract 7 0) src2@@1)))
 :qid |outputbpl.2432:24|
 :skolemid |45|
 :pattern ( ($shlBv8From32 src1@@9 src2@@1))
)))
(assert (forall ((src1@@10 (_ BitVec 8)) (src2@@2 (_ BitVec 32)) ) (! (= ($shrBv8From32 src1@@10 src2@@2) (bvlshr src1@@10 ((_ extract 7 0) src2@@2)))
 :qid |outputbpl.2447:24|
 :skolemid |46|
 :pattern ( ($shrBv8From32 src1@@10 src2@@2))
)))
(assert (forall ((src1@@11 (_ BitVec 8)) (src2@@3 (_ BitVec 64)) ) (! (= ($shlBv8From64 src1@@11 src2@@3) (bvshl src1@@11 ((_ extract 7 0) src2@@3)))
 :qid |outputbpl.2473:24|
 :skolemid |47|
 :pattern ( ($shlBv8From64 src1@@11 src2@@3))
)))
(assert (forall ((src1@@12 (_ BitVec 8)) (src2@@4 (_ BitVec 64)) ) (! (= ($shrBv8From64 src1@@12 src2@@4) (bvlshr src1@@12 ((_ extract 7 0) src2@@4)))
 :qid |outputbpl.2488:24|
 :skolemid |48|
 :pattern ( ($shrBv8From64 src1@@12 src2@@4))
)))
(assert (forall ((src1@@13 (_ BitVec 8)) (src2@@5 (_ BitVec 128)) ) (! (= ($shlBv8From128 src1@@13 src2@@5) (bvshl src1@@13 ((_ extract 7 0) src2@@5)))
 :qid |outputbpl.2514:25|
 :skolemid |49|
 :pattern ( ($shlBv8From128 src1@@13 src2@@5))
)))
(assert (forall ((src1@@14 (_ BitVec 8)) (src2@@6 (_ BitVec 128)) ) (! (= ($shrBv8From128 src1@@14 src2@@6) (bvlshr src1@@14 ((_ extract 7 0) src2@@6)))
 :qid |outputbpl.2529:25|
 :skolemid |50|
 :pattern ( ($shrBv8From128 src1@@14 src2@@6))
)))
(assert (forall ((src1@@15 (_ BitVec 8)) (src2@@7 (_ BitVec 256)) ) (! (= ($shlBv8From256 src1@@15 src2@@7) (bvshl src1@@15 ((_ extract 7 0) src2@@7)))
 :qid |outputbpl.2555:25|
 :skolemid |51|
 :pattern ( ($shlBv8From256 src1@@15 src2@@7))
)))
(assert (forall ((src1@@16 (_ BitVec 8)) (src2@@8 (_ BitVec 256)) ) (! (= ($shrBv8From256 src1@@16 src2@@8) (bvlshr src1@@16 ((_ extract 7 0) src2@@8)))
 :qid |outputbpl.2570:25|
 :skolemid |52|
 :pattern ( ($shrBv8From256 src1@@16 src2@@8))
)))
(assert (forall ((src1@@17 (_ BitVec 16)) (src2@@9 (_ BitVec 32)) ) (! (= ($shlBv16From32 src1@@17 src2@@9) (bvshl src1@@17 ((_ extract 15 0) src2@@9)))
 :qid |outputbpl.2670:25|
 :skolemid |57|
 :pattern ( ($shlBv16From32 src1@@17 src2@@9))
)))
(assert (forall ((src1@@18 (_ BitVec 16)) (src2@@10 (_ BitVec 32)) ) (! (= ($shrBv16From32 src1@@18 src2@@10) (bvlshr src1@@18 ((_ extract 15 0) src2@@10)))
 :qid |outputbpl.2685:25|
 :skolemid |58|
 :pattern ( ($shrBv16From32 src1@@18 src2@@10))
)))
(assert (forall ((src1@@19 (_ BitVec 16)) (src2@@11 (_ BitVec 64)) ) (! (= ($shlBv16From64 src1@@19 src2@@11) (bvshl src1@@19 ((_ extract 15 0) src2@@11)))
 :qid |outputbpl.2711:25|
 :skolemid |59|
 :pattern ( ($shlBv16From64 src1@@19 src2@@11))
)))
(assert (forall ((src1@@20 (_ BitVec 16)) (src2@@12 (_ BitVec 64)) ) (! (= ($shrBv16From64 src1@@20 src2@@12) (bvlshr src1@@20 ((_ extract 15 0) src2@@12)))
 :qid |outputbpl.2726:25|
 :skolemid |60|
 :pattern ( ($shrBv16From64 src1@@20 src2@@12))
)))
(assert (forall ((src1@@21 (_ BitVec 16)) (src2@@13 (_ BitVec 128)) ) (! (= ($shlBv16From128 src1@@21 src2@@13) (bvshl src1@@21 ((_ extract 15 0) src2@@13)))
 :qid |outputbpl.2752:26|
 :skolemid |61|
 :pattern ( ($shlBv16From128 src1@@21 src2@@13))
)))
(assert (forall ((src1@@22 (_ BitVec 16)) (src2@@14 (_ BitVec 128)) ) (! (= ($shrBv16From128 src1@@22 src2@@14) (bvlshr src1@@22 ((_ extract 15 0) src2@@14)))
 :qid |outputbpl.2767:26|
 :skolemid |62|
 :pattern ( ($shrBv16From128 src1@@22 src2@@14))
)))
(assert (forall ((src1@@23 (_ BitVec 16)) (src2@@15 (_ BitVec 256)) ) (! (= ($shlBv16From256 src1@@23 src2@@15) (bvshl src1@@23 ((_ extract 15 0) src2@@15)))
 :qid |outputbpl.2793:26|
 :skolemid |63|
 :pattern ( ($shlBv16From256 src1@@23 src2@@15))
)))
(assert (forall ((src1@@24 (_ BitVec 16)) (src2@@16 (_ BitVec 256)) ) (! (= ($shrBv16From256 src1@@24 src2@@16) (bvlshr src1@@24 ((_ extract 15 0) src2@@16)))
 :qid |outputbpl.2808:26|
 :skolemid |64|
 :pattern ( ($shrBv16From256 src1@@24 src2@@16))
)))
(assert (forall ((src1@@25 (_ BitVec 32)) (src2@@17 (_ BitVec 64)) ) (! (= ($shlBv32From64 src1@@25 src2@@17) (bvshl src1@@25 ((_ extract 31 0) src2@@17)))
 :qid |outputbpl.2945:25|
 :skolemid |71|
 :pattern ( ($shlBv32From64 src1@@25 src2@@17))
)))
(assert (forall ((src1@@26 (_ BitVec 32)) (src2@@18 (_ BitVec 64)) ) (! (= ($shrBv32From64 src1@@26 src2@@18) (bvlshr src1@@26 ((_ extract 31 0) src2@@18)))
 :qid |outputbpl.2960:25|
 :skolemid |72|
 :pattern ( ($shrBv32From64 src1@@26 src2@@18))
)))
(assert (forall ((src1@@27 (_ BitVec 32)) (src2@@19 (_ BitVec 128)) ) (! (= ($shlBv32From128 src1@@27 src2@@19) (bvshl src1@@27 ((_ extract 31 0) src2@@19)))
 :qid |outputbpl.2986:26|
 :skolemid |73|
 :pattern ( ($shlBv32From128 src1@@27 src2@@19))
)))
(assert (forall ((src1@@28 (_ BitVec 32)) (src2@@20 (_ BitVec 128)) ) (! (= ($shrBv32From128 src1@@28 src2@@20) (bvlshr src1@@28 ((_ extract 31 0) src2@@20)))
 :qid |outputbpl.3001:26|
 :skolemid |74|
 :pattern ( ($shrBv32From128 src1@@28 src2@@20))
)))
(assert (forall ((src1@@29 (_ BitVec 32)) (src2@@21 (_ BitVec 256)) ) (! (= ($shlBv32From256 src1@@29 src2@@21) (bvshl src1@@29 ((_ extract 31 0) src2@@21)))
 :qid |outputbpl.3027:26|
 :skolemid |75|
 :pattern ( ($shlBv32From256 src1@@29 src2@@21))
)))
(assert (forall ((src1@@30 (_ BitVec 32)) (src2@@22 (_ BitVec 256)) ) (! (= ($shrBv32From256 src1@@30 src2@@22) (bvlshr src1@@30 ((_ extract 31 0) src2@@22)))
 :qid |outputbpl.3042:26|
 :skolemid |76|
 :pattern ( ($shrBv32From256 src1@@30 src2@@22))
)))
(assert (forall ((src1@@31 (_ BitVec 64)) (src2@@23 (_ BitVec 128)) ) (! (= ($shlBv64From128 src1@@31 src2@@23) (bvshl src1@@31 ((_ extract 63 0) src2@@23)))
 :qid |outputbpl.3221:26|
 :skolemid |86|
 :pattern ( ($shlBv64From128 src1@@31 src2@@23))
)))
(assert (forall ((src1@@32 (_ BitVec 64)) (src2@@24 (_ BitVec 128)) ) (! (= ($shrBv64From128 src1@@32 src2@@24) (bvlshr src1@@32 ((_ extract 63 0) src2@@24)))
 :qid |outputbpl.3236:26|
 :skolemid |87|
 :pattern ( ($shrBv64From128 src1@@32 src2@@24))
)))
(assert (forall ((src1@@33 (_ BitVec 64)) (src2@@25 (_ BitVec 256)) ) (! (= ($shlBv64From256 src1@@33 src2@@25) (bvshl src1@@33 ((_ extract 63 0) src2@@25)))
 :qid |outputbpl.3270:26|
 :skolemid |89|
 :pattern ( ($shlBv64From256 src1@@33 src2@@25))
)))
(assert (forall ((src1@@34 (_ BitVec 64)) (src2@@26 (_ BitVec 256)) ) (! (= ($shrBv64From256 src1@@34 src2@@26) (bvlshr src1@@34 ((_ extract 63 0) src2@@26)))
 :qid |outputbpl.3285:26|
 :skolemid |90|
 :pattern ( ($shrBv64From256 src1@@34 src2@@26))
)))
(assert (forall ((src1@@35 (_ BitVec 128)) (src2@@27 (_ BitVec 256)) ) (! (= ($shlBv128From256 src1@@35 src2@@27) (bvshl src1@@35 ((_ extract 127 0) src2@@27)))
 :qid |outputbpl.3496:27|
 :skolemid |101|
 :pattern ( ($shlBv128From256 src1@@35 src2@@27))
)))
(assert (forall ((src1@@36 (_ BitVec 128)) (src2@@28 (_ BitVec 256)) ) (! (= ($shrBv128From256 src1@@36 src2@@28) (bvlshr src1@@36 ((_ extract 127 0) src2@@28)))
 :qid |outputbpl.3511:27|
 :skolemid |102|
 :pattern ( ($shrBv128From256 src1@@36 src2@@28))
)))
(assert (forall ((v@@4 T@Vec_11000) ) (! (= (|$IsValid'vec'u8''| v@@4)  (and (|$IsValid'u64'| (|l#Vec_11000| v@@4)) (forall ((i@@6 Int) ) (!  (=> (InRangeVec_19336 v@@4 i@@6) (|$IsValid'u8'| (|Select__T@[Int]Int_| (|v#Vec_11000| v@@4) i@@6)))
 :qid |outputbpl.3784:13|
 :skolemid |123|
))))
 :qid |outputbpl.3782:28|
 :skolemid |124|
 :pattern ( (|$IsValid'vec'u8''| v@@4))
)))
(assert (forall ((|l#0@@3| Bool) (i@@7 Int) ) (! (= (|Select__T@[Int]Bool_| (|lambda#4| |l#0@@3|) i@@7) |l#0@@3|)
 :qid |outputbpl.194:57|
 :skolemid |139|
 :pattern ( (|Select__T@[Int]Bool_| (|lambda#4| |l#0@@3|) i@@7))
)))
(assert (forall ((v@@5 Int) ) (! (= (|$IsValid'num'| v@@5) true)
 :qid |outputbpl.2037:24|
 :skolemid |35|
 :pattern ( (|$IsValid'num'| v@@5))
)))
(assert (forall ((src@@0 (_ BitVec 64)) ) (! (= ($castBv64to256 src@@0) (concat #x000000000000000000000000000000000000000000000000 src@@0))
 :qid |outputbpl.3635:25|
 :skolemid |109|
 :pattern ( ($castBv64to256 src@@0))
)))
(assert (forall ((n Int) (e@@0 Int) ) (! (= ($pow n e@@0) (ite  (and (not (= n 0)) (= e@@0 0)) 1 (ite (> e@@0 0) (* n ($pow n (- e@@0 1))) $undefined_int)))
 :qid |outputbpl.972:15|
 :skolemid |20|
 :pattern ( ($pow n e@@0))
)))
(assert (forall ((src1@@37 (_ BitVec 16)) (src2@@29 (_ BitVec 8)) ) (! (= ($shlBv16From8 src1@@37 src2@@29) (bvshl src1@@37 (concat #x00 src2@@29)))
 :qid |outputbpl.2592:24|
 :skolemid |53|
 :pattern ( ($shlBv16From8 src1@@37 src2@@29))
)))
(assert (forall ((src1@@38 (_ BitVec 16)) (src2@@30 (_ BitVec 8)) ) (! (= ($shrBv16From8 src1@@38 src2@@30) (bvlshr src1@@38 (concat #x00 src2@@30)))
 :qid |outputbpl.2607:24|
 :skolemid |54|
 :pattern ( ($shrBv16From8 src1@@38 src2@@30))
)))
(assert (forall ((src1@@39 (_ BitVec 32)) (src2@@31 (_ BitVec 16)) ) (! (= ($shlBv32From16 src1@@39 src2@@31) (bvshl src1@@39 (concat #x0000 src2@@31)))
 :qid |outputbpl.2867:25|
 :skolemid |67|
 :pattern ( ($shlBv32From16 src1@@39 src2@@31))
)))
(assert (forall ((src1@@40 (_ BitVec 32)) (src2@@32 (_ BitVec 16)) ) (! (= ($shrBv32From16 src1@@40 src2@@32) (bvlshr src1@@40 (concat #x0000 src2@@32)))
 :qid |outputbpl.2882:25|
 :skolemid |68|
 :pattern ( ($shrBv32From16 src1@@40 src2@@32))
)))
(assert (forall ((src1@@41 (_ BitVec 32)) (src2@@33 (_ BitVec 8)) ) (! (= ($shlBv32From8 src1@@41 src2@@33) (bvshl src1@@41 (concat #x000000 src2@@33)))
 :qid |outputbpl.2830:24|
 :skolemid |65|
 :pattern ( ($shlBv32From8 src1@@41 src2@@33))
)))
(assert (forall ((src1@@42 (_ BitVec 32)) (src2@@34 (_ BitVec 8)) ) (! (= ($shrBv32From8 src1@@42 src2@@34) (bvlshr src1@@42 (concat #x000000 src2@@34)))
 :qid |outputbpl.2845:24|
 :skolemid |66|
 :pattern ( ($shrBv32From8 src1@@42 src2@@34))
)))
(assert (forall ((src1@@43 (_ BitVec 64)) (src2@@35 (_ BitVec 32)) ) (! (= ($shlBv64From32 src1@@43 src2@@35) (bvshl src1@@43 (concat #x00000000 src2@@35)))
 :qid |outputbpl.3138:25|
 :skolemid |81|
 :pattern ( ($shlBv64From32 src1@@43 src2@@35))
)))
(assert (forall ((src1@@44 (_ BitVec 64)) (src2@@36 (_ BitVec 32)) ) (! (= ($shrBv64From32 src1@@44 src2@@36) (bvlshr src1@@44 (concat #x00000000 src2@@36)))
 :qid |outputbpl.3153:25|
 :skolemid |82|
 :pattern ( ($shrBv64From32 src1@@44 src2@@36))
)))
(assert (forall ((src1@@45 (_ BitVec 64)) (src2@@37 (_ BitVec 16)) ) (! (= ($shlBv64From16 src1@@45 src2@@37) (bvshl src1@@45 (concat #x000000000000 src2@@37)))
 :qid |outputbpl.3101:25|
 :skolemid |79|
 :pattern ( ($shlBv64From16 src1@@45 src2@@37))
)))
(assert (forall ((src1@@46 (_ BitVec 64)) (src2@@38 (_ BitVec 16)) ) (! (= ($shrBv64From16 src1@@46 src2@@38) (bvlshr src1@@46 (concat #x000000000000 src2@@38)))
 :qid |outputbpl.3116:25|
 :skolemid |80|
 :pattern ( ($shrBv64From16 src1@@46 src2@@38))
)))
(assert (forall ((src1@@47 (_ BitVec 64)) (src2@@39 (_ BitVec 8)) ) (! (= ($shlBv64From8 src1@@47 src2@@39) (bvshl src1@@47 (concat #x00000000000000 src2@@39)))
 :qid |outputbpl.3064:24|
 :skolemid |77|
 :pattern ( ($shlBv64From8 src1@@47 src2@@39))
)))
(assert (forall ((src1@@48 (_ BitVec 64)) (src2@@40 (_ BitVec 8)) ) (! (= ($shrBv64From8 src1@@48 src2@@40) (bvlshr src1@@48 (concat #x00000000000000 src2@@40)))
 :qid |outputbpl.3079:24|
 :skolemid |78|
 :pattern ( ($shrBv64From8 src1@@48 src2@@40))
)))
(assert (forall ((src1@@49 (_ BitVec 128)) (src2@@41 (_ BitVec 64)) ) (! (= ($shlBv128From64 src1@@49 src2@@41) (bvshl src1@@49 (concat #x0000000000000000 src2@@41)))
 :qid |outputbpl.3418:26|
 :skolemid |97|
 :pattern ( ($shlBv128From64 src1@@49 src2@@41))
)))
(assert (forall ((src1@@50 (_ BitVec 128)) (src2@@42 (_ BitVec 64)) ) (! (= ($shrBv128From64 src1@@50 src2@@42) (bvlshr src1@@50 (concat #x0000000000000000 src2@@42)))
 :qid |outputbpl.3433:26|
 :skolemid |98|
 :pattern ( ($shrBv128From64 src1@@50 src2@@42))
)))
(assert (forall ((src1@@51 (_ BitVec 128)) (src2@@43 (_ BitVec 32)) ) (! (= ($shlBv128From32 src1@@51 src2@@43) (bvshl src1@@51 (concat #x000000000000000000000000 src2@@43)))
 :qid |outputbpl.3381:26|
 :skolemid |95|
 :pattern ( ($shlBv128From32 src1@@51 src2@@43))
)))
(assert (forall ((src1@@52 (_ BitVec 128)) (src2@@44 (_ BitVec 32)) ) (! (= ($shrBv128From32 src1@@52 src2@@44) (bvlshr src1@@52 (concat #x000000000000000000000000 src2@@44)))
 :qid |outputbpl.3396:26|
 :skolemid |96|
 :pattern ( ($shrBv128From32 src1@@52 src2@@44))
)))
(assert (forall ((src1@@53 (_ BitVec 128)) (src2@@45 (_ BitVec 16)) ) (! (= ($shlBv128From16 src1@@53 src2@@45) (bvshl src1@@53 (concat #x0000000000000000000000000000 src2@@45)))
 :qid |outputbpl.3344:26|
 :skolemid |93|
 :pattern ( ($shlBv128From16 src1@@53 src2@@45))
)))
(assert (forall ((src1@@54 (_ BitVec 128)) (src2@@46 (_ BitVec 16)) ) (! (= ($shrBv128From16 src1@@54 src2@@46) (bvlshr src1@@54 (concat #x0000000000000000000000000000 src2@@46)))
 :qid |outputbpl.3359:26|
 :skolemid |94|
 :pattern ( ($shrBv128From16 src1@@54 src2@@46))
)))
(assert (forall ((src1@@55 (_ BitVec 128)) (src2@@47 (_ BitVec 8)) ) (! (= ($shlBv128From8 src1@@55 src2@@47) (bvshl src1@@55 (concat #x000000000000000000000000000000 src2@@47)))
 :qid |outputbpl.3307:25|
 :skolemid |91|
 :pattern ( ($shlBv128From8 src1@@55 src2@@47))
)))
(assert (forall ((src1@@56 (_ BitVec 128)) (src2@@48 (_ BitVec 8)) ) (! (= ($shrBv128From8 src1@@56 src2@@48) (bvlshr src1@@56 (concat #x000000000000000000000000000000 src2@@48)))
 :qid |outputbpl.3322:25|
 :skolemid |92|
 :pattern ( ($shrBv128From8 src1@@56 src2@@48))
)))
(assert (forall ((src1@@57 (_ BitVec 256)) (src2@@49 (_ BitVec 128)) ) (! (= ($shlBv256From128 src1@@57 src2@@49) (bvshl src1@@57 (concat #x00000000000000000000000000000000 src2@@49)))
 :qid |outputbpl.3678:27|
 :skolemid |112|
 :pattern ( ($shlBv256From128 src1@@57 src2@@49))
)))
(assert (forall ((src1@@58 (_ BitVec 256)) (src2@@50 (_ BitVec 128)) ) (! (= ($shrBv256From128 src1@@58 src2@@50) (bvlshr src1@@58 (concat #x00000000000000000000000000000000 src2@@50)))
 :qid |outputbpl.3693:27|
 :skolemid |113|
 :pattern ( ($shrBv256From128 src1@@58 src2@@50))
)))
(assert (forall ((src1@@59 (_ BitVec 256)) (src2@@51 (_ BitVec 64)) ) (! (= ($shlBv256From64 src1@@59 src2@@51) (bvshl src1@@59 (concat #x000000000000000000000000000000000000000000000000 src2@@51)))
 :qid |outputbpl.3641:26|
 :skolemid |110|
 :pattern ( ($shlBv256From64 src1@@59 src2@@51))
)))
(assert (forall ((src1@@60 (_ BitVec 256)) (src2@@52 (_ BitVec 64)) ) (! (= ($shrBv256From64 src1@@60 src2@@52) (bvlshr src1@@60 (concat #x000000000000000000000000000000000000000000000000 src2@@52)))
 :qid |outputbpl.3656:26|
 :skolemid |111|
 :pattern ( ($shrBv256From64 src1@@60 src2@@52))
)))
(assert (forall ((src1@@61 (_ BitVec 256)) (src2@@53 (_ BitVec 32)) ) (! (= ($shlBv256From32 src1@@61 src2@@53) (bvshl src1@@61 (concat #x00000000000000000000000000000000000000000000000000000000 src2@@53)))
 :qid |outputbpl.3599:26|
 :skolemid |107|
 :pattern ( ($shlBv256From32 src1@@61 src2@@53))
)))
(assert (forall ((src1@@62 (_ BitVec 256)) (src2@@54 (_ BitVec 32)) ) (! (= ($shrBv256From32 src1@@62 src2@@54) (bvlshr src1@@62 (concat #x00000000000000000000000000000000000000000000000000000000 src2@@54)))
 :qid |outputbpl.3614:26|
 :skolemid |108|
 :pattern ( ($shrBv256From32 src1@@62 src2@@54))
)))
(assert (forall ((src1@@63 (_ BitVec 256)) (src2@@55 (_ BitVec 16)) ) (! (= ($shlBv256From16 src1@@63 src2@@55) (bvshl src1@@63 (concat #x000000000000000000000000000000000000000000000000000000000000 src2@@55)))
 :qid |outputbpl.3562:26|
 :skolemid |105|
 :pattern ( ($shlBv256From16 src1@@63 src2@@55))
)))
(assert (forall ((src1@@64 (_ BitVec 256)) (src2@@56 (_ BitVec 16)) ) (! (= ($shrBv256From16 src1@@64 src2@@56) (bvlshr src1@@64 (concat #x000000000000000000000000000000000000000000000000000000000000 src2@@56)))
 :qid |outputbpl.3577:26|
 :skolemid |106|
 :pattern ( ($shrBv256From16 src1@@64 src2@@56))
)))
(assert (forall ((src1@@65 (_ BitVec 256)) (src2@@57 (_ BitVec 8)) ) (! (= ($shlBv256From8 src1@@65 src2@@57) (bvshl src1@@65 (concat #x00000000000000000000000000000000000000000000000000000000000000 src2@@57)))
 :qid |outputbpl.3533:25|
 :skolemid |103|
 :pattern ( ($shlBv256From8 src1@@65 src2@@57))
)))
(assert (forall ((src1@@66 (_ BitVec 256)) (src2@@58 (_ BitVec 8)) ) (! (= ($shrBv256From8 src1@@66 src2@@58) (bvlshr src1@@66 (concat #x00000000000000000000000000000000000000000000000000000000000000 src2@@58)))
 :qid |outputbpl.3544:25|
 :skolemid |104|
 :pattern ( ($shrBv256From8 src1@@66 src2@@58))
)))
(assert (forall ((s T@$bc_ProphecyBenchmark3Levels5Fields_Node1) ) (! (= (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node1'| s)  (and (and (and (and (and (and (and (|$IsValid'u64'| (|$v0#$bc_ProphecyBenchmark3Levels5Fields_Node1| s)) (|$IsValid'u64'| (|$v1#$bc_ProphecyBenchmark3Levels5Fields_Node1| s))) (|$IsValid'u64'| (|$v2#$bc_ProphecyBenchmark3Levels5Fields_Node1| s))) (|$IsValid'u64'| (|$v3#$bc_ProphecyBenchmark3Levels5Fields_Node1| s))) (|$IsValid'u64'| (|$v4#$bc_ProphecyBenchmark3Levels5Fields_Node1| s))) (|$IsValid'u64'| (|$v5#$bc_ProphecyBenchmark3Levels5Fields_Node1| s))) (|$IsValid'u64'| (|$v6#$bc_ProphecyBenchmark3Levels5Fields_Node1| s))) (|$IsValid'u64'| (|$v7#$bc_ProphecyBenchmark3Levels5Fields_Node1| s))))
 :qid |outputbpl.4311:62|
 :skolemid |132|
 :pattern ( (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node1'| s))
)))
(assert (forall ((s@@0 T@$bc_ProphecyBenchmark3Levels5Fields_Node2) ) (! (= (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node2'| s@@0)  (and (and (and (and (and (and (and (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node1'| (|$v0#$bc_ProphecyBenchmark3Levels5Fields_Node2| s@@0)) (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node1'| (|$v1#$bc_ProphecyBenchmark3Levels5Fields_Node2| s@@0))) (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node1'| (|$v2#$bc_ProphecyBenchmark3Levels5Fields_Node2| s@@0))) (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node1'| (|$v3#$bc_ProphecyBenchmark3Levels5Fields_Node2| s@@0))) (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node1'| (|$v4#$bc_ProphecyBenchmark3Levels5Fields_Node2| s@@0))) (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node1'| (|$v5#$bc_ProphecyBenchmark3Levels5Fields_Node2| s@@0))) (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node1'| (|$v6#$bc_ProphecyBenchmark3Levels5Fields_Node2| s@@0))) (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node1'| (|$v7#$bc_ProphecyBenchmark3Levels5Fields_Node2| s@@0))))
 :qid |outputbpl.4353:62|
 :skolemid |133|
 :pattern ( (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node2'| s@@0))
)))
(assert (forall ((s@@1 T@$bc_ProphecyBenchmark3Levels5Fields_Node3) ) (! (= (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node3'| s@@1)  (and (and (and (and (and (and (and (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node2'| (|$v0#$bc_ProphecyBenchmark3Levels5Fields_Node3| s@@1)) (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node2'| (|$v1#$bc_ProphecyBenchmark3Levels5Fields_Node3| s@@1))) (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node2'| (|$v2#$bc_ProphecyBenchmark3Levels5Fields_Node3| s@@1))) (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node2'| (|$v3#$bc_ProphecyBenchmark3Levels5Fields_Node3| s@@1))) (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node2'| (|$v4#$bc_ProphecyBenchmark3Levels5Fields_Node3| s@@1))) (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node2'| (|$v5#$bc_ProphecyBenchmark3Levels5Fields_Node3| s@@1))) (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node2'| (|$v6#$bc_ProphecyBenchmark3Levels5Fields_Node3| s@@1))) (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node2'| (|$v7#$bc_ProphecyBenchmark3Levels5Fields_Node3| s@@1))))
 :qid |outputbpl.4395:62|
 :skolemid |134|
 :pattern ( (|$IsValid'$bc_ProphecyBenchmark3Levels5Fields_Node3'| s@@1))
)))
(assert (forall ((src@@1 (_ BitVec 64)) ) (! (= ($castBv64to64 src@@1) src@@1)
 :qid |outputbpl.3174:24|
 :skolemid |83|
 :pattern ( ($castBv64to64 src@@1))
)))
(assert (forall ((src@@2 (_ BitVec 256)) ) (! (= ($castBv256to256 src@@2) src@@2)
 :qid |outputbpl.3714:26|
 :skolemid |114|
 :pattern ( ($castBv256to256 src@@2))
)))
(assert (forall ((src1@@67 (_ BitVec 8)) (src2@@59 (_ BitVec 8)) ) (! (= ($shlBv8From8 src1@@67 src2@@59) (bvshl src1@@67 src2@@59))
 :qid |outputbpl.2350:23|
 :skolemid |41|
 :pattern ( ($shlBv8From8 src1@@67 src2@@59))
)))
(assert (forall ((src1@@68 (_ BitVec 8)) (src2@@60 (_ BitVec 8)) ) (! (= ($shrBv8From8 src1@@68 src2@@60) (bvlshr src1@@68 src2@@60))
 :qid |outputbpl.2365:23|
 :skolemid |42|
 :pattern ( ($shrBv8From8 src1@@68 src2@@60))
)))
(assert (forall ((src1@@69 (_ BitVec 16)) (src2@@61 (_ BitVec 16)) ) (! (= ($shlBv16From16 src1@@69 src2@@61) (bvshl src1@@69 src2@@61))
 :qid |outputbpl.2629:25|
 :skolemid |55|
 :pattern ( ($shlBv16From16 src1@@69 src2@@61))
)))
(assert (forall ((src1@@70 (_ BitVec 16)) (src2@@62 (_ BitVec 16)) ) (! (= ($shrBv16From16 src1@@70 src2@@62) (bvlshr src1@@70 src2@@62))
 :qid |outputbpl.2644:25|
 :skolemid |56|
 :pattern ( ($shrBv16From16 src1@@70 src2@@62))
)))
(assert (forall ((src1@@71 (_ BitVec 32)) (src2@@63 (_ BitVec 32)) ) (! (= ($shlBv32From32 src1@@71 src2@@63) (bvshl src1@@71 src2@@63))
 :qid |outputbpl.2904:25|
 :skolemid |69|
 :pattern ( ($shlBv32From32 src1@@71 src2@@63))
)))
(assert (forall ((src1@@72 (_ BitVec 32)) (src2@@64 (_ BitVec 32)) ) (! (= ($shrBv32From32 src1@@72 src2@@64) (bvlshr src1@@72 src2@@64))
 :qid |outputbpl.2919:25|
 :skolemid |70|
 :pattern ( ($shrBv32From32 src1@@72 src2@@64))
)))
(assert (forall ((src1@@73 (_ BitVec 64)) (src2@@65 (_ BitVec 64)) ) (! (= ($shlBv64From64 src1@@73 src2@@65) (bvshl src1@@73 src2@@65))
 :qid |outputbpl.3180:25|
 :skolemid |84|
 :pattern ( ($shlBv64From64 src1@@73 src2@@65))
)))
(assert (forall ((src1@@74 (_ BitVec 64)) (src2@@66 (_ BitVec 64)) ) (! (= ($shrBv64From64 src1@@74 src2@@66) (bvlshr src1@@74 src2@@66))
 :qid |outputbpl.3195:25|
 :skolemid |85|
 :pattern ( ($shrBv64From64 src1@@74 src2@@66))
)))
(assert (forall ((src1@@75 (_ BitVec 128)) (src2@@67 (_ BitVec 128)) ) (! (= ($shlBv128From128 src1@@75 src2@@67) (bvshl src1@@75 src2@@67))
 :qid |outputbpl.3455:27|
 :skolemid |99|
 :pattern ( ($shlBv128From128 src1@@75 src2@@67))
)))
(assert (forall ((src1@@76 (_ BitVec 128)) (src2@@68 (_ BitVec 128)) ) (! (= ($shrBv128From128 src1@@76 src2@@68) (bvlshr src1@@76 src2@@68))
 :qid |outputbpl.3470:27|
 :skolemid |100|
 :pattern ( ($shrBv128From128 src1@@76 src2@@68))
)))
(assert (forall ((src1@@77 (_ BitVec 256)) (src2@@69 (_ BitVec 256)) ) (! (= ($shlBv256From256 src1@@77 src2@@69) (bvshl src1@@77 src2@@69))
 :qid |outputbpl.3720:27|
 :skolemid |115|
 :pattern ( ($shlBv256From256 src1@@77 src2@@69))
)))
(assert (forall ((src1@@78 (_ BitVec 256)) (src2@@70 (_ BitVec 256)) ) (! (= ($shrBv256From256 src1@@78 src2@@70) (bvlshr src1@@78 src2@@70))
 :qid |outputbpl.3735:27|
 :skolemid |116|
 :pattern ( ($shrBv256From256 src1@@78 src2@@70))
)))
(assert (forall ((k1@@0 T@Vec_11000) (k2@@0 T@Vec_11000) ) (!  (=> (|$IsEqual'vec'u8''| k1@@0 k2@@0) (= ($1_Signature_$ed25519_validate_pubkey k1@@0) ($1_Signature_$ed25519_validate_pubkey k2@@0)))
 :qid |outputbpl.4215:15|
 :skolemid |130|
 :pattern ( ($1_Signature_$ed25519_validate_pubkey k1@@0) ($1_Signature_$ed25519_validate_pubkey k2@@0))
)))
(assert (forall ((v@@6 (_ BitVec 8)) ) (! (= (|$IsValid'bv8'| v@@6)  (and (bvuge v@@6 #x00) (bvule v@@6 #xff)))
 :qid |outputbpl.1379:24|
 :skolemid |29|
 :pattern ( (|$IsValid'bv8'| v@@6))
)))
(assert (forall ((v@@7 (_ BitVec 64)) ) (! (= (|$IsValid'bv64'| v@@7)  (and (bvuge v@@7 #x0000000000000000) (bvule v@@7 #xffffffffffffffff)))
 :qid |outputbpl.1754:25|
 :skolemid |32|
 :pattern ( (|$IsValid'bv64'| v@@7))
)))
(assert (forall ((v@@8 (_ BitVec 16)) ) (! (= (|$IsValid'bv16'| v@@8)  (and (bvuge v@@8 #x0000) (bvule v@@8 #xffff)))
 :qid |outputbpl.1504:25|
 :skolemid |30|
 :pattern ( (|$IsValid'bv16'| v@@8))
)))
(assert (forall ((v@@9 (_ BitVec 256)) ) (! (= (|$IsValid'bv256'| v@@9)  (and (bvuge v@@9 #x0000000000000000000000000000000000000000000000000000000000000000) (bvule v@@9 #xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)))
 :qid |outputbpl.2004:26|
 :skolemid |34|
 :pattern ( (|$IsValid'bv256'| v@@9))
)))
(assert (forall ((v@@10 T@Vec_11000) (e@@1 Int) ) (! (let ((i@@8 (|$IndexOfVec'u8'| v@@10 e@@1)))
(ite  (not (exists ((i@@9 Int) ) (!  (and (and (|$IsValid'u64'| i@@9) (InRangeVec_19336 v@@10 i@@9)) (= (|Select__T@[Int]Int_| (|v#Vec_11000| v@@10) i@@9) e@@1))
 :qid |outputbpl.3789:13|
 :skolemid |125|
))) (= i@@8 (- 0 1))  (and (and (and (|$IsValid'u64'| i@@8) (InRangeVec_19336 v@@10 i@@8)) (= (|Select__T@[Int]Int_| (|v#Vec_11000| v@@10) i@@8) e@@1)) (forall ((j@@1 Int) ) (!  (=> (and (and (|$IsValid'u64'| j@@1) (>= j@@1 0)) (< j@@1 i@@8)) (not (= (|Select__T@[Int]Int_| (|v#Vec_11000| v@@10) j@@1) e@@1)))
 :qid |outputbpl.3797:17|
 :skolemid |126|
)))))
 :qid |outputbpl.3793:15|
 :skolemid |127|
 :pattern ( (|$IndexOfVec'u8'| v@@10 e@@1))
)))
(assert (forall ((v@@11 (_ BitVec 128)) ) (! (= (|$IsValid'bv128'| v@@11)  (and (bvuge v@@11 #x00000000000000000000000000000000) (bvule v@@11 #xffffffffffffffffffffffffffffffff)))
 :qid |outputbpl.1879:26|
 :skolemid |33|
 :pattern ( (|$IsValid'bv128'| v@@11))
)))
(assert (forall ((v1@@0 T@Vec_11000) (v2@@0 T@Vec_11000) ) (! (= (|$IsEqual'vec'u8''| v1@@0 v2@@0) (|$IsEqual'vec'u8''| ($1_hash_sha2 v1@@0) ($1_hash_sha2 v2@@0)))
 :qid |outputbpl.4090:15|
 :skolemid |128|
 :pattern ( ($1_hash_sha2 v1@@0) ($1_hash_sha2 v2@@0))
)))
(assert (forall ((v1@@1 T@Vec_11000) (v2@@1 T@Vec_11000) ) (! (= (|$IsEqual'vec'u8''| v1@@1 v2@@1) (|$IsEqual'vec'u8''| ($1_hash_sha3 v1@@1) ($1_hash_sha3 v2@@1)))
 :qid |outputbpl.4106:15|
 :skolemid |129|
 :pattern ( ($1_hash_sha3 v1@@1) ($1_hash_sha3 v2@@1))
)))
(assert (forall ((v@@12 Int) ) (! (= (|$IsValid'u8'| v@@12)  (and (>= v@@12 $MIN_U8) (<= v@@12 $MAX_U8)))
 :qid |outputbpl.287:23|
 :skolemid |8|
 :pattern ( (|$IsValid'u8'| v@@12))
)))
(assert (forall ((v@@13 Int) ) (! (= (|$IsValid'u16'| v@@13)  (and (>= v@@13 $MIN_U16) (<= v@@13 $MAX_U16)))
 :qid |outputbpl.342:24|
 :skolemid |9|
 :pattern ( (|$IsValid'u16'| v@@13))
)))
(assert (forall ((v@@14 Int) ) (! (= (|$IsValid'u32'| v@@14)  (and (>= v@@14 $MIN_U32) (<= v@@14 $MAX_U32)))
 :qid |outputbpl.397:24|
 :skolemid |10|
 :pattern ( (|$IsValid'u32'| v@@14))
)))
(assert (forall ((v@@15 Int) ) (! (= (|$IsValid'u64'| v@@15)  (and (>= v@@15 $MIN_U64) (<= v@@15 $MAX_U64)))
 :qid |outputbpl.452:24|
 :skolemid |11|
 :pattern ( (|$IsValid'u64'| v@@15))
)))
(assert (forall ((v@@16 Int) ) (! (= (|$IsValid'u128'| v@@16)  (and (>= v@@16 $MIN_U128) (<= v@@16 $MAX_U128)))
 :qid |outputbpl.507:25|
 :skolemid |12|
 :pattern ( (|$IsValid'u128'| v@@16))
)))
(assert (forall ((v@@17 Int) ) (! (= (|$IsValid'u256'| v@@17)  (and (>= v@@17 $MIN_U256) (<= v@@17 $MAX_U256)))
 :qid |outputbpl.562:25|
 :skolemid |13|
 :pattern ( (|$IsValid'u256'| v@@17))
)))
(assert (forall ((v@@18 Int) ) (! (= (|$IsValid'i8'| v@@18)  (and (>= v@@18 $MIN_I8) (<= v@@18 $MAX_I8)))
 :qid |outputbpl.617:23|
 :skolemid |14|
 :pattern ( (|$IsValid'i8'| v@@18))
)))
(assert (forall ((v@@19 Int) ) (! (= (|$IsValid'i16'| v@@19)  (and (>= v@@19 $MIN_I16) (<= v@@19 $MAX_I16)))
 :qid |outputbpl.672:24|
 :skolemid |15|
 :pattern ( (|$IsValid'i16'| v@@19))
)))
(assert (forall ((v@@20 Int) ) (! (= (|$IsValid'i32'| v@@20)  (and (>= v@@20 $MIN_I32) (<= v@@20 $MAX_I32)))
 :qid |outputbpl.727:24|
 :skolemid |16|
 :pattern ( (|$IsValid'i32'| v@@20))
)))
(assert (forall ((v@@21 Int) ) (! (= (|$IsValid'i64'| v@@21)  (and (>= v@@21 $MIN_I64) (<= v@@21 $MAX_I64)))
 :qid |outputbpl.782:24|
 :skolemid |17|
 :pattern ( (|$IsValid'i64'| v@@21))
)))
(assert (forall ((v@@22 Int) ) (! (= (|$IsValid'i128'| v@@22)  (and (>= v@@22 $MIN_I128) (<= v@@22 $MAX_I128)))
 :qid |outputbpl.837:25|
 :skolemid |18|
 :pattern ( (|$IsValid'i128'| v@@22))
)))
(assert (forall ((v@@23 Int) ) (! (= (|$IsValid'i256'| v@@23)  (and (>= v@@23 $MIN_I256) (<= v@@23 $MAX_I256)))
 :qid |outputbpl.892:25|
 :skolemid |19|
 :pattern ( (|$IsValid'i256'| v@@23))
)))
(assert (forall ((v@@24 T@Vec_11000) (i@@10 Int) ) (! (= (InRangeVec_19336 v@@24 i@@10)  (and (>= i@@10 0) (< i@@10 (|l#Vec_11000| v@@24))))
 :qid |outputbpl.123:24|
 :skolemid |3|
 :pattern ( (InRangeVec_19336 v@@24 i@@10))
)))
(assert (forall ((r T@$Range) (i@@11 Int) ) (! (= ($InRange r i@@11)  (and (<= (|lb#$Range| r) i@@11) (< i@@11 (|ub#$Range| r))))
 :qid |outputbpl.2051:19|
 :skolemid |37|
 :pattern ( ($InRange r i@@11))
)))
(assert (= $MAX_U32 4294967295))
(assert (= $MIN_U8 0))
(assert (= $MIN_U16 0))
(assert (= $MIN_U32 0))
(assert (= $MIN_U64 0))
(assert (= $MIN_U128 0))
(assert (= $MIN_U256 0))
(assert (= $MAX_I8 127))
(assert (= $MAX_U8 255))
(assert (= $MAX_U64 18446744073709551615))
(assert (= $MAX_I64 9223372036854775807))
(assert (= $MAX_I16 32767))
(assert (= $MAX_U16 65535))
(assert (= $MAX_U256 115792089237316195423570985008687907853269984665640564039457584007913129639935))
(assert (= $MAX_I256 57896044618658097711785492504343953926634992332820282019728792003956564819967))
(assert (= $EXEC_FAILURE_CODE (- 0 1)))
(assert (= $MIN_I8 (- 0 128)))
(assert (= $MIN_I64 (- 0 9223372036854775808)))
(assert (= $MIN_I16 (- 0 32768)))
(assert (= $MIN_I256 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)))
; Valid

