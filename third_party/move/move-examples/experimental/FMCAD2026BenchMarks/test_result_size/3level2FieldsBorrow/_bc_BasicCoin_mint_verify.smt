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
(declare-sort T@T_11073 0)
(declare-sort T@T2_11267 0)
(declare-sort |T@[Int]Bool| 0)
(declare-sort |T@#0| 0)
(declare-sort |T@[Int]#0| 0)
(declare-sort |T@[Int]$bc_BasicCoin_Balance'#0'| 0)
(declare-datatypes ((T@$Memory_56317 0)) ((($Memory_56317 (|domain#$Memory_56317| |T@[Int]Bool|) (|contents#$Memory_56317| |T@[Int]#0|) ) ) ))
(declare-datatypes ((T@$bc_ProphecyBenchmark3Levels2Fields_Node1 0)) ((($bc_ProphecyBenchmark3Levels2Fields_Node1 (|$v0#$bc_ProphecyBenchmark3Levels2Fields_Node1| Int) (|$v1#$bc_ProphecyBenchmark3Levels2Fields_Node1| Int) (|$v2#$bc_ProphecyBenchmark3Levels2Fields_Node1| Int) (|$v3#$bc_ProphecyBenchmark3Levels2Fields_Node1| Int) (|$v4#$bc_ProphecyBenchmark3Levels2Fields_Node1| Int) (|$v5#$bc_ProphecyBenchmark3Levels2Fields_Node1| Int) (|$v6#$bc_ProphecyBenchmark3Levels2Fields_Node1| Int) (|$v7#$bc_ProphecyBenchmark3Levels2Fields_Node1| Int) ) ) ))
(declare-datatypes ((T@$bc_ProphecyBenchmark3Levels2Fields_Node2 0)) ((($bc_ProphecyBenchmark3Levels2Fields_Node2 (|$v0#$bc_ProphecyBenchmark3Levels2Fields_Node2| T@$bc_ProphecyBenchmark3Levels2Fields_Node1) (|$v1#$bc_ProphecyBenchmark3Levels2Fields_Node2| T@$bc_ProphecyBenchmark3Levels2Fields_Node1) (|$v2#$bc_ProphecyBenchmark3Levels2Fields_Node2| T@$bc_ProphecyBenchmark3Levels2Fields_Node1) (|$v3#$bc_ProphecyBenchmark3Levels2Fields_Node2| T@$bc_ProphecyBenchmark3Levels2Fields_Node1) (|$v4#$bc_ProphecyBenchmark3Levels2Fields_Node2| T@$bc_ProphecyBenchmark3Levels2Fields_Node1) (|$v5#$bc_ProphecyBenchmark3Levels2Fields_Node2| T@$bc_ProphecyBenchmark3Levels2Fields_Node1) (|$v6#$bc_ProphecyBenchmark3Levels2Fields_Node2| T@$bc_ProphecyBenchmark3Levels2Fields_Node1) (|$v7#$bc_ProphecyBenchmark3Levels2Fields_Node2| T@$bc_ProphecyBenchmark3Levels2Fields_Node1) ) ) ))
(declare-datatypes ((T@$bc_ProphecyBenchmark3Levels2Fields_Node3 0)) ((($bc_ProphecyBenchmark3Levels2Fields_Node3 (|$v0#$bc_ProphecyBenchmark3Levels2Fields_Node3| T@$bc_ProphecyBenchmark3Levels2Fields_Node2) (|$v1#$bc_ProphecyBenchmark3Levels2Fields_Node3| T@$bc_ProphecyBenchmark3Levels2Fields_Node2) (|$v2#$bc_ProphecyBenchmark3Levels2Fields_Node3| T@$bc_ProphecyBenchmark3Levels2Fields_Node2) (|$v3#$bc_ProphecyBenchmark3Levels2Fields_Node3| T@$bc_ProphecyBenchmark3Levels2Fields_Node2) (|$v4#$bc_ProphecyBenchmark3Levels2Fields_Node3| T@$bc_ProphecyBenchmark3Levels2Fields_Node2) (|$v5#$bc_ProphecyBenchmark3Levels2Fields_Node3| T@$bc_ProphecyBenchmark3Levels2Fields_Node2) (|$v6#$bc_ProphecyBenchmark3Levels2Fields_Node3| T@$bc_ProphecyBenchmark3Levels2Fields_Node2) (|$v7#$bc_ProphecyBenchmark3Levels2Fields_Node3| T@$bc_ProphecyBenchmark3Levels2Fields_Node2) ) ) ))
(declare-datatypes ((|T@$bc_BasicCoin_Coin'#0'| 0)) (((|$bc_BasicCoin_Coin'#0'| (|$value#$bc_BasicCoin_Coin'#0'| Int) ) ) ))
(declare-datatypes ((|T@$bc_BasicCoin_Balance'#0'| 0)) (((|$bc_BasicCoin_Balance'#0'| (|$coin#$bc_BasicCoin_Balance'#0'| |T@$bc_BasicCoin_Coin'#0'|) ) ) ))
(declare-datatypes ((T@$Memory_56677 0)) ((($Memory_56677 (|domain#$Memory_56677| |T@[Int]Bool|) (|contents#$Memory_56677| |T@[Int]$bc_BasicCoin_Balance'#0'|) ) ) ))
(declare-datatypes ((T@Vec_11028 0)) (((Vec_11028 (|v#Vec_11028| |T@[Int]Int|) (|l#Vec_11028| Int) ) ) ))
(declare-datatypes ((T@$TypeParamInfo 0)) ((($TypeParamBool ) ($TypeParamU8 ) ($TypeParamU16 ) ($TypeParamU32 ) ($TypeParamU64 ) ($TypeParamU128 ) ($TypeParamU256 ) ($TypeParamI8 ) ($TypeParamI16 ) ($TypeParamI32 ) ($TypeParamI64 ) ($TypeParamI128 ) ($TypeParamI256 ) ($TypeParamAddress ) ($TypeParamSigner ) ($TypeParamVector (|e#$TypeParamVector| T@$TypeParamInfo) ) ($TypeParamStruct (|a#$TypeParamStruct| Int) (|m#$TypeParamStruct| T@Vec_11028) (|s#$TypeParamStruct| T@Vec_11028) ) ) ))
(declare-datatypes ((T@$signer 0)) ((($signer (|$addr#$signer| Int) ) ($permissioned_signer (|$addr#$permissioned_signer| Int) (|$permission_addr#$permissioned_signer| Int) ) ) ))
(declare-datatypes ((T@$Location 0)) ((($Global (|a#$Global| Int) ) ($Local (|i#$Local| Int) ) ($Param (|i#$Param| Int) ) ($Uninitialized ) ) ))
(declare-datatypes ((T@$Mutation_64216 0)) ((($Mutation_64216 (|l#$Mutation_64216| T@$Location) (|p#$Mutation_64216| T@Vec_11028) (|v#$Mutation_64216| T@$bc_ProphecyBenchmark3Levels2Fields_Node1) (|v_final#$Mutation_64216| T@$bc_ProphecyBenchmark3Levels2Fields_Node1) ) ) ))
(declare-datatypes ((T@$Mutation_64193 0)) ((($Mutation_64193 (|l#$Mutation_64193| T@$Location) (|p#$Mutation_64193| T@Vec_11028) (|v#$Mutation_64193| T@$bc_ProphecyBenchmark3Levels2Fields_Node2) (|v_final#$Mutation_64193| T@$bc_ProphecyBenchmark3Levels2Fields_Node2) ) ) ))
(declare-datatypes ((T@$Mutation_64170 0)) ((($Mutation_64170 (|l#$Mutation_64170| T@$Location) (|p#$Mutation_64170| T@Vec_11028) (|v#$Mutation_64170| T@$bc_ProphecyBenchmark3Levels2Fields_Node3) (|v_final#$Mutation_64170| T@$bc_ProphecyBenchmark3Levels2Fields_Node3) ) ) ))
(declare-datatypes ((T@$Mutation_57370 0)) ((($Mutation_57370 (|l#$Mutation_57370| T@$Location) (|p#$Mutation_57370| T@Vec_11028) (|v#$Mutation_57370| |T@$bc_BasicCoin_Coin'#0'|) (|v_final#$Mutation_57370| |T@$bc_BasicCoin_Coin'#0'|) ) ) ))
(declare-datatypes ((T@$Mutation_57347 0)) ((($Mutation_57347 (|l#$Mutation_57347| T@$Location) (|p#$Mutation_57347| T@Vec_11028) (|v#$Mutation_57347| |T@$bc_BasicCoin_Balance'#0'|) (|v_final#$Mutation_57347| |T@$bc_BasicCoin_Balance'#0'|) ) ) ))
(declare-datatypes ((T@$Mutation_21031 0)) ((($Mutation_21031 (|l#$Mutation_21031| T@$Location) (|p#$Mutation_21031| T@Vec_11028) (|v#$Mutation_21031| Int) (|v_final#$Mutation_21031| Int) ) ) ))
(declare-datatypes ((T@$Mutation_49529 0)) ((($Mutation_49529 (|l#$Mutation_49529| T@$Location) (|p#$Mutation_49529| T@Vec_11028) (|v#$Mutation_49529| T@Vec_11028) (|v_final#$Mutation_49529| T@Vec_11028) ) ) ))
(declare-datatypes ((T@$Mutation_36883 0)) ((($Mutation_36883 (|l#$Mutation_36883| T@$Location) (|p#$Mutation_36883| T@Vec_11028) (|v#$Mutation_36883| T@T2_11267) (|v_final#$Mutation_36883| T@T2_11267) ) ) ))
(declare-datatypes ((T@$Mutation_36750 0)) ((($Mutation_36750 (|l#$Mutation_36750| T@$Location) (|p#$Mutation_36750| T@Vec_11028) (|v#$Mutation_36750| T@T_11073) (|v_final#$Mutation_36750| T@T_11073) ) ) ))
(declare-datatypes ((T@$Range 0)) ((($Range (|lb#$Range| Int) (|ub#$Range| Int) ) ) ))
(declare-fun $MAX_U128 () Int)
(declare-fun $MAX_I128 () Int)
(declare-fun $TypeName (T@$TypeParamInfo) T@Vec_11028)
(declare-fun |$IsEqual'vec'u8''| (T@Vec_11028 T@Vec_11028) Bool)
(declare-fun |Store__T@[Int]Int_| (|T@[Int]Int| Int Int) |T@[Int]Int|)
(declare-fun |Select__T@[Int]Int_| (|T@[Int]Int| Int) Int)
(assert (forall ( ( ?x0 |T@[Int]Int|) ( ?x1 Int) ( ?x2 Int)) (! (= (|Select__T@[Int]Int_| (|Store__T@[Int]Int_| ?x0 ?x1 ?x2) ?x1)  ?x2) :weight 0)))
(assert (forall ( ( ?x0 |T@[Int]Int|) ( ?x1 Int) ( ?y1 Int) ( ?x2 Int)) (! (=>  (not (= ?x1 ?y1)) (= (|Select__T@[Int]Int_| (|Store__T@[Int]Int_| ?x0 ?x1 ?x2) ?y1) (|Select__T@[Int]Int_| ?x0 ?y1))) :weight 0)))
(declare-fun MapConstVec_19835 (Int) |T@[Int]Int|)
(declare-fun DefaultVecElem_19835 () Int)
(declare-fun $MIN_I128 () Int)
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
(declare-fun $ConstMemoryDomain (Bool) |T@[Int]Bool|)
(declare-fun |lambda#4| (Bool) |T@[Int]Bool|)
(declare-fun InRangeVec_19490 (T@Vec_11028 Int) Bool)
(declare-fun |$IsPrefix'vec'u8''| (T@Vec_11028 T@Vec_11028) Bool)
(declare-fun DefaultTableKeyExistsArray_990 () |T@[Int]Bool|)
(declare-fun IndexOfVec_11028 (T@Vec_11028 Int) Int)
(declare-fun $1_Signature_$ed25519_verify (T@Vec_11028 T@Vec_11028 T@Vec_11028) Bool)
(declare-fun |lambda#0| (Int Int Int |T@[Int]Int| |T@[Int]Int| Int Int) |T@[Int]Int|)
(declare-fun |lambda#3| (Int Int Int |T@[Int]Int| |T@[Int]Int| Int Int) |T@[Int]Int|)
(declare-fun |$IsValid'bv32'| ((_ BitVec 32)) Bool)
(declare-fun |$IsValid'address'| (Int) Bool)
(declare-fun |$IsSuffix'vec'u8''| (T@Vec_11028 T@Vec_11028) Bool)
(declare-fun |lambda#2| (Int Int |T@[Int]Int| Int Int) |T@[Int]Int|)
(declare-fun $shl (Int Int) Int)
(declare-fun $castBv64to8 ((_ BitVec 64)) (_ BitVec 8))
(declare-fun |$Arbitrary_value_of'bv8'| () (_ BitVec 8))
(declare-fun $castBv256to8 ((_ BitVec 256)) (_ BitVec 8))
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
(declare-fun |$IsValid'vec'u8''| (T@Vec_11028) Bool)
(declare-fun |$IsValid'u64'| (Int) Bool)
(declare-fun |$IsValid'u8'| (Int) Bool)
(declare-fun |Select__T@[Int]Bool_| (|T@[Int]Bool| Int) Bool)
(declare-fun |$IsValid'num'| (Int) Bool)
(declare-fun $castBv8to64 ((_ BitVec 8)) (_ BitVec 64))
(declare-fun $castBv64to256 ((_ BitVec 64)) (_ BitVec 256))
(declare-fun $castBv8to256 ((_ BitVec 8)) (_ BitVec 256))
(declare-fun $undefined_int () Int)
(declare-fun |$IsValid'$bc_BasicCoin_Balance'#0''| (|T@$bc_BasicCoin_Balance'#0'|) Bool)
(declare-fun |$IsValid'$bc_BasicCoin_Coin'#0''| (|T@$bc_BasicCoin_Coin'#0'|) Bool)
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
(declare-fun |$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node1'| (T@$bc_ProphecyBenchmark3Levels2Fields_Node1) Bool)
(declare-fun |$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node2'| (T@$bc_ProphecyBenchmark3Levels2Fields_Node2) Bool)
(declare-fun |$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node3'| (T@$bc_ProphecyBenchmark3Levels2Fields_Node3) Bool)
(declare-fun $castBv8to8 ((_ BitVec 8)) (_ BitVec 8))
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
(declare-fun $1_Signature_$ed25519_validate_pubkey (T@Vec_11028) Bool)
(declare-fun |$IsValid'bv8'| ((_ BitVec 8)) Bool)
(declare-fun |$IsValid'bv64'| ((_ BitVec 64)) Bool)
(declare-fun |$IsValid'bv16'| ((_ BitVec 16)) Bool)
(declare-fun |$IsValid'bv256'| ((_ BitVec 256)) Bool)
(declare-fun |$IndexOfVec'u8'| (T@Vec_11028 Int) Int)
(declare-fun |$IsValid'bv128'| ((_ BitVec 128)) Bool)
(declare-fun $1_hash_sha2 (T@Vec_11028) T@Vec_11028)
(declare-fun $1_hash_sha3 (T@Vec_11028) T@Vec_11028)
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
(assert (forall ((t T@$TypeParamInfo) ) (!  (=> (is-$TypeParamU128 t) (|$IsEqual'vec'u8''| ($TypeName t) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 117) 1 49) 2 50) 3 56) 4)))
 :qid |outputbpl.4348:15|
 :skolemid |147|
 :pattern ( ($TypeName t))
)))
(assert (= $MIN_I128 (- 0 170141183460469231731687303715884105728)))
(assert (forall ((t@@0 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamU256 t@@0) (|$IsEqual'vec'u8''| ($TypeName t@@0) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 117) 1 50) 2 53) 3 54) 4)))
 :qid |outputbpl.4350:15|
 :skolemid |149|
 :pattern ( ($TypeName t@@0))
)))
(assert (forall ((|l#0| Int) (|l#1| Int) (|l#2| |T@[Int]Int|) (|l#3| Int) (|l#4| Int) (|l#5| Int) (i Int) ) (! (= (|Select__T@[Int]Int_| (|lambda#1| |l#0| |l#1| |l#2| |l#3| |l#4| |l#5|) i) (ite  (and (<= |l#0| i) (< i |l#1|)) (|Select__T@[Int]Int_| |l#2| (- (- |l#3| i) |l#4|)) |l#5|))
 :qid |outputbpl.83:30|
 :skolemid |184|
 :pattern ( (|Select__T@[Int]Int_| (|lambda#1| |l#0| |l#1| |l#2| |l#3| |l#4| |l#5|) i))
)))
(assert (forall ((src1 Int) (p Int) ) (! (= ($shr src1 p) (div src1 ($pow 2 p)))
 :qid |outputbpl.1010:15|
 :skolemid |22|
 :pattern ( ($shr src1 p))
)))
(assert (forall ((src1@@0 Int) (p@@0 Int) ) (! (= ($shlU8 src1@@0 p@@0) (mod (* src1@@0 ($pow 2 p@@0)) (+ $MAX_U8 1)))
 :qid |outputbpl.1025:17|
 :skolemid |23|
 :pattern ( ($shlU8 src1@@0 p@@0))
)))
(assert (forall ((src1@@1 Int) (p@@1 Int) ) (! (= ($shlU16 src1@@1 p@@1) (mod (* src1@@1 ($pow 2 p@@1)) (+ $MAX_U16 1)))
 :qid |outputbpl.1056:18|
 :skolemid |24|
 :pattern ( ($shlU16 src1@@1 p@@1))
)))
(assert (forall ((src1@@2 Int) (p@@2 Int) ) (! (= ($shlU32 src1@@2 p@@2) (mod (* src1@@2 ($pow 2 p@@2)) (+ $MAX_U32 1)))
 :qid |outputbpl.1087:18|
 :skolemid |25|
 :pattern ( ($shlU32 src1@@2 p@@2))
)))
(assert (forall ((src1@@3 Int) (p@@3 Int) ) (! (= ($shlU64 src1@@3 p@@3) (mod (* src1@@3 ($pow 2 p@@3)) (+ $MAX_U64 1)))
 :qid |outputbpl.1118:18|
 :skolemid |26|
 :pattern ( ($shlU64 src1@@3 p@@3))
)))
(assert (forall ((src1@@4 Int) (p@@4 Int) ) (! (= ($shlU128 src1@@4 p@@4) (mod (* src1@@4 ($pow 2 p@@4)) (+ $MAX_U128 1)))
 :qid |outputbpl.1149:19|
 :skolemid |27|
 :pattern ( ($shlU128 src1@@4 p@@4))
)))
(assert (forall ((src1@@5 Int) (p@@5 Int) ) (! (= ($shlU256 src1@@5 p@@5) (mod (* src1@@5 ($pow 2 p@@5)) (+ $MAX_U256 1)))
 :qid |outputbpl.1180:19|
 :skolemid |28|
 :pattern ( ($shlU256 src1@@5 p@@5))
)))
(assert (= ($ConstMemoryDomain false) (|lambda#4| false)))
(assert (= ($ConstMemoryDomain true) (|lambda#4| true)))
(assert (forall ((v1 T@Vec_11028) (v2 T@Vec_11028) ) (! (= (|$IsEqual'vec'u8''| v1 v2)  (and (= (|l#Vec_11028| v1) (|l#Vec_11028| v2)) (forall ((i@@0 Int) ) (!  (=> (InRangeVec_19490 v1 i@@0) (= (|Select__T@[Int]Int_| (|v#Vec_11028| v1) i@@0) (|Select__T@[Int]Int_| (|v#Vec_11028| v2) i@@0)))
 :qid |outputbpl.3825:13|
 :skolemid |122|
))))
 :qid |outputbpl.3823:28|
 :skolemid |123|
 :pattern ( (|$IsEqual'vec'u8''| v1 v2))
)))
(assert (forall ((v T@Vec_11028) (prefix T@Vec_11028) ) (! (= (|$IsPrefix'vec'u8''| v prefix)  (and (>= (|l#Vec_11028| v) (|l#Vec_11028| prefix)) (forall ((i@@1 Int) ) (!  (=> (InRangeVec_19490 prefix i@@1) (= (|Select__T@[Int]Int_| (|v#Vec_11028| v) i@@1) (|Select__T@[Int]Int_| (|v#Vec_11028| prefix) i@@1)))
 :qid |outputbpl.3831:13|
 :skolemid |124|
))))
 :qid |outputbpl.3829:29|
 :skolemid |125|
 :pattern ( (|$IsPrefix'vec'u8''| v prefix))
)))
(assert (= DefaultTableKeyExistsArray_990 (|lambda#4| false)))
(assert (forall ((v@@0 T@Vec_11028) (e Int) ) (! (let ((i@@2 (IndexOfVec_11028 v@@0 e)))
(ite  (not (exists ((i@@3 Int) ) (!  (and (InRangeVec_19490 v@@0 i@@3) (= (|Select__T@[Int]Int_| (|v#Vec_11028| v@@0) i@@3) e))
 :qid |outputbpl.110:13|
 :skolemid |0|
))) (= i@@2 (- 0 1))  (and (and (InRangeVec_19490 v@@0 i@@2) (= (|Select__T@[Int]Int_| (|v#Vec_11028| v@@0) i@@2) e)) (forall ((j Int) ) (!  (=> (and (>= j 0) (< j i@@2)) (not (= (|Select__T@[Int]Int_| (|v#Vec_11028| v@@0) j) e)))
 :qid |outputbpl.118:17|
 :skolemid |1|
)))))
 :qid |outputbpl.114:32|
 :skolemid |2|
 :pattern ( (IndexOfVec_11028 v@@0 e))
)))
(assert (forall ((t@@1 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamI128 t@@1) (|$IsEqual'vec'u8''| ($TypeName t@@1) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 105) 1 49) 2 50) 3 56) 4)))
 :qid |outputbpl.4360:15|
 :skolemid |159|
 :pattern ( ($TypeName t@@1))
)))
(assert (forall ((t@@2 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamI256 t@@2) (|$IsEqual'vec'u8''| ($TypeName t@@2) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 105) 1 50) 2 53) 3 54) 4)))
 :qid |outputbpl.4362:15|
 :skolemid |161|
 :pattern ( ($TypeName t@@2))
)))
(assert (forall ((s1 T@Vec_11028) (s2 T@Vec_11028) (k1 T@Vec_11028) (k2 T@Vec_11028) (m1 T@Vec_11028) (m2 T@Vec_11028) ) (!  (=> (and (and (|$IsEqual'vec'u8''| s1 s2) (|$IsEqual'vec'u8''| k1 k2)) (|$IsEqual'vec'u8''| m1 m2)) (= ($1_Signature_$ed25519_verify s1 k1 m1) ($1_Signature_$ed25519_verify s2 k2 m2)))
 :qid |outputbpl.4277:15|
 :skolemid |136|
 :pattern ( ($1_Signature_$ed25519_verify s1 k1 m1) ($1_Signature_$ed25519_verify s2 k2 m2))
)))
(assert (forall ((|l#0@@0| Int) (|l#1@@0| Int) (|l#2@@0| Int) (|l#3@@0| |T@[Int]Int|) (|l#4@@0| |T@[Int]Int|) (|l#5@@0| Int) (|l#6| Int) (i@@4 Int) ) (! (= (|Select__T@[Int]Int_| (|lambda#0| |l#0@@0| |l#1@@0| |l#2@@0| |l#3@@0| |l#4@@0| |l#5@@0| |l#6|) i@@4) (ite  (and (>= i@@4 |l#0@@0|) (< i@@4 |l#1@@0|)) (ite (< i@@4 |l#2@@0|) (|Select__T@[Int]Int_| |l#3@@0| i@@4) (|Select__T@[Int]Int_| |l#4@@0| (- i@@4 |l#5@@0|))) |l#6|))
 :qid |outputbpl.74:19|
 :skolemid |183|
 :pattern ( (|Select__T@[Int]Int_| (|lambda#0| |l#0@@0| |l#1@@0| |l#2@@0| |l#3@@0| |l#4@@0| |l#5@@0| |l#6|) i@@4))
)))
(assert (forall ((|l#0@@1| Int) (|l#1@@1| Int) (|l#2@@1| Int) (|l#3@@1| |T@[Int]Int|) (|l#4@@1| |T@[Int]Int|) (|l#5@@1| Int) (|l#6@@0| Int) (j@@0 Int) ) (! (= (|Select__T@[Int]Int_| (|lambda#3| |l#0@@1| |l#1@@1| |l#2@@1| |l#3@@1| |l#4@@1| |l#5@@1| |l#6@@0|) j@@0) (ite  (and (>= j@@0 |l#0@@1|) (< j@@0 |l#1@@1|)) (ite (< j@@0 |l#2@@1|) (|Select__T@[Int]Int_| |l#3@@1| j@@0) (|Select__T@[Int]Int_| |l#4@@1| (+ j@@0 |l#5@@1|))) |l#6@@0|))
 :qid |outputbpl.64:20|
 :skolemid |186|
 :pattern ( (|Select__T@[Int]Int_| (|lambda#3| |l#0@@1| |l#1@@1| |l#2@@1| |l#3@@1| |l#4@@1| |l#5@@1| |l#6@@0|) j@@0))
)))
(assert (forall ((v@@1 (_ BitVec 32)) ) (! (= (|$IsValid'bv32'| v@@1)  (and (bvuge v@@1 #x00000000) (bvule v@@1 #x7fffffff)))
 :qid |outputbpl.1657:25|
 :skolemid |31|
 :pattern ( (|$IsValid'bv32'| v@@1))
)))
(assert (forall ((v@@2 Int) ) (! (= (|$IsValid'address'| v@@2) (>= v@@2 0))
 :qid |outputbpl.2069:28|
 :skolemid |36|
 :pattern ( (|$IsValid'address'| v@@2))
)))
(assert (forall ((t@@3 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamSigner t@@3) (|$IsEqual'vec'u8''| ($TypeName t@@3) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 115) 1 105) 2 103) 3 110) 4 101) 5 114) 6)))
 :qid |outputbpl.4366:15|
 :skolemid |165|
 :pattern ( ($TypeName t@@3))
)))
(assert (forall ((v@@3 T@Vec_11028) (suffix T@Vec_11028) ) (! (= (|$IsSuffix'vec'u8''| v@@3 suffix)  (and (>= (|l#Vec_11028| v@@3) (|l#Vec_11028| suffix)) (forall ((i@@5 Int) ) (!  (=> (InRangeVec_19490 suffix i@@5) (= (|Select__T@[Int]Int_| (|v#Vec_11028| v@@3) (+ (- (|l#Vec_11028| v@@3) (|l#Vec_11028| suffix)) i@@5)) (|Select__T@[Int]Int_| (|v#Vec_11028| suffix) i@@5)))
 :qid |outputbpl.3837:13|
 :skolemid |126|
))))
 :qid |outputbpl.3835:29|
 :skolemid |127|
 :pattern ( (|$IsSuffix'vec'u8''| v@@3 suffix))
)))
(assert (forall ((|l#0@@2| Int) (|l#1@@2| Int) (|l#2@@2| |T@[Int]Int|) (|l#3@@2| Int) (|l#4@@2| Int) (k Int) ) (! (= (|Select__T@[Int]Int_| (|lambda#2| |l#0@@2| |l#1@@2| |l#2@@2| |l#3@@2| |l#4@@2|) k) (ite  (and (<= |l#0@@2| k) (< k |l#1@@2|)) (|Select__T@[Int]Int_| |l#2@@2| (+ |l#3@@2| k)) |l#4@@2|))
 :qid |outputbpl.91:14|
 :skolemid |185|
 :pattern ( (|Select__T@[Int]Int_| (|lambda#2| |l#0@@2| |l#1@@2| |l#2@@2| |l#3@@2| |l#4@@2|) k))
)))
(assert (forall ((src1@@6 Int) (p@@6 Int) ) (! (= ($shl src1@@6 p@@6) (* src1@@6 ($pow 2 p@@6)))
 :qid |outputbpl.1006:15|
 :skolemid |21|
 :pattern ( ($shl src1@@6 p@@6))
)))
(assert (forall ((t@@4 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@4) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 117) 1 49) 2 54) 3)) (is-$TypeParamU16 t@@4))
 :qid |outputbpl.4343:15|
 :skolemid |142|
 :pattern ( ($TypeName t@@4))
)))
(assert (forall ((t@@5 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@5) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 117) 1 51) 2 50) 3)) (is-$TypeParamU32 t@@5))
 :qid |outputbpl.4345:15|
 :skolemid |144|
 :pattern ( ($TypeName t@@5))
)))
(assert (forall ((t@@6 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@6) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 117) 1 54) 2 52) 3)) (is-$TypeParamU64 t@@6))
 :qid |outputbpl.4347:15|
 :skolemid |146|
 :pattern ( ($TypeName t@@6))
)))
(assert (forall ((t@@7 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamAddress t@@7) (|$IsEqual'vec'u8''| ($TypeName t@@7) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 97) 1 100) 2 100) 3 114) 4 101) 5 115) 6 115) 7)))
 :qid |outputbpl.4364:15|
 :skolemid |163|
 :pattern ( ($TypeName t@@7))
)))
(assert (forall ((t@@8 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamVector t@@8) (|$IsEqual'vec'u8''| ($TypeName t@@8) (let ((m2@@0 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 62) 1))))
(let ((l2 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 62) 1))))
(let ((m1@@0 (|v#Vec_11028| (let ((m2@@1 (|v#Vec_11028| ($TypeName (|e#$TypeParamVector| t@@8)))))
(let ((l2@@0 (|l#Vec_11028| ($TypeName (|e#$TypeParamVector| t@@8)))))
(let ((m1@@1 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 118) 1 101) 2 99) 3 116) 4 111) 5 114) 6 60) 7))))
(let ((l1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 118) 1 101) 2 99) 3 116) 4 111) 5 114) 6 60) 7))))
(Vec_11028 (|lambda#0| 0 (+ l1 l2@@0) l1 m1@@1 m2@@1 l1 DefaultVecElem_19835) (+ l1 l2@@0)))))))))
(let ((l1@@0 (|l#Vec_11028| (let ((m2@@1 (|v#Vec_11028| ($TypeName (|e#$TypeParamVector| t@@8)))))
(let ((l2@@0 (|l#Vec_11028| ($TypeName (|e#$TypeParamVector| t@@8)))))
(let ((m1@@1 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 118) 1 101) 2 99) 3 116) 4 111) 5 114) 6 60) 7))))
(let ((l1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 118) 1 101) 2 99) 3 116) 4 111) 5 114) 6 60) 7))))
(Vec_11028 (|lambda#0| 0 (+ l1 l2@@0) l1 m1@@1 m2@@1 l1 DefaultVecElem_19835) (+ l1 l2@@0)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@0 l2) l1@@0 m1@@0 m2@@0 l1@@0 DefaultVecElem_19835) (+ l1@@0 l2))))))))
 :qid |outputbpl.4368:15|
 :skolemid |167|
 :pattern ( ($TypeName t@@8))
)))
(assert (forall ((src (_ BitVec 64)) ) (! (= ($castBv64to8 src) (ite (bvugt src #x00000000000000ff) |$Arbitrary_value_of'bv8'| ((_ extract 7 0) src)))
 :qid |outputbpl.2505:23|
 :skolemid |48|
 :pattern ( ($castBv64to8 src))
)))
(assert (forall ((src@@0 (_ BitVec 256)) ) (! (= ($castBv256to8 src@@0) (ite (bvugt src@@0 #x00000000000000000000000000000000000000000000000000000000000000ff) |$Arbitrary_value_of'bv8'| ((_ extract 7 0) src@@0)))
 :qid |outputbpl.2595:24|
 :skolemid |53|
 :pattern ( ($castBv256to8 src@@0))
)))
(assert (forall ((src@@1 (_ BitVec 256)) ) (! (= ($castBv256to64 src@@1) (ite (bvugt src@@1 #x000000000000000000000000000000000000000000000000ffffffffffffffff) |$Arbitrary_value_of'bv64'| ((_ extract 63 0) src@@1)))
 :qid |outputbpl.3315:25|
 :skolemid |92|
 :pattern ( ($castBv256to64 src@@1))
)))
(assert (= $MAX_I32 2147483647))
(assert (= $MIN_I32 (- 0 2147483648)))
(assert (forall ((t@@9 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@9) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 98) 1 111) 2 111) 3 108) 4)) (is-$TypeParamBool t@@9))
 :qid |outputbpl.4339:15|
 :skolemid |138|
 :pattern ( ($TypeName t@@9))
)))
(assert (forall ((src1@@7 (_ BitVec 8)) (src2 (_ BitVec 16)) ) (! (= ($shlBv8From16 src1@@7 src2) (bvshl src1@@7 ((_ extract 7 0) src2)))
 :qid |outputbpl.2424:24|
 :skolemid |44|
 :pattern ( ($shlBv8From16 src1@@7 src2))
)))
(assert (forall ((src1@@8 (_ BitVec 8)) (src2@@0 (_ BitVec 16)) ) (! (= ($shrBv8From16 src1@@8 src2@@0) (bvlshr src1@@8 ((_ extract 7 0) src2@@0)))
 :qid |outputbpl.2439:24|
 :skolemid |45|
 :pattern ( ($shrBv8From16 src1@@8 src2@@0))
)))
(assert (forall ((src1@@9 (_ BitVec 8)) (src2@@1 (_ BitVec 32)) ) (! (= ($shlBv8From32 src1@@9 src2@@1) (bvshl src1@@9 ((_ extract 7 0) src2@@1)))
 :qid |outputbpl.2465:24|
 :skolemid |46|
 :pattern ( ($shlBv8From32 src1@@9 src2@@1))
)))
(assert (forall ((src1@@10 (_ BitVec 8)) (src2@@2 (_ BitVec 32)) ) (! (= ($shrBv8From32 src1@@10 src2@@2) (bvlshr src1@@10 ((_ extract 7 0) src2@@2)))
 :qid |outputbpl.2480:24|
 :skolemid |47|
 :pattern ( ($shrBv8From32 src1@@10 src2@@2))
)))
(assert (forall ((src1@@11 (_ BitVec 8)) (src2@@3 (_ BitVec 64)) ) (! (= ($shlBv8From64 src1@@11 src2@@3) (bvshl src1@@11 ((_ extract 7 0) src2@@3)))
 :qid |outputbpl.2514:24|
 :skolemid |49|
 :pattern ( ($shlBv8From64 src1@@11 src2@@3))
)))
(assert (forall ((src1@@12 (_ BitVec 8)) (src2@@4 (_ BitVec 64)) ) (! (= ($shrBv8From64 src1@@12 src2@@4) (bvlshr src1@@12 ((_ extract 7 0) src2@@4)))
 :qid |outputbpl.2529:24|
 :skolemid |50|
 :pattern ( ($shrBv8From64 src1@@12 src2@@4))
)))
(assert (forall ((src1@@13 (_ BitVec 8)) (src2@@5 (_ BitVec 128)) ) (! (= ($shlBv8From128 src1@@13 src2@@5) (bvshl src1@@13 ((_ extract 7 0) src2@@5)))
 :qid |outputbpl.2555:25|
 :skolemid |51|
 :pattern ( ($shlBv8From128 src1@@13 src2@@5))
)))
(assert (forall ((src1@@14 (_ BitVec 8)) (src2@@6 (_ BitVec 128)) ) (! (= ($shrBv8From128 src1@@14 src2@@6) (bvlshr src1@@14 ((_ extract 7 0) src2@@6)))
 :qid |outputbpl.2570:25|
 :skolemid |52|
 :pattern ( ($shrBv8From128 src1@@14 src2@@6))
)))
(assert (forall ((src1@@15 (_ BitVec 8)) (src2@@7 (_ BitVec 256)) ) (! (= ($shlBv8From256 src1@@15 src2@@7) (bvshl src1@@15 ((_ extract 7 0) src2@@7)))
 :qid |outputbpl.2604:25|
 :skolemid |54|
 :pattern ( ($shlBv8From256 src1@@15 src2@@7))
)))
(assert (forall ((src1@@16 (_ BitVec 8)) (src2@@8 (_ BitVec 256)) ) (! (= ($shrBv8From256 src1@@16 src2@@8) (bvlshr src1@@16 ((_ extract 7 0) src2@@8)))
 :qid |outputbpl.2619:25|
 :skolemid |55|
 :pattern ( ($shrBv8From256 src1@@16 src2@@8))
)))
(assert (forall ((src1@@17 (_ BitVec 16)) (src2@@9 (_ BitVec 32)) ) (! (= ($shlBv16From32 src1@@17 src2@@9) (bvshl src1@@17 ((_ extract 15 0) src2@@9)))
 :qid |outputbpl.2719:25|
 :skolemid |60|
 :pattern ( ($shlBv16From32 src1@@17 src2@@9))
)))
(assert (forall ((src1@@18 (_ BitVec 16)) (src2@@10 (_ BitVec 32)) ) (! (= ($shrBv16From32 src1@@18 src2@@10) (bvlshr src1@@18 ((_ extract 15 0) src2@@10)))
 :qid |outputbpl.2734:25|
 :skolemid |61|
 :pattern ( ($shrBv16From32 src1@@18 src2@@10))
)))
(assert (forall ((src1@@19 (_ BitVec 16)) (src2@@11 (_ BitVec 64)) ) (! (= ($shlBv16From64 src1@@19 src2@@11) (bvshl src1@@19 ((_ extract 15 0) src2@@11)))
 :qid |outputbpl.2760:25|
 :skolemid |62|
 :pattern ( ($shlBv16From64 src1@@19 src2@@11))
)))
(assert (forall ((src1@@20 (_ BitVec 16)) (src2@@12 (_ BitVec 64)) ) (! (= ($shrBv16From64 src1@@20 src2@@12) (bvlshr src1@@20 ((_ extract 15 0) src2@@12)))
 :qid |outputbpl.2775:25|
 :skolemid |63|
 :pattern ( ($shrBv16From64 src1@@20 src2@@12))
)))
(assert (forall ((src1@@21 (_ BitVec 16)) (src2@@13 (_ BitVec 128)) ) (! (= ($shlBv16From128 src1@@21 src2@@13) (bvshl src1@@21 ((_ extract 15 0) src2@@13)))
 :qid |outputbpl.2801:26|
 :skolemid |64|
 :pattern ( ($shlBv16From128 src1@@21 src2@@13))
)))
(assert (forall ((src1@@22 (_ BitVec 16)) (src2@@14 (_ BitVec 128)) ) (! (= ($shrBv16From128 src1@@22 src2@@14) (bvlshr src1@@22 ((_ extract 15 0) src2@@14)))
 :qid |outputbpl.2816:26|
 :skolemid |65|
 :pattern ( ($shrBv16From128 src1@@22 src2@@14))
)))
(assert (forall ((src1@@23 (_ BitVec 16)) (src2@@15 (_ BitVec 256)) ) (! (= ($shlBv16From256 src1@@23 src2@@15) (bvshl src1@@23 ((_ extract 15 0) src2@@15)))
 :qid |outputbpl.2842:26|
 :skolemid |66|
 :pattern ( ($shlBv16From256 src1@@23 src2@@15))
)))
(assert (forall ((src1@@24 (_ BitVec 16)) (src2@@16 (_ BitVec 256)) ) (! (= ($shrBv16From256 src1@@24 src2@@16) (bvlshr src1@@24 ((_ extract 15 0) src2@@16)))
 :qid |outputbpl.2857:26|
 :skolemid |67|
 :pattern ( ($shrBv16From256 src1@@24 src2@@16))
)))
(assert (forall ((src1@@25 (_ BitVec 32)) (src2@@17 (_ BitVec 64)) ) (! (= ($shlBv32From64 src1@@25 src2@@17) (bvshl src1@@25 ((_ extract 31 0) src2@@17)))
 :qid |outputbpl.2994:25|
 :skolemid |74|
 :pattern ( ($shlBv32From64 src1@@25 src2@@17))
)))
(assert (forall ((src1@@26 (_ BitVec 32)) (src2@@18 (_ BitVec 64)) ) (! (= ($shrBv32From64 src1@@26 src2@@18) (bvlshr src1@@26 ((_ extract 31 0) src2@@18)))
 :qid |outputbpl.3009:25|
 :skolemid |75|
 :pattern ( ($shrBv32From64 src1@@26 src2@@18))
)))
(assert (forall ((src1@@27 (_ BitVec 32)) (src2@@19 (_ BitVec 128)) ) (! (= ($shlBv32From128 src1@@27 src2@@19) (bvshl src1@@27 ((_ extract 31 0) src2@@19)))
 :qid |outputbpl.3035:26|
 :skolemid |76|
 :pattern ( ($shlBv32From128 src1@@27 src2@@19))
)))
(assert (forall ((src1@@28 (_ BitVec 32)) (src2@@20 (_ BitVec 128)) ) (! (= ($shrBv32From128 src1@@28 src2@@20) (bvlshr src1@@28 ((_ extract 31 0) src2@@20)))
 :qid |outputbpl.3050:26|
 :skolemid |77|
 :pattern ( ($shrBv32From128 src1@@28 src2@@20))
)))
(assert (forall ((src1@@29 (_ BitVec 32)) (src2@@21 (_ BitVec 256)) ) (! (= ($shlBv32From256 src1@@29 src2@@21) (bvshl src1@@29 ((_ extract 31 0) src2@@21)))
 :qid |outputbpl.3076:26|
 :skolemid |78|
 :pattern ( ($shlBv32From256 src1@@29 src2@@21))
)))
(assert (forall ((src1@@30 (_ BitVec 32)) (src2@@22 (_ BitVec 256)) ) (! (= ($shrBv32From256 src1@@30 src2@@22) (bvlshr src1@@30 ((_ extract 31 0) src2@@22)))
 :qid |outputbpl.3091:26|
 :skolemid |79|
 :pattern ( ($shrBv32From256 src1@@30 src2@@22))
)))
(assert (forall ((src1@@31 (_ BitVec 64)) (src2@@23 (_ BitVec 128)) ) (! (= ($shlBv64From128 src1@@31 src2@@23) (bvshl src1@@31 ((_ extract 63 0) src2@@23)))
 :qid |outputbpl.3275:26|
 :skolemid |90|
 :pattern ( ($shlBv64From128 src1@@31 src2@@23))
)))
(assert (forall ((src1@@32 (_ BitVec 64)) (src2@@24 (_ BitVec 128)) ) (! (= ($shrBv64From128 src1@@32 src2@@24) (bvlshr src1@@32 ((_ extract 63 0) src2@@24)))
 :qid |outputbpl.3290:26|
 :skolemid |91|
 :pattern ( ($shrBv64From128 src1@@32 src2@@24))
)))
(assert (forall ((src1@@33 (_ BitVec 64)) (src2@@25 (_ BitVec 256)) ) (! (= ($shlBv64From256 src1@@33 src2@@25) (bvshl src1@@33 ((_ extract 63 0) src2@@25)))
 :qid |outputbpl.3324:26|
 :skolemid |93|
 :pattern ( ($shlBv64From256 src1@@33 src2@@25))
)))
(assert (forall ((src1@@34 (_ BitVec 64)) (src2@@26 (_ BitVec 256)) ) (! (= ($shrBv64From256 src1@@34 src2@@26) (bvlshr src1@@34 ((_ extract 63 0) src2@@26)))
 :qid |outputbpl.3339:26|
 :skolemid |94|
 :pattern ( ($shrBv64From256 src1@@34 src2@@26))
)))
(assert (forall ((src1@@35 (_ BitVec 128)) (src2@@27 (_ BitVec 256)) ) (! (= ($shlBv128From256 src1@@35 src2@@27) (bvshl src1@@35 ((_ extract 127 0) src2@@27)))
 :qid |outputbpl.3550:27|
 :skolemid |105|
 :pattern ( ($shlBv128From256 src1@@35 src2@@27))
)))
(assert (forall ((src1@@36 (_ BitVec 128)) (src2@@28 (_ BitVec 256)) ) (! (= ($shrBv128From256 src1@@36 src2@@28) (bvlshr src1@@36 ((_ extract 127 0) src2@@28)))
 :qid |outputbpl.3565:27|
 :skolemid |106|
 :pattern ( ($shrBv128From256 src1@@36 src2@@28))
)))
(assert (forall ((t@@10 T@$TypeParamInfo) ) (!  (=> (and (|$IsPrefix'vec'u8''| ($TypeName t@@10) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 118) 1 101) 2 99) 3 116) 4 111) 5 114) 6 60) 7)) (|$IsSuffix'vec'u8''| ($TypeName t@@10) (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 62) 1))) (is-$TypeParamVector t@@10))
 :qid |outputbpl.4369:15|
 :skolemid |168|
 :pattern ( ($TypeName t@@10))
)))
(assert (forall ((t@@11 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamI16 t@@11) (|$IsEqual'vec'u8''| ($TypeName t@@11) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 105) 1 49) 2 54) 3)))
 :qid |outputbpl.4354:15|
 :skolemid |153|
 :pattern ( ($TypeName t@@11))
)))
(assert (forall ((t@@12 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamI32 t@@12) (|$IsEqual'vec'u8''| ($TypeName t@@12) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 105) 1 51) 2 50) 3)))
 :qid |outputbpl.4356:15|
 :skolemid |155|
 :pattern ( ($TypeName t@@12))
)))
(assert (forall ((t@@13 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamI64 t@@13) (|$IsEqual'vec'u8''| ($TypeName t@@13) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 105) 1 54) 2 52) 3)))
 :qid |outputbpl.4358:15|
 :skolemid |157|
 :pattern ( ($TypeName t@@13))
)))
(assert (forall ((t@@14 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@14) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 115) 1 105) 2 103) 3 110) 4 101) 5 114) 6)) (is-$TypeParamSigner t@@14))
 :qid |outputbpl.4367:15|
 :skolemid |166|
 :pattern ( ($TypeName t@@14))
)))
(assert (forall ((v@@4 T@Vec_11028) ) (! (= (|$IsValid'vec'u8''| v@@4)  (and (|$IsValid'u64'| (|l#Vec_11028| v@@4)) (forall ((i@@6 Int) ) (!  (=> (InRangeVec_19490 v@@4 i@@6) (|$IsValid'u8'| (|Select__T@[Int]Int_| (|v#Vec_11028| v@@4) i@@6)))
 :qid |outputbpl.3843:13|
 :skolemid |128|
))))
 :qid |outputbpl.3841:28|
 :skolemid |129|
 :pattern ( (|$IsValid'vec'u8''| v@@4))
)))
(assert (forall ((|l#0@@3| Bool) (i@@7 Int) ) (! (= (|Select__T@[Int]Bool_| (|lambda#4| |l#0@@3|) i@@7) |l#0@@3|)
 :qid |outputbpl.194:57|
 :skolemid |187|
 :pattern ( (|Select__T@[Int]Bool_| (|lambda#4| |l#0@@3|) i@@7))
)))
(assert (forall ((v@@5 Int) ) (! (= (|$IsValid'num'| v@@5) true)
 :qid |outputbpl.2065:24|
 :skolemid |35|
 :pattern ( (|$IsValid'num'| v@@5))
)))
(assert (forall ((t@@15 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamI8 t@@15) (|$IsEqual'vec'u8''| ($TypeName t@@15) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 105) 1 56) 2)))
 :qid |outputbpl.4352:15|
 :skolemid |151|
 :pattern ( ($TypeName t@@15))
)))
(assert (forall ((t@@16 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamU8 t@@16) (|$IsEqual'vec'u8''| ($TypeName t@@16) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 117) 1 56) 2)))
 :qid |outputbpl.4340:15|
 :skolemid |139|
 :pattern ( ($TypeName t@@16))
)))
(assert (forall ((src@@2 (_ BitVec 8)) ) (! (= ($castBv8to64 src@@2) (concat #x00000000000000 src@@2))
 :qid |outputbpl.3112:23|
 :skolemid |80|
 :pattern ( ($castBv8to64 src@@2))
)))
(assert (forall ((src@@3 (_ BitVec 64)) ) (! (= ($castBv64to256 src@@3) (concat #x000000000000000000000000000000000000000000000000 src@@3))
 :qid |outputbpl.3694:25|
 :skolemid |114|
 :pattern ( ($castBv64to256 src@@3))
)))
(assert (forall ((src@@4 (_ BitVec 8)) ) (! (= ($castBv8to256 src@@4) (concat #x00000000000000000000000000000000000000000000000000000000000000 src@@4))
 :qid |outputbpl.3586:24|
 :skolemid |107|
 :pattern ( ($castBv8to256 src@@4))
)))
(assert (forall ((n Int) (e@@0 Int) ) (! (= ($pow n e@@0) (ite  (and (not (= n 0)) (= e@@0 0)) 1 (ite (> e@@0 0) (* n ($pow n (- e@@0 1))) $undefined_int)))
 :qid |outputbpl.1000:15|
 :skolemid |20|
 :pattern ( ($pow n e@@0))
)))
(assert (forall ((t@@17 T@$TypeParamInfo) ) (!  (=> (|$IsPrefix'vec'u8''| ($TypeName t@@17) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2)) (is-$TypeParamVector t@@17))
 :qid |outputbpl.4371:15|
 :skolemid |170|
 :pattern ( ($TypeName t@@17))
)))
(assert (forall ((t@@18 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@18) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 105) 1 56) 2)) (is-$TypeParamI8 t@@18))
 :qid |outputbpl.4353:15|
 :skolemid |152|
 :pattern ( ($TypeName t@@18))
)))
(assert (forall ((t@@19 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@19) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 117) 1 56) 2)) (is-$TypeParamU8 t@@19))
 :qid |outputbpl.4341:15|
 :skolemid |140|
 :pattern ( ($TypeName t@@19))
)))
(assert (forall ((s |T@$bc_BasicCoin_Balance'#0'|) ) (! (= (|$IsValid'$bc_BasicCoin_Balance'#0''| s) (|$IsValid'$bc_BasicCoin_Coin'#0''| (|$coin#$bc_BasicCoin_Balance'#0'| s)))
 :qid |outputbpl.4565:46|
 :skolemid |171|
 :pattern ( (|$IsValid'$bc_BasicCoin_Balance'#0''| s))
)))
(assert (forall ((s@@0 |T@$bc_BasicCoin_Coin'#0'|) ) (! (= (|$IsValid'$bc_BasicCoin_Coin'#0''| s@@0) (|$IsValid'u64'| (|$value#$bc_BasicCoin_Coin'#0'| s@@0)))
 :qid |outputbpl.4580:43|
 :skolemid |172|
 :pattern ( (|$IsValid'$bc_BasicCoin_Coin'#0''| s@@0))
)))
(assert (forall ((src1@@37 (_ BitVec 16)) (src2@@29 (_ BitVec 8)) ) (! (= ($shlBv16From8 src1@@37 src2@@29) (bvshl src1@@37 (concat #x00 src2@@29)))
 :qid |outputbpl.2641:24|
 :skolemid |56|
 :pattern ( ($shlBv16From8 src1@@37 src2@@29))
)))
(assert (forall ((src1@@38 (_ BitVec 16)) (src2@@30 (_ BitVec 8)) ) (! (= ($shrBv16From8 src1@@38 src2@@30) (bvlshr src1@@38 (concat #x00 src2@@30)))
 :qid |outputbpl.2656:24|
 :skolemid |57|
 :pattern ( ($shrBv16From8 src1@@38 src2@@30))
)))
(assert (forall ((src1@@39 (_ BitVec 32)) (src2@@31 (_ BitVec 16)) ) (! (= ($shlBv32From16 src1@@39 src2@@31) (bvshl src1@@39 (concat #x0000 src2@@31)))
 :qid |outputbpl.2916:25|
 :skolemid |70|
 :pattern ( ($shlBv32From16 src1@@39 src2@@31))
)))
(assert (forall ((src1@@40 (_ BitVec 32)) (src2@@32 (_ BitVec 16)) ) (! (= ($shrBv32From16 src1@@40 src2@@32) (bvlshr src1@@40 (concat #x0000 src2@@32)))
 :qid |outputbpl.2931:25|
 :skolemid |71|
 :pattern ( ($shrBv32From16 src1@@40 src2@@32))
)))
(assert (forall ((src1@@41 (_ BitVec 32)) (src2@@33 (_ BitVec 8)) ) (! (= ($shlBv32From8 src1@@41 src2@@33) (bvshl src1@@41 (concat #x000000 src2@@33)))
 :qid |outputbpl.2879:24|
 :skolemid |68|
 :pattern ( ($shlBv32From8 src1@@41 src2@@33))
)))
(assert (forall ((src1@@42 (_ BitVec 32)) (src2@@34 (_ BitVec 8)) ) (! (= ($shrBv32From8 src1@@42 src2@@34) (bvlshr src1@@42 (concat #x000000 src2@@34)))
 :qid |outputbpl.2894:24|
 :skolemid |69|
 :pattern ( ($shrBv32From8 src1@@42 src2@@34))
)))
(assert (forall ((src1@@43 (_ BitVec 64)) (src2@@35 (_ BitVec 32)) ) (! (= ($shlBv64From32 src1@@43 src2@@35) (bvshl src1@@43 (concat #x00000000 src2@@35)))
 :qid |outputbpl.3192:25|
 :skolemid |85|
 :pattern ( ($shlBv64From32 src1@@43 src2@@35))
)))
(assert (forall ((src1@@44 (_ BitVec 64)) (src2@@36 (_ BitVec 32)) ) (! (= ($shrBv64From32 src1@@44 src2@@36) (bvlshr src1@@44 (concat #x00000000 src2@@36)))
 :qid |outputbpl.3207:25|
 :skolemid |86|
 :pattern ( ($shrBv64From32 src1@@44 src2@@36))
)))
(assert (forall ((src1@@45 (_ BitVec 64)) (src2@@37 (_ BitVec 16)) ) (! (= ($shlBv64From16 src1@@45 src2@@37) (bvshl src1@@45 (concat #x000000000000 src2@@37)))
 :qid |outputbpl.3155:25|
 :skolemid |83|
 :pattern ( ($shlBv64From16 src1@@45 src2@@37))
)))
(assert (forall ((src1@@46 (_ BitVec 64)) (src2@@38 (_ BitVec 16)) ) (! (= ($shrBv64From16 src1@@46 src2@@38) (bvlshr src1@@46 (concat #x000000000000 src2@@38)))
 :qid |outputbpl.3170:25|
 :skolemid |84|
 :pattern ( ($shrBv64From16 src1@@46 src2@@38))
)))
(assert (forall ((src1@@47 (_ BitVec 64)) (src2@@39 (_ BitVec 8)) ) (! (= ($shlBv64From8 src1@@47 src2@@39) (bvshl src1@@47 (concat #x00000000000000 src2@@39)))
 :qid |outputbpl.3118:24|
 :skolemid |81|
 :pattern ( ($shlBv64From8 src1@@47 src2@@39))
)))
(assert (forall ((src1@@48 (_ BitVec 64)) (src2@@40 (_ BitVec 8)) ) (! (= ($shrBv64From8 src1@@48 src2@@40) (bvlshr src1@@48 (concat #x00000000000000 src2@@40)))
 :qid |outputbpl.3133:24|
 :skolemid |82|
 :pattern ( ($shrBv64From8 src1@@48 src2@@40))
)))
(assert (forall ((src1@@49 (_ BitVec 128)) (src2@@41 (_ BitVec 64)) ) (! (= ($shlBv128From64 src1@@49 src2@@41) (bvshl src1@@49 (concat #x0000000000000000 src2@@41)))
 :qid |outputbpl.3472:26|
 :skolemid |101|
 :pattern ( ($shlBv128From64 src1@@49 src2@@41))
)))
(assert (forall ((src1@@50 (_ BitVec 128)) (src2@@42 (_ BitVec 64)) ) (! (= ($shrBv128From64 src1@@50 src2@@42) (bvlshr src1@@50 (concat #x0000000000000000 src2@@42)))
 :qid |outputbpl.3487:26|
 :skolemid |102|
 :pattern ( ($shrBv128From64 src1@@50 src2@@42))
)))
(assert (forall ((src1@@51 (_ BitVec 128)) (src2@@43 (_ BitVec 32)) ) (! (= ($shlBv128From32 src1@@51 src2@@43) (bvshl src1@@51 (concat #x000000000000000000000000 src2@@43)))
 :qid |outputbpl.3435:26|
 :skolemid |99|
 :pattern ( ($shlBv128From32 src1@@51 src2@@43))
)))
(assert (forall ((src1@@52 (_ BitVec 128)) (src2@@44 (_ BitVec 32)) ) (! (= ($shrBv128From32 src1@@52 src2@@44) (bvlshr src1@@52 (concat #x000000000000000000000000 src2@@44)))
 :qid |outputbpl.3450:26|
 :skolemid |100|
 :pattern ( ($shrBv128From32 src1@@52 src2@@44))
)))
(assert (forall ((src1@@53 (_ BitVec 128)) (src2@@45 (_ BitVec 16)) ) (! (= ($shlBv128From16 src1@@53 src2@@45) (bvshl src1@@53 (concat #x0000000000000000000000000000 src2@@45)))
 :qid |outputbpl.3398:26|
 :skolemid |97|
 :pattern ( ($shlBv128From16 src1@@53 src2@@45))
)))
(assert (forall ((src1@@54 (_ BitVec 128)) (src2@@46 (_ BitVec 16)) ) (! (= ($shrBv128From16 src1@@54 src2@@46) (bvlshr src1@@54 (concat #x0000000000000000000000000000 src2@@46)))
 :qid |outputbpl.3413:26|
 :skolemid |98|
 :pattern ( ($shrBv128From16 src1@@54 src2@@46))
)))
(assert (forall ((src1@@55 (_ BitVec 128)) (src2@@47 (_ BitVec 8)) ) (! (= ($shlBv128From8 src1@@55 src2@@47) (bvshl src1@@55 (concat #x000000000000000000000000000000 src2@@47)))
 :qid |outputbpl.3361:25|
 :skolemid |95|
 :pattern ( ($shlBv128From8 src1@@55 src2@@47))
)))
(assert (forall ((src1@@56 (_ BitVec 128)) (src2@@48 (_ BitVec 8)) ) (! (= ($shrBv128From8 src1@@56 src2@@48) (bvlshr src1@@56 (concat #x000000000000000000000000000000 src2@@48)))
 :qid |outputbpl.3376:25|
 :skolemid |96|
 :pattern ( ($shrBv128From8 src1@@56 src2@@48))
)))
(assert (forall ((src1@@57 (_ BitVec 256)) (src2@@49 (_ BitVec 128)) ) (! (= ($shlBv256From128 src1@@57 src2@@49) (bvshl src1@@57 (concat #x00000000000000000000000000000000 src2@@49)))
 :qid |outputbpl.3737:27|
 :skolemid |117|
 :pattern ( ($shlBv256From128 src1@@57 src2@@49))
)))
(assert (forall ((src1@@58 (_ BitVec 256)) (src2@@50 (_ BitVec 128)) ) (! (= ($shrBv256From128 src1@@58 src2@@50) (bvlshr src1@@58 (concat #x00000000000000000000000000000000 src2@@50)))
 :qid |outputbpl.3752:27|
 :skolemid |118|
 :pattern ( ($shrBv256From128 src1@@58 src2@@50))
)))
(assert (forall ((src1@@59 (_ BitVec 256)) (src2@@51 (_ BitVec 64)) ) (! (= ($shlBv256From64 src1@@59 src2@@51) (bvshl src1@@59 (concat #x000000000000000000000000000000000000000000000000 src2@@51)))
 :qid |outputbpl.3700:26|
 :skolemid |115|
 :pattern ( ($shlBv256From64 src1@@59 src2@@51))
)))
(assert (forall ((src1@@60 (_ BitVec 256)) (src2@@52 (_ BitVec 64)) ) (! (= ($shrBv256From64 src1@@60 src2@@52) (bvlshr src1@@60 (concat #x000000000000000000000000000000000000000000000000 src2@@52)))
 :qid |outputbpl.3715:26|
 :skolemid |116|
 :pattern ( ($shrBv256From64 src1@@60 src2@@52))
)))
(assert (forall ((src1@@61 (_ BitVec 256)) (src2@@53 (_ BitVec 32)) ) (! (= ($shlBv256From32 src1@@61 src2@@53) (bvshl src1@@61 (concat #x00000000000000000000000000000000000000000000000000000000 src2@@53)))
 :qid |outputbpl.3658:26|
 :skolemid |112|
 :pattern ( ($shlBv256From32 src1@@61 src2@@53))
)))
(assert (forall ((src1@@62 (_ BitVec 256)) (src2@@54 (_ BitVec 32)) ) (! (= ($shrBv256From32 src1@@62 src2@@54) (bvlshr src1@@62 (concat #x00000000000000000000000000000000000000000000000000000000 src2@@54)))
 :qid |outputbpl.3673:26|
 :skolemid |113|
 :pattern ( ($shrBv256From32 src1@@62 src2@@54))
)))
(assert (forall ((src1@@63 (_ BitVec 256)) (src2@@55 (_ BitVec 16)) ) (! (= ($shlBv256From16 src1@@63 src2@@55) (bvshl src1@@63 (concat #x000000000000000000000000000000000000000000000000000000000000 src2@@55)))
 :qid |outputbpl.3621:26|
 :skolemid |110|
 :pattern ( ($shlBv256From16 src1@@63 src2@@55))
)))
(assert (forall ((src1@@64 (_ BitVec 256)) (src2@@56 (_ BitVec 16)) ) (! (= ($shrBv256From16 src1@@64 src2@@56) (bvlshr src1@@64 (concat #x000000000000000000000000000000000000000000000000000000000000 src2@@56)))
 :qid |outputbpl.3636:26|
 :skolemid |111|
 :pattern ( ($shrBv256From16 src1@@64 src2@@56))
)))
(assert (forall ((src1@@65 (_ BitVec 256)) (src2@@57 (_ BitVec 8)) ) (! (= ($shlBv256From8 src1@@65 src2@@57) (bvshl src1@@65 (concat #x00000000000000000000000000000000000000000000000000000000000000 src2@@57)))
 :qid |outputbpl.3592:25|
 :skolemid |108|
 :pattern ( ($shlBv256From8 src1@@65 src2@@57))
)))
(assert (forall ((src1@@66 (_ BitVec 256)) (src2@@58 (_ BitVec 8)) ) (! (= ($shrBv256From8 src1@@66 src2@@58) (bvlshr src1@@66 (concat #x00000000000000000000000000000000000000000000000000000000000000 src2@@58)))
 :qid |outputbpl.3603:25|
 :skolemid |109|
 :pattern ( ($shrBv256From8 src1@@66 src2@@58))
)))
(assert (forall ((t@@20 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamU16 t@@20) (|$IsEqual'vec'u8''| ($TypeName t@@20) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 117) 1 49) 2 54) 3)))
 :qid |outputbpl.4342:15|
 :skolemid |141|
 :pattern ( ($TypeName t@@20))
)))
(assert (forall ((t@@21 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamU32 t@@21) (|$IsEqual'vec'u8''| ($TypeName t@@21) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 117) 1 51) 2 50) 3)))
 :qid |outputbpl.4344:15|
 :skolemid |143|
 :pattern ( ($TypeName t@@21))
)))
(assert (forall ((t@@22 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamU64 t@@22) (|$IsEqual'vec'u8''| ($TypeName t@@22) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 117) 1 54) 2 52) 3)))
 :qid |outputbpl.4346:15|
 :skolemid |145|
 :pattern ( ($TypeName t@@22))
)))
(assert (forall ((s@@1 T@$bc_ProphecyBenchmark3Levels2Fields_Node1) ) (! (= (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node1'| s@@1)  (and (and (and (and (and (and (and (|$IsValid'u64'| (|$v0#$bc_ProphecyBenchmark3Levels2Fields_Node1| s@@1)) (|$IsValid'u64'| (|$v1#$bc_ProphecyBenchmark3Levels2Fields_Node1| s@@1))) (|$IsValid'u64'| (|$v2#$bc_ProphecyBenchmark3Levels2Fields_Node1| s@@1))) (|$IsValid'u64'| (|$v3#$bc_ProphecyBenchmark3Levels2Fields_Node1| s@@1))) (|$IsValid'u64'| (|$v4#$bc_ProphecyBenchmark3Levels2Fields_Node1| s@@1))) (|$IsValid'u64'| (|$v5#$bc_ProphecyBenchmark3Levels2Fields_Node1| s@@1))) (|$IsValid'u64'| (|$v6#$bc_ProphecyBenchmark3Levels2Fields_Node1| s@@1))) (|$IsValid'u64'| (|$v7#$bc_ProphecyBenchmark3Levels2Fields_Node1| s@@1))))
 :qid |outputbpl.6065:62|
 :skolemid |180|
 :pattern ( (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node1'| s@@1))
)))
(assert (forall ((s@@2 T@$bc_ProphecyBenchmark3Levels2Fields_Node2) ) (! (= (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node2'| s@@2)  (and (and (and (and (and (and (and (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node1'| (|$v0#$bc_ProphecyBenchmark3Levels2Fields_Node2| s@@2)) (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node1'| (|$v1#$bc_ProphecyBenchmark3Levels2Fields_Node2| s@@2))) (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node1'| (|$v2#$bc_ProphecyBenchmark3Levels2Fields_Node2| s@@2))) (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node1'| (|$v3#$bc_ProphecyBenchmark3Levels2Fields_Node2| s@@2))) (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node1'| (|$v4#$bc_ProphecyBenchmark3Levels2Fields_Node2| s@@2))) (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node1'| (|$v5#$bc_ProphecyBenchmark3Levels2Fields_Node2| s@@2))) (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node1'| (|$v6#$bc_ProphecyBenchmark3Levels2Fields_Node2| s@@2))) (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node1'| (|$v7#$bc_ProphecyBenchmark3Levels2Fields_Node2| s@@2))))
 :qid |outputbpl.6107:62|
 :skolemid |181|
 :pattern ( (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node2'| s@@2))
)))
(assert (forall ((s@@3 T@$bc_ProphecyBenchmark3Levels2Fields_Node3) ) (! (= (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node3'| s@@3)  (and (and (and (and (and (and (and (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node2'| (|$v0#$bc_ProphecyBenchmark3Levels2Fields_Node3| s@@3)) (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node2'| (|$v1#$bc_ProphecyBenchmark3Levels2Fields_Node3| s@@3))) (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node2'| (|$v2#$bc_ProphecyBenchmark3Levels2Fields_Node3| s@@3))) (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node2'| (|$v3#$bc_ProphecyBenchmark3Levels2Fields_Node3| s@@3))) (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node2'| (|$v4#$bc_ProphecyBenchmark3Levels2Fields_Node3| s@@3))) (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node2'| (|$v5#$bc_ProphecyBenchmark3Levels2Fields_Node3| s@@3))) (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node2'| (|$v6#$bc_ProphecyBenchmark3Levels2Fields_Node3| s@@3))) (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node2'| (|$v7#$bc_ProphecyBenchmark3Levels2Fields_Node3| s@@3))))
 :qid |outputbpl.6149:62|
 :skolemid |182|
 :pattern ( (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node3'| s@@3))
)))
(assert (forall ((src@@5 (_ BitVec 8)) ) (! (= ($castBv8to8 src@@5) src@@5)
 :qid |outputbpl.2377:22|
 :skolemid |41|
 :pattern ( ($castBv8to8 src@@5))
)))
(assert (forall ((src@@6 (_ BitVec 64)) ) (! (= ($castBv64to64 src@@6) src@@6)
 :qid |outputbpl.3228:24|
 :skolemid |87|
 :pattern ( ($castBv64to64 src@@6))
)))
(assert (forall ((src@@7 (_ BitVec 256)) ) (! (= ($castBv256to256 src@@7) src@@7)
 :qid |outputbpl.3773:26|
 :skolemid |119|
 :pattern ( ($castBv256to256 src@@7))
)))
(assert (forall ((t@@23 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@23) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 117) 1 49) 2 50) 3 56) 4)) (is-$TypeParamU128 t@@23))
 :qid |outputbpl.4349:15|
 :skolemid |148|
 :pattern ( ($TypeName t@@23))
)))
(assert (forall ((src1@@67 (_ BitVec 8)) (src2@@59 (_ BitVec 8)) ) (! (= ($shlBv8From8 src1@@67 src2@@59) (bvshl src1@@67 src2@@59))
 :qid |outputbpl.2383:23|
 :skolemid |42|
 :pattern ( ($shlBv8From8 src1@@67 src2@@59))
)))
(assert (forall ((src1@@68 (_ BitVec 8)) (src2@@60 (_ BitVec 8)) ) (! (= ($shrBv8From8 src1@@68 src2@@60) (bvlshr src1@@68 src2@@60))
 :qid |outputbpl.2398:23|
 :skolemid |43|
 :pattern ( ($shrBv8From8 src1@@68 src2@@60))
)))
(assert (forall ((src1@@69 (_ BitVec 16)) (src2@@61 (_ BitVec 16)) ) (! (= ($shlBv16From16 src1@@69 src2@@61) (bvshl src1@@69 src2@@61))
 :qid |outputbpl.2678:25|
 :skolemid |58|
 :pattern ( ($shlBv16From16 src1@@69 src2@@61))
)))
(assert (forall ((src1@@70 (_ BitVec 16)) (src2@@62 (_ BitVec 16)) ) (! (= ($shrBv16From16 src1@@70 src2@@62) (bvlshr src1@@70 src2@@62))
 :qid |outputbpl.2693:25|
 :skolemid |59|
 :pattern ( ($shrBv16From16 src1@@70 src2@@62))
)))
(assert (forall ((src1@@71 (_ BitVec 32)) (src2@@63 (_ BitVec 32)) ) (! (= ($shlBv32From32 src1@@71 src2@@63) (bvshl src1@@71 src2@@63))
 :qid |outputbpl.2953:25|
 :skolemid |72|
 :pattern ( ($shlBv32From32 src1@@71 src2@@63))
)))
(assert (forall ((src1@@72 (_ BitVec 32)) (src2@@64 (_ BitVec 32)) ) (! (= ($shrBv32From32 src1@@72 src2@@64) (bvlshr src1@@72 src2@@64))
 :qid |outputbpl.2968:25|
 :skolemid |73|
 :pattern ( ($shrBv32From32 src1@@72 src2@@64))
)))
(assert (forall ((src1@@73 (_ BitVec 64)) (src2@@65 (_ BitVec 64)) ) (! (= ($shlBv64From64 src1@@73 src2@@65) (bvshl src1@@73 src2@@65))
 :qid |outputbpl.3234:25|
 :skolemid |88|
 :pattern ( ($shlBv64From64 src1@@73 src2@@65))
)))
(assert (forall ((src1@@74 (_ BitVec 64)) (src2@@66 (_ BitVec 64)) ) (! (= ($shrBv64From64 src1@@74 src2@@66) (bvlshr src1@@74 src2@@66))
 :qid |outputbpl.3249:25|
 :skolemid |89|
 :pattern ( ($shrBv64From64 src1@@74 src2@@66))
)))
(assert (forall ((src1@@75 (_ BitVec 128)) (src2@@67 (_ BitVec 128)) ) (! (= ($shlBv128From128 src1@@75 src2@@67) (bvshl src1@@75 src2@@67))
 :qid |outputbpl.3509:27|
 :skolemid |103|
 :pattern ( ($shlBv128From128 src1@@75 src2@@67))
)))
(assert (forall ((src1@@76 (_ BitVec 128)) (src2@@68 (_ BitVec 128)) ) (! (= ($shrBv128From128 src1@@76 src2@@68) (bvlshr src1@@76 src2@@68))
 :qid |outputbpl.3524:27|
 :skolemid |104|
 :pattern ( ($shrBv128From128 src1@@76 src2@@68))
)))
(assert (forall ((src1@@77 (_ BitVec 256)) (src2@@69 (_ BitVec 256)) ) (! (= ($shlBv256From256 src1@@77 src2@@69) (bvshl src1@@77 src2@@69))
 :qid |outputbpl.3779:27|
 :skolemid |120|
 :pattern ( ($shlBv256From256 src1@@77 src2@@69))
)))
(assert (forall ((src1@@78 (_ BitVec 256)) (src2@@70 (_ BitVec 256)) ) (! (= ($shrBv256From256 src1@@78 src2@@70) (bvlshr src1@@78 src2@@70))
 :qid |outputbpl.3794:27|
 :skolemid |121|
 :pattern ( ($shrBv256From256 src1@@78 src2@@70))
)))
(assert (forall ((k1@@0 T@Vec_11028) (k2@@0 T@Vec_11028) ) (!  (=> (|$IsEqual'vec'u8''| k1@@0 k2@@0) (= ($1_Signature_$ed25519_validate_pubkey k1@@0) ($1_Signature_$ed25519_validate_pubkey k2@@0)))
 :qid |outputbpl.4274:15|
 :skolemid |135|
 :pattern ( ($1_Signature_$ed25519_validate_pubkey k1@@0) ($1_Signature_$ed25519_validate_pubkey k2@@0))
)))
(assert (forall ((v@@6 (_ BitVec 8)) ) (! (= (|$IsValid'bv8'| v@@6)  (and (bvuge v@@6 #x00) (bvule v@@6 #xff)))
 :qid |outputbpl.1407:24|
 :skolemid |29|
 :pattern ( (|$IsValid'bv8'| v@@6))
)))
(assert (forall ((v@@7 (_ BitVec 64)) ) (! (= (|$IsValid'bv64'| v@@7)  (and (bvuge v@@7 #x0000000000000000) (bvule v@@7 #xffffffffffffffff)))
 :qid |outputbpl.1782:25|
 :skolemid |32|
 :pattern ( (|$IsValid'bv64'| v@@7))
)))
(assert (forall ((v@@8 (_ BitVec 16)) ) (! (= (|$IsValid'bv16'| v@@8)  (and (bvuge v@@8 #x0000) (bvule v@@8 #xffff)))
 :qid |outputbpl.1532:25|
 :skolemid |30|
 :pattern ( (|$IsValid'bv16'| v@@8))
)))
(assert (forall ((v@@9 (_ BitVec 256)) ) (! (= (|$IsValid'bv256'| v@@9)  (and (bvuge v@@9 #x0000000000000000000000000000000000000000000000000000000000000000) (bvule v@@9 #xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)))
 :qid |outputbpl.2032:26|
 :skolemid |34|
 :pattern ( (|$IsValid'bv256'| v@@9))
)))
(assert (forall ((v@@10 T@Vec_11028) (e@@1 Int) ) (! (let ((i@@8 (|$IndexOfVec'u8'| v@@10 e@@1)))
(ite  (not (exists ((i@@9 Int) ) (!  (and (and (|$IsValid'u64'| i@@9) (InRangeVec_19490 v@@10 i@@9)) (= (|Select__T@[Int]Int_| (|v#Vec_11028| v@@10) i@@9) e@@1))
 :qid |outputbpl.3848:13|
 :skolemid |130|
))) (= i@@8 (- 0 1))  (and (and (and (|$IsValid'u64'| i@@8) (InRangeVec_19490 v@@10 i@@8)) (= (|Select__T@[Int]Int_| (|v#Vec_11028| v@@10) i@@8) e@@1)) (forall ((j@@1 Int) ) (!  (=> (and (and (|$IsValid'u64'| j@@1) (>= j@@1 0)) (< j@@1 i@@8)) (not (= (|Select__T@[Int]Int_| (|v#Vec_11028| v@@10) j@@1) e@@1)))
 :qid |outputbpl.3856:17|
 :skolemid |131|
)))))
 :qid |outputbpl.3852:15|
 :skolemid |132|
 :pattern ( (|$IndexOfVec'u8'| v@@10 e@@1))
)))
(assert (forall ((t@@24 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@24) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 105) 1 49) 2 50) 3 56) 4)) (is-$TypeParamI128 t@@24))
 :qid |outputbpl.4361:15|
 :skolemid |160|
 :pattern ( ($TypeName t@@24))
)))
(assert (forall ((t@@25 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamBool t@@25) (|$IsEqual'vec'u8''| ($TypeName t@@25) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 98) 1 111) 2 111) 3 108) 4)))
 :qid |outputbpl.4338:15|
 :skolemid |137|
 :pattern ( ($TypeName t@@25))
)))
(assert (forall ((v@@11 (_ BitVec 128)) ) (! (= (|$IsValid'bv128'| v@@11)  (and (bvuge v@@11 #x00000000000000000000000000000000) (bvule v@@11 #xffffffffffffffffffffffffffffffff)))
 :qid |outputbpl.1907:26|
 :skolemid |33|
 :pattern ( (|$IsValid'bv128'| v@@11))
)))
(assert (forall ((v1@@0 T@Vec_11028) (v2@@0 T@Vec_11028) ) (! (= (|$IsEqual'vec'u8''| v1@@0 v2@@0) (|$IsEqual'vec'u8''| ($1_hash_sha2 v1@@0) ($1_hash_sha2 v2@@0)))
 :qid |outputbpl.4149:15|
 :skolemid |133|
 :pattern ( ($1_hash_sha2 v1@@0) ($1_hash_sha2 v2@@0))
)))
(assert (forall ((v1@@1 T@Vec_11028) (v2@@1 T@Vec_11028) ) (! (= (|$IsEqual'vec'u8''| v1@@1 v2@@1) (|$IsEqual'vec'u8''| ($1_hash_sha3 v1@@1) ($1_hash_sha3 v2@@1)))
 :qid |outputbpl.4165:15|
 :skolemid |134|
 :pattern ( ($1_hash_sha3 v1@@1) ($1_hash_sha3 v2@@1))
)))
(assert (forall ((t@@26 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamStruct t@@26) (|$IsEqual'vec'u8''| ($TypeName t@@26) (let ((m2@@2 (|v#Vec_11028| (|s#$TypeParamStruct| t@@26))))
(let ((l2@@1 (|l#Vec_11028| (|s#$TypeParamStruct| t@@26))))
(let ((m1@@2 (|v#Vec_11028| (let ((m2@@3 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((l2@@2 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((m1@@3 (|v#Vec_11028| (let ((m2@@4 (|v#Vec_11028| (|m#$TypeParamStruct| t@@26))))
(let ((l2@@3 (|l#Vec_11028| (|m#$TypeParamStruct| t@@26))))
(let ((m1@@4 (|v#Vec_11028| (let ((m2@@5 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((l2@@4 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((m1@@5 (|v#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(let ((l1@@2 (|l#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@2 l2@@4) l1@@2 m1@@5 m2@@5 l1@@2 DefaultVecElem_19835) (+ l1@@2 l2@@4)))))))))
(let ((l1@@3 (|l#Vec_11028| (let ((m2@@5 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((l2@@4 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((m1@@5 (|v#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(let ((l1@@2 (|l#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@2 l2@@4) l1@@2 m1@@5 m2@@5 l1@@2 DefaultVecElem_19835) (+ l1@@2 l2@@4)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@3 l2@@3) l1@@3 m1@@4 m2@@4 l1@@3 DefaultVecElem_19835) (+ l1@@3 l2@@3)))))))))
(let ((l1@@4 (|l#Vec_11028| (let ((m2@@4 (|v#Vec_11028| (|m#$TypeParamStruct| t@@26))))
(let ((l2@@3 (|l#Vec_11028| (|m#$TypeParamStruct| t@@26))))
(let ((m1@@4 (|v#Vec_11028| (let ((m2@@5 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((l2@@4 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((m1@@5 (|v#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(let ((l1@@2 (|l#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@2 l2@@4) l1@@2 m1@@5 m2@@5 l1@@2 DefaultVecElem_19835) (+ l1@@2 l2@@4)))))))))
(let ((l1@@3 (|l#Vec_11028| (let ((m2@@5 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((l2@@4 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((m1@@5 (|v#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(let ((l1@@2 (|l#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@2 l2@@4) l1@@2 m1@@5 m2@@5 l1@@2 DefaultVecElem_19835) (+ l1@@2 l2@@4)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@3 l2@@3) l1@@3 m1@@4 m2@@4 l1@@3 DefaultVecElem_19835) (+ l1@@3 l2@@3)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@4 l2@@2) l1@@4 m1@@3 m2@@3 l1@@4 DefaultVecElem_19835) (+ l1@@4 l2@@2)))))))))
(let ((l1@@5 (|l#Vec_11028| (let ((m2@@3 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((l2@@2 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((m1@@3 (|v#Vec_11028| (let ((m2@@4 (|v#Vec_11028| (|m#$TypeParamStruct| t@@26))))
(let ((l2@@3 (|l#Vec_11028| (|m#$TypeParamStruct| t@@26))))
(let ((m1@@4 (|v#Vec_11028| (let ((m2@@5 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((l2@@4 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((m1@@5 (|v#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(let ((l1@@2 (|l#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@2 l2@@4) l1@@2 m1@@5 m2@@5 l1@@2 DefaultVecElem_19835) (+ l1@@2 l2@@4)))))))))
(let ((l1@@3 (|l#Vec_11028| (let ((m2@@5 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((l2@@4 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((m1@@5 (|v#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(let ((l1@@2 (|l#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@2 l2@@4) l1@@2 m1@@5 m2@@5 l1@@2 DefaultVecElem_19835) (+ l1@@2 l2@@4)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@3 l2@@3) l1@@3 m1@@4 m2@@4 l1@@3 DefaultVecElem_19835) (+ l1@@3 l2@@3)))))))))
(let ((l1@@4 (|l#Vec_11028| (let ((m2@@4 (|v#Vec_11028| (|m#$TypeParamStruct| t@@26))))
(let ((l2@@3 (|l#Vec_11028| (|m#$TypeParamStruct| t@@26))))
(let ((m1@@4 (|v#Vec_11028| (let ((m2@@5 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((l2@@4 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((m1@@5 (|v#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(let ((l1@@2 (|l#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@2 l2@@4) l1@@2 m1@@5 m2@@5 l1@@2 DefaultVecElem_19835) (+ l1@@2 l2@@4)))))))))
(let ((l1@@3 (|l#Vec_11028| (let ((m2@@5 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((l2@@4 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((m1@@5 (|v#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(let ((l1@@2 (|l#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@2 l2@@4) l1@@2 m1@@5 m2@@5 l1@@2 DefaultVecElem_19835) (+ l1@@2 l2@@4)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@3 l2@@3) l1@@3 m1@@4 m2@@4 l1@@3 DefaultVecElem_19835) (+ l1@@3 l2@@3)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@4 l2@@2) l1@@4 m1@@3 m2@@3 l1@@4 DefaultVecElem_19835) (+ l1@@4 l2@@2)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@5 l2@@1) l1@@5 m1@@2 m2@@2 l1@@5 DefaultVecElem_19835) (+ l1@@5 l2@@1))))))))
 :qid |outputbpl.4370:15|
 :skolemid |169|
 :pattern ( ($TypeName t@@26))
)))
(assert (forall ((t@@27 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@27) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 105) 1 49) 2 54) 3)) (is-$TypeParamI16 t@@27))
 :qid |outputbpl.4355:15|
 :skolemid |154|
 :pattern ( ($TypeName t@@27))
)))
(assert (forall ((t@@28 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@28) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 105) 1 51) 2 50) 3)) (is-$TypeParamI32 t@@28))
 :qid |outputbpl.4357:15|
 :skolemid |156|
 :pattern ( ($TypeName t@@28))
)))
(assert (forall ((t@@29 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@29) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 105) 1 54) 2 52) 3)) (is-$TypeParamI64 t@@29))
 :qid |outputbpl.4359:15|
 :skolemid |158|
 :pattern ( ($TypeName t@@29))
)))
(assert (forall ((v@@12 Int) ) (! (= (|$IsValid'u8'| v@@12)  (and (>= v@@12 $MIN_U8) (<= v@@12 $MAX_U8)))
 :qid |outputbpl.315:23|
 :skolemid |8|
 :pattern ( (|$IsValid'u8'| v@@12))
)))
(assert (forall ((v@@13 Int) ) (! (= (|$IsValid'u16'| v@@13)  (and (>= v@@13 $MIN_U16) (<= v@@13 $MAX_U16)))
 :qid |outputbpl.370:24|
 :skolemid |9|
 :pattern ( (|$IsValid'u16'| v@@13))
)))
(assert (forall ((v@@14 Int) ) (! (= (|$IsValid'u32'| v@@14)  (and (>= v@@14 $MIN_U32) (<= v@@14 $MAX_U32)))
 :qid |outputbpl.425:24|
 :skolemid |10|
 :pattern ( (|$IsValid'u32'| v@@14))
)))
(assert (forall ((v@@15 Int) ) (! (= (|$IsValid'u64'| v@@15)  (and (>= v@@15 $MIN_U64) (<= v@@15 $MAX_U64)))
 :qid |outputbpl.480:24|
 :skolemid |11|
 :pattern ( (|$IsValid'u64'| v@@15))
)))
(assert (forall ((v@@16 Int) ) (! (= (|$IsValid'u128'| v@@16)  (and (>= v@@16 $MIN_U128) (<= v@@16 $MAX_U128)))
 :qid |outputbpl.535:25|
 :skolemid |12|
 :pattern ( (|$IsValid'u128'| v@@16))
)))
(assert (forall ((v@@17 Int) ) (! (= (|$IsValid'u256'| v@@17)  (and (>= v@@17 $MIN_U256) (<= v@@17 $MAX_U256)))
 :qid |outputbpl.590:25|
 :skolemid |13|
 :pattern ( (|$IsValid'u256'| v@@17))
)))
(assert (forall ((v@@18 Int) ) (! (= (|$IsValid'i8'| v@@18)  (and (>= v@@18 $MIN_I8) (<= v@@18 $MAX_I8)))
 :qid |outputbpl.645:23|
 :skolemid |14|
 :pattern ( (|$IsValid'i8'| v@@18))
)))
(assert (forall ((v@@19 Int) ) (! (= (|$IsValid'i16'| v@@19)  (and (>= v@@19 $MIN_I16) (<= v@@19 $MAX_I16)))
 :qid |outputbpl.700:24|
 :skolemid |15|
 :pattern ( (|$IsValid'i16'| v@@19))
)))
(assert (forall ((v@@20 Int) ) (! (= (|$IsValid'i32'| v@@20)  (and (>= v@@20 $MIN_I32) (<= v@@20 $MAX_I32)))
 :qid |outputbpl.755:24|
 :skolemid |16|
 :pattern ( (|$IsValid'i32'| v@@20))
)))
(assert (forall ((v@@21 Int) ) (! (= (|$IsValid'i64'| v@@21)  (and (>= v@@21 $MIN_I64) (<= v@@21 $MAX_I64)))
 :qid |outputbpl.810:24|
 :skolemid |17|
 :pattern ( (|$IsValid'i64'| v@@21))
)))
(assert (forall ((v@@22 Int) ) (! (= (|$IsValid'i128'| v@@22)  (and (>= v@@22 $MIN_I128) (<= v@@22 $MAX_I128)))
 :qid |outputbpl.865:25|
 :skolemid |18|
 :pattern ( (|$IsValid'i128'| v@@22))
)))
(assert (forall ((v@@23 Int) ) (! (= (|$IsValid'i256'| v@@23)  (and (>= v@@23 $MIN_I256) (<= v@@23 $MAX_I256)))
 :qid |outputbpl.920:25|
 :skolemid |19|
 :pattern ( (|$IsValid'i256'| v@@23))
)))
(assert (forall ((v@@24 T@Vec_11028) (i@@10 Int) ) (! (= (InRangeVec_19490 v@@24 i@@10)  (and (>= i@@10 0) (< i@@10 (|l#Vec_11028| v@@24))))
 :qid |outputbpl.123:24|
 :skolemid |3|
 :pattern ( (InRangeVec_19490 v@@24 i@@10))
)))
(assert (forall ((t@@30 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@30) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 117) 1 50) 2 53) 3 54) 4)) (is-$TypeParamU256 t@@30))
 :qid |outputbpl.4351:15|
 :skolemid |150|
 :pattern ( ($TypeName t@@30))
)))
(assert (forall ((r T@$Range) (i@@11 Int) ) (! (= ($InRange r i@@11)  (and (<= (|lb#$Range| r) i@@11) (< i@@11 (|ub#$Range| r))))
 :qid |outputbpl.2079:19|
 :skolemid |37|
 :pattern ( ($InRange r i@@11))
)))
(assert (forall ((t@@31 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@31) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 105) 1 50) 2 53) 3 54) 4)) (is-$TypeParamI256 t@@31))
 :qid |outputbpl.4363:15|
 :skolemid |162|
 :pattern ( ($TypeName t@@31))
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
(assert (forall ((t@@32 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@32) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 97) 1 100) 2 100) 3 114) 4 101) 5 115) 6 115) 7)) (is-$TypeParamAddress t@@32))
 :qid |outputbpl.4365:15|
 :skolemid |164|
 :pattern ( ($TypeName t@@32))
)))
(assert (= $MAX_U256 115792089237316195423570985008687907853269984665640564039457584007913129639935))
(assert (= $MAX_I256 57896044618658097711785492504343953926634992332820282019728792003956564819967))
(assert (= $EXEC_FAILURE_CODE (- 0 1)))
(assert (= $MIN_I8 (- 0 128)))
(assert (= $MIN_I64 (- 0 9223372036854775808)))
(assert (= $MIN_I16 (- 0 32768)))
(assert (= $MIN_I256 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)))
(push 1)
(declare-fun ControlFlow (Int Int) Int)
(declare-fun $abort_flag@4 () Bool)
(declare-fun $t8 () Int)
(declare-fun |Select__T@[Int]$bc_BasicCoin_Balance'#0'_| (|T@[Int]$bc_BasicCoin_Balance'#0'| Int) |T@$bc_BasicCoin_Balance'#0'|)
(declare-fun |$bc_BasicCoin_Balance'#0'_$memory@3| () T@$Memory_56677)
(declare-fun _$t0 () Int)
(declare-fun |$bc_BasicCoin_Balance'#0'_$memory| () T@$Memory_56677)
(declare-fun $t3 () Int)
(declare-fun _$t1 () Int)
(declare-fun $abort_code@4 () Int)
(declare-fun |inline$$bc_BasicCoin_deposit'#0'$0$$t8@1| () Int)
(declare-fun |$bc_BasicCoin_Balance'#0'_$memory@2| () T@$Memory_56677)
(declare-fun $abort_flag@3 () Bool)
(declare-fun $abort_code@3 () Int)
(declare-fun |$bc_BasicCoin_Balance'#0'_$memory@1| () T@$Memory_56677)
(declare-fun $abort_flag@2 () Bool)
(declare-fun $abort_code@2 () Int)
(declare-fun $abort_flag@1 () Bool)
(declare-fun $abort_code@1 () Int)
(declare-fun |inline$$bc_BasicCoin_deposit'#0'$0$$t11@1| () T@$Mutation_21031)
(declare-fun call3formal@result@0 () T@$Mutation_21031)
(declare-fun inline$$AddU64$0$dst@2 () Int)
(declare-fun |inline$$bc_BasicCoin_deposit'#0'$0$$t10@1| () T@$Mutation_57370)
(declare-fun |inline$$bc_BasicCoin_deposit'#0'$0$$t9@2| () T@$Mutation_57347)
(declare-fun inline$$AddU64$0$dst@0 () Int)
(declare-fun |inline$$bc_BasicCoin_balance_of'#0'$0$$ret0@1| () Int)
(declare-fun |inline$$bc_BasicCoin_deposit'#0'$0$$t12@1| () Int)
(declare-fun inline$$AddU64$0$dst@1 () Int)
(declare-fun call2formal@v@0 () |T@$bc_BasicCoin_Coin'#0'|)
(declare-fun |inline$$bc_BasicCoin_deposit'#0'$0$$t9@1| () T@$Mutation_57347)
(declare-fun call3formal@result@0@@0 () T@$Mutation_57370)
(declare-fun call2formal@v@0@@0 () Int)
(declare-fun $t4@0 () |T@$bc_BasicCoin_Coin'#0'|)
(declare-fun |inline$$bc_BasicCoin_deposit'#0'$0$$temp_0'u64'@1| () Int)
(declare-fun |inline$$bc_BasicCoin_deposit'#0'$0$$t9@0| () T@$Mutation_57347)
(declare-fun call0formal@l@0 () T@$Location)
(declare-fun call1formal@p@0 () T@Vec_11028)
(declare-fun call2formal@v@0@@1 () |T@$bc_BasicCoin_Balance'#0'|)
(declare-fun call3formal@result@0@@1 () T@$Mutation_57347)
(declare-fun |$bc_BasicCoin_Balance'#0'_$memory@0| () T@$Memory_56677)
(declare-fun |Store__T@[Int]Bool_| (|T@[Int]Bool| Int Bool) |T@[Int]Bool|)
(assert (forall ( ( ?x0 |T@[Int]Bool|) ( ?x1 Int) ( ?x2 Bool)) (! (= (|Select__T@[Int]Bool_| (|Store__T@[Int]Bool_| ?x0 ?x1 ?x2) ?x1)  ?x2) :weight 0)))
(assert (forall ( ( ?x0 |T@[Int]Bool|) ( ?x1 Int) ( ?y1 Int) ( ?x2 Bool)) (! (=>  (not (= ?x1 ?y1)) (= (|Select__T@[Int]Bool_| (|Store__T@[Int]Bool_| ?x0 ?x1 ?x2) ?y1) (|Select__T@[Int]Bool_| ?x0 ?y1))) :weight 0)))
(declare-fun |Store__T@[Int]$bc_BasicCoin_Balance'#0'_| (|T@[Int]$bc_BasicCoin_Balance'#0'| Int |T@$bc_BasicCoin_Balance'#0'|) |T@[Int]$bc_BasicCoin_Balance'#0'|)
(assert (forall ( ( ?x0 |T@[Int]$bc_BasicCoin_Balance'#0'|) ( ?x1 Int) ( ?x2 |T@$bc_BasicCoin_Balance'#0'|)) (! (= (|Select__T@[Int]$bc_BasicCoin_Balance'#0'_| (|Store__T@[Int]$bc_BasicCoin_Balance'#0'_| ?x0 ?x1 ?x2) ?x1)  ?x2) :weight 0)))
(assert (forall ( ( ?x0 |T@[Int]$bc_BasicCoin_Balance'#0'|) ( ?x1 Int) ( ?y1 Int) ( ?x2 |T@$bc_BasicCoin_Balance'#0'|)) (! (=>  (not (= ?x1 ?y1)) (= (|Select__T@[Int]$bc_BasicCoin_Balance'#0'_| (|Store__T@[Int]$bc_BasicCoin_Balance'#0'_| ?x0 ?x1 ?x2) ?y1) (|Select__T@[Int]$bc_BasicCoin_Balance'#0'_| ?x0 ?y1))) :weight 0)))
(declare-fun $abort_flag@0 () Bool)
(declare-fun |inline$$bc_BasicCoin_balance_of'#0'$0$$t3@1| () |T@$bc_BasicCoin_Coin'#0'|)
(declare-fun |inline$$bc_BasicCoin_balance_of'#0'$0$$t1@2| () |T@$bc_BasicCoin_Balance'#0'|)
(declare-fun |inline$$bc_BasicCoin_balance_of'#0'$0$$t4@1| () Int)
(declare-fun |inline$$bc_BasicCoin_balance_of'#0'$0$$ret0@0| () Int)
(declare-fun |inline$$bc_BasicCoin_balance_of'#0'$0$$t1@0| () |T@$bc_BasicCoin_Balance'#0'|)
(declare-fun |inline$$bc_BasicCoin_balance_of'#0'$0$$t1@1| () |T@$bc_BasicCoin_Balance'#0'|)
(declare-fun $abort_code@0 () Int)
(declare-fun |inline$$bc_BasicCoin_deposit'#0'$0$$t5@0| () Int)
(declare-fun |inline$$bc_BasicCoin_deposit'#0'$0$$t6@0| () Int)
(declare-fun _$t2 () |T@#0|)
(declare-fun $t5 () Int)
(declare-fun $t6 () Int)
(declare-fun $cur_index_initialized () Bool)
(declare-fun $cur_index@0 () Int)
(declare-fun $cur_index () Int)
(set-info :boogie-vc-id $bc_BasicCoin_mint$verify)
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
 (=> (= (ControlFlow 0 0) 30) (let ((anon4_Else_correct  (=> (and (not $abort_flag@4) (= $t8 (|$value#$bc_BasicCoin_Coin'#0'| (|$coin#$bc_BasicCoin_Balance'#0'| (|Select__T@[Int]$bc_BasicCoin_Balance'#0'_| (|contents#$Memory_56677| |$bc_BasicCoin_Balance'#0'_$memory@3|) _$t0))))) (and (=> (= (ControlFlow 0 4) (- 0 6)) (not (not (|Select__T@[Int]Bool_| (|domain#$Memory_56677| |$bc_BasicCoin_Balance'#0'_$memory|) _$t0)))) (=> (not (not (|Select__T@[Int]Bool_| (|domain#$Memory_56677| |$bc_BasicCoin_Balance'#0'_$memory|) _$t0))) (and (=> (= (ControlFlow 0 4) (- 0 5)) (not (> (+ $t3 _$t1) 18446744073709551615))) (=> (not (> (+ $t3 _$t1) 18446744073709551615)) (=> (= (ControlFlow 0 4) (- 0 3)) (= $t8 (+ $t3 _$t1))))))))))
(let ((anon4_Then_correct  (=> $abort_flag@4 (=> (and (= $abort_code@4 $abort_code@4) (= (ControlFlow 0 2) (- 0 1))) (or (not (|Select__T@[Int]Bool_| (|domain#$Memory_56677| |$bc_BasicCoin_Balance'#0'_$memory|) _$t0)) (> (+ $t3 _$t1) 18446744073709551615))))))
(let ((|inline$$bc_BasicCoin_deposit'#0'$0$L2_correct|  (=> (= $abort_flag@4 true) (=> (and (= $abort_code@4 |inline$$bc_BasicCoin_deposit'#0'$0$$t8@1|) (= |$bc_BasicCoin_Balance'#0'_$memory@3| |$bc_BasicCoin_Balance'#0'_$memory@2|)) (and (=> (= (ControlFlow 0 8) 2) anon4_Then_correct) (=> (= (ControlFlow 0 8) 4) anon4_Else_correct))))))
(let ((|inline$$bc_BasicCoin_deposit'#0'$0$anon13_Then_correct|  (=> $abort_flag@3 (=> (and (and (= $abort_code@3 $abort_code@3) (= |inline$$bc_BasicCoin_deposit'#0'$0$$t8@1| $abort_code@3)) (and (= |$bc_BasicCoin_Balance'#0'_$memory@2| |$bc_BasicCoin_Balance'#0'_$memory@1|) (= (ControlFlow 0 11) 8))) |inline$$bc_BasicCoin_deposit'#0'$0$L2_correct|))))
(let ((|inline$$bc_BasicCoin_deposit'#0'$0$anon12_Then_correct|  (=> $abort_flag@2 (=> (and (and (= $abort_code@2 $abort_code@2) (= |inline$$bc_BasicCoin_deposit'#0'$0$$t8@1| $abort_code@2)) (and (= |$bc_BasicCoin_Balance'#0'_$memory@2| |$bc_BasicCoin_Balance'#0'_$memory@1|) (= (ControlFlow 0 10) 8))) |inline$$bc_BasicCoin_deposit'#0'$0$L2_correct|))))
(let ((|inline$$bc_BasicCoin_deposit'#0'$0$anon10_Then_correct|  (=> $abort_flag@1 (=> (and (and (= $abort_code@1 $abort_code@1) (= |inline$$bc_BasicCoin_deposit'#0'$0$$t8@1| $abort_code@1)) (and (= |$bc_BasicCoin_Balance'#0'_$memory@2| |$bc_BasicCoin_Balance'#0'_$memory|) (= (ControlFlow 0 9) 8))) |inline$$bc_BasicCoin_deposit'#0'$0$L2_correct|))))
(let ((|inline$$bc_BasicCoin_deposit'#0'$0$anon13_Else_correct|  (=> (and (and (and (not $abort_flag@3) (= |inline$$bc_BasicCoin_deposit'#0'$0$$t11@1| ($Mutation_21031 (|l#$Mutation_21031| call3formal@result@0) (|p#$Mutation_21031| call3formal@result@0) inline$$AddU64$0$dst@2 (|v_final#$Mutation_21031| call3formal@result@0)))) (and (= (|v#$Mutation_21031| |inline$$bc_BasicCoin_deposit'#0'$0$$t11@1|) (|v_final#$Mutation_21031| |inline$$bc_BasicCoin_deposit'#0'$0$$t11@1|)) (= (|v#$Mutation_57370| |inline$$bc_BasicCoin_deposit'#0'$0$$t10@1|) (|v_final#$Mutation_57370| |inline$$bc_BasicCoin_deposit'#0'$0$$t10@1|)))) (and (and (= (|v#$Mutation_57347| |inline$$bc_BasicCoin_deposit'#0'$0$$t9@2|) (|v_final#$Mutation_57347| |inline$$bc_BasicCoin_deposit'#0'$0$$t9@2|)) (= $abort_flag@4 $abort_flag@3)) (and (= $abort_code@4 $abort_code@3) (= |$bc_BasicCoin_Balance'#0'_$memory@3| |$bc_BasicCoin_Balance'#0'_$memory@1|)))) (and (=> (= (ControlFlow 0 7) 2) anon4_Then_correct) (=> (= (ControlFlow 0 7) 4) anon4_Else_correct)))))
(let ((inline$$AddU64$0$anon3_Then$1_correct  (=> (= $abort_code@3 $EXEC_FAILURE_CODE) (=> (and (= $abort_flag@3 true) (= inline$$AddU64$0$dst@2 inline$$AddU64$0$dst@0)) (and (=> (= (ControlFlow 0 13) 11) |inline$$bc_BasicCoin_deposit'#0'$0$anon13_Then_correct|) (=> (= (ControlFlow 0 13) 7) |inline$$bc_BasicCoin_deposit'#0'$0$anon13_Else_correct|))))))
(let ((inline$$AddU64$0$anon3_Then_correct  (=> (and (or (> (+ |inline$$bc_BasicCoin_balance_of'#0'$0$$ret0@1| |inline$$bc_BasicCoin_deposit'#0'$0$$t12@1|) $MAX_U64) (< (+ |inline$$bc_BasicCoin_balance_of'#0'$0$$ret0@1| |inline$$bc_BasicCoin_deposit'#0'$0$$t12@1|) $MIN_U64)) (= (ControlFlow 0 14) 13)) inline$$AddU64$0$anon3_Then$1_correct)))
(let ((inline$$AddU64$0$anon3_Else_correct  (=> (not (or (> (+ |inline$$bc_BasicCoin_balance_of'#0'$0$$ret0@1| |inline$$bc_BasicCoin_deposit'#0'$0$$t12@1|) $MAX_U64) (< (+ |inline$$bc_BasicCoin_balance_of'#0'$0$$ret0@1| |inline$$bc_BasicCoin_deposit'#0'$0$$t12@1|) $MIN_U64))) (=> (and (and (= inline$$AddU64$0$dst@1 (+ |inline$$bc_BasicCoin_balance_of'#0'$0$$ret0@1| |inline$$bc_BasicCoin_deposit'#0'$0$$t12@1|)) (= $abort_code@3 $abort_code@2)) (and (= $abort_flag@3 $abort_flag@2) (= inline$$AddU64$0$dst@2 inline$$AddU64$0$dst@1))) (and (=> (= (ControlFlow 0 12) 11) |inline$$bc_BasicCoin_deposit'#0'$0$anon13_Then_correct|) (=> (= (ControlFlow 0 12) 7) |inline$$bc_BasicCoin_deposit'#0'$0$anon13_Else_correct|))))))
(let ((|inline$$bc_BasicCoin_deposit'#0'$0$anon12_Else_correct|  (=> (not $abort_flag@2) (=> (and (and (= call2formal@v@0 (|$coin#$bc_BasicCoin_Balance'#0'| (|v#$Mutation_57347| |inline$$bc_BasicCoin_deposit'#0'$0$$t9@1|))) (= (|v#$Mutation_57370| call3formal@result@0@@0) (|$coin#$bc_BasicCoin_Balance'#0'| (|v#$Mutation_57347| |inline$$bc_BasicCoin_deposit'#0'$0$$t9@1|)))) (and (= |inline$$bc_BasicCoin_deposit'#0'$0$$t9@2| ($Mutation_57347 (|l#$Mutation_57347| |inline$$bc_BasicCoin_deposit'#0'$0$$t9@1|) (|p#$Mutation_57347| |inline$$bc_BasicCoin_deposit'#0'$0$$t9@1|) (|$bc_BasicCoin_Balance'#0'| (|v_final#$Mutation_57370| call3formal@result@0@@0)) (|v_final#$Mutation_57347| |inline$$bc_BasicCoin_deposit'#0'$0$$t9@1|))) (= (|v#$Mutation_57347| |inline$$bc_BasicCoin_deposit'#0'$0$$t9@2|) (|v_final#$Mutation_57347| |inline$$bc_BasicCoin_deposit'#0'$0$$t9@2|)))) (=> (and (and (and (= call2formal@v@0@@0 (|$value#$bc_BasicCoin_Coin'#0'| (|v#$Mutation_57370| call3formal@result@0@@0))) (= (|v#$Mutation_21031| call3formal@result@0) (|$value#$bc_BasicCoin_Coin'#0'| (|v#$Mutation_57370| call3formal@result@0@@0)))) (and (= |inline$$bc_BasicCoin_deposit'#0'$0$$t10@1| ($Mutation_57370 (|l#$Mutation_57370| call3formal@result@0@@0) (|p#$Mutation_57370| call3formal@result@0@@0) (|$bc_BasicCoin_Coin'#0'| (|v_final#$Mutation_21031| call3formal@result@0)) (|v_final#$Mutation_57370| call3formal@result@0@@0))) (= (|v#$Mutation_57370| |inline$$bc_BasicCoin_deposit'#0'$0$$t10@1|) (|v_final#$Mutation_57370| |inline$$bc_BasicCoin_deposit'#0'$0$$t10@1|)))) (and (and (= |inline$$bc_BasicCoin_deposit'#0'$0$$t12@1| (|$value#$bc_BasicCoin_Coin'#0'| $t4@0)) (= |inline$$bc_BasicCoin_deposit'#0'$0$$t12@1| |inline$$bc_BasicCoin_deposit'#0'$0$$t12@1|)) (and (= |inline$$bc_BasicCoin_deposit'#0'$0$$temp_0'u64'@1| (|v#$Mutation_21031| call3formal@result@0)) (= |inline$$bc_BasicCoin_deposit'#0'$0$$temp_0'u64'@1| |inline$$bc_BasicCoin_deposit'#0'$0$$temp_0'u64'@1|)))) (and (=> (= (ControlFlow 0 15) 14) inline$$AddU64$0$anon3_Then_correct) (=> (= (ControlFlow 0 15) 12) inline$$AddU64$0$anon3_Else_correct)))))))
(let ((|inline$$bc_BasicCoin_deposit'#0'$0$anon11_Then$1_correct|  (=> (and (and (= |$bc_BasicCoin_Balance'#0'_$memory@1| |$bc_BasicCoin_Balance'#0'_$memory|) (= $abort_code@2 $EXEC_FAILURE_CODE)) (and (= |inline$$bc_BasicCoin_deposit'#0'$0$$t9@1| |inline$$bc_BasicCoin_deposit'#0'$0$$t9@0|) (= $abort_flag@2 true))) (and (=> (= (ControlFlow 0 17) 10) |inline$$bc_BasicCoin_deposit'#0'$0$anon12_Then_correct|) (=> (= (ControlFlow 0 17) 15) |inline$$bc_BasicCoin_deposit'#0'$0$anon12_Else_correct|)))))
(let ((|inline$$bc_BasicCoin_deposit'#0'$0$anon11_Then_correct|  (=> (and (not (|Select__T@[Int]Bool_| (|domain#$Memory_56677| |$bc_BasicCoin_Balance'#0'_$memory|) _$t0)) (= (ControlFlow 0 18) 17)) |inline$$bc_BasicCoin_deposit'#0'$0$anon11_Then$1_correct|)))
(let ((|inline$$bc_BasicCoin_deposit'#0'$0$anon11_Else_correct|  (=> (and (|Select__T@[Int]Bool_| (|domain#$Memory_56677| |$bc_BasicCoin_Balance'#0'_$memory|) _$t0) (= call0formal@l@0 ($Global _$t0))) (=> (and (and (and (= call1formal@p@0 (Vec_11028 (MapConstVec_19835 DefaultVecElem_19835) 0)) (= call2formal@v@0@@1 (|Select__T@[Int]$bc_BasicCoin_Balance'#0'_| (|contents#$Memory_56677| |$bc_BasicCoin_Balance'#0'_$memory|) _$t0))) (and (= (|Select__T@[Int]$bc_BasicCoin_Balance'#0'_| (|contents#$Memory_56677| |$bc_BasicCoin_Balance'#0'_$memory|) _$t0) (|v#$Mutation_57347| call3formal@result@0@@1)) (= |$bc_BasicCoin_Balance'#0'_$memory@0| ($Memory_56677 (|Store__T@[Int]Bool_| (|domain#$Memory_56677| |$bc_BasicCoin_Balance'#0'_$memory|) _$t0 true) (|Store__T@[Int]$bc_BasicCoin_Balance'#0'_| (|contents#$Memory_56677| |$bc_BasicCoin_Balance'#0'_$memory|) _$t0 (|v_final#$Mutation_57347| call3formal@result@0@@1)))))) (and (and (= |$bc_BasicCoin_Balance'#0'_$memory@1| |$bc_BasicCoin_Balance'#0'_$memory@0|) (= $abort_code@2 $abort_code@1)) (and (= |inline$$bc_BasicCoin_deposit'#0'$0$$t9@1| call3formal@result@0@@1) (= $abort_flag@2 $abort_flag@1)))) (and (=> (= (ControlFlow 0 16) 10) |inline$$bc_BasicCoin_deposit'#0'$0$anon12_Then_correct|) (=> (= (ControlFlow 0 16) 15) |inline$$bc_BasicCoin_deposit'#0'$0$anon12_Else_correct|))))))
(let ((|inline$$bc_BasicCoin_deposit'#0'$0$anon10_Else_correct|  (=> (not $abort_flag@1) (and (=> (= (ControlFlow 0 19) 18) |inline$$bc_BasicCoin_deposit'#0'$0$anon11_Then_correct|) (=> (= (ControlFlow 0 19) 16) |inline$$bc_BasicCoin_deposit'#0'$0$anon11_Else_correct|)))))
(let ((|inline$$bc_BasicCoin_balance_of'#0'$0$anon7_Else_correct|  (=> (and (not $abort_flag@0) (= |inline$$bc_BasicCoin_balance_of'#0'$0$$t3@1| (|$coin#$bc_BasicCoin_Balance'#0'| |inline$$bc_BasicCoin_balance_of'#0'$0$$t1@2|))) (=> (and (and (= |inline$$bc_BasicCoin_balance_of'#0'$0$$t4@1| (|$value#$bc_BasicCoin_Coin'#0'| |inline$$bc_BasicCoin_balance_of'#0'$0$$t3@1|)) (= |inline$$bc_BasicCoin_balance_of'#0'$0$$t4@1| |inline$$bc_BasicCoin_balance_of'#0'$0$$t4@1|)) (and (= $abort_flag@1 $abort_flag@0) (= |inline$$bc_BasicCoin_balance_of'#0'$0$$ret0@1| |inline$$bc_BasicCoin_balance_of'#0'$0$$t4@1|))) (and (=> (= (ControlFlow 0 21) 9) |inline$$bc_BasicCoin_deposit'#0'$0$anon10_Then_correct|) (=> (= (ControlFlow 0 21) 19) |inline$$bc_BasicCoin_deposit'#0'$0$anon10_Else_correct|))))))
(let ((|inline$$bc_BasicCoin_balance_of'#0'$0$anon7_Then_correct|  (=> (and (and $abort_flag@0 (= $abort_code@1 $abort_code@1)) (and (= $abort_flag@1 true) (= |inline$$bc_BasicCoin_balance_of'#0'$0$$ret0@1| |inline$$bc_BasicCoin_balance_of'#0'$0$$ret0@0|))) (and (=> (= (ControlFlow 0 20) 9) |inline$$bc_BasicCoin_deposit'#0'$0$anon10_Then_correct|) (=> (= (ControlFlow 0 20) 19) |inline$$bc_BasicCoin_deposit'#0'$0$anon10_Else_correct|)))))
(let ((|inline$$bc_BasicCoin_balance_of'#0'$0$anon6_Then$1_correct|  (=> (= $abort_flag@0 true) (=> (and (= $abort_code@1 $EXEC_FAILURE_CODE) (= |inline$$bc_BasicCoin_balance_of'#0'$0$$t1@2| |inline$$bc_BasicCoin_balance_of'#0'$0$$t1@0|)) (and (=> (= (ControlFlow 0 23) 20) |inline$$bc_BasicCoin_balance_of'#0'$0$anon7_Then_correct|) (=> (= (ControlFlow 0 23) 21) |inline$$bc_BasicCoin_balance_of'#0'$0$anon7_Else_correct|))))))
(let ((|inline$$bc_BasicCoin_balance_of'#0'$0$anon6_Then_correct|  (=> (and (not (|Select__T@[Int]Bool_| (|domain#$Memory_56677| |$bc_BasicCoin_Balance'#0'_$memory|) _$t0)) (= (ControlFlow 0 24) 23)) |inline$$bc_BasicCoin_balance_of'#0'$0$anon6_Then$1_correct|)))
(let ((|inline$$bc_BasicCoin_balance_of'#0'$0$anon6_Else_correct|  (=> (|Select__T@[Int]Bool_| (|domain#$Memory_56677| |$bc_BasicCoin_Balance'#0'_$memory|) _$t0) (=> (and (and (= |inline$$bc_BasicCoin_balance_of'#0'$0$$t1@1| (|Select__T@[Int]$bc_BasicCoin_Balance'#0'_| (|contents#$Memory_56677| |$bc_BasicCoin_Balance'#0'_$memory|) _$t0)) (= $abort_flag@0 false)) (and (= $abort_code@1 $abort_code@0) (= |inline$$bc_BasicCoin_balance_of'#0'$0$$t1@2| |inline$$bc_BasicCoin_balance_of'#0'$0$$t1@1|))) (and (=> (= (ControlFlow 0 22) 20) |inline$$bc_BasicCoin_balance_of'#0'$0$anon7_Then_correct|) (=> (= (ControlFlow 0 22) 21) |inline$$bc_BasicCoin_balance_of'#0'$0$anon7_Else_correct|))))))
(let ((|inline$$bc_BasicCoin_balance_of'#0'$0$anon0_correct|  (=> (= _$t0 _$t0) (and (=> (= (ControlFlow 0 25) 24) |inline$$bc_BasicCoin_balance_of'#0'$0$anon6_Then_correct|) (=> (= (ControlFlow 0 25) 22) |inline$$bc_BasicCoin_balance_of'#0'$0$anon6_Else_correct|)))))
(let ((|inline$$bc_BasicCoin_deposit'#0'$0$anon0_correct|  (=> (= |inline$$bc_BasicCoin_deposit'#0'$0$$t5@0| (|$value#$bc_BasicCoin_Coin'#0'| (|$coin#$bc_BasicCoin_Balance'#0'| (|Select__T@[Int]$bc_BasicCoin_Balance'#0'_| (|contents#$Memory_56677| |$bc_BasicCoin_Balance'#0'_$memory|) _$t0)))) (=> (and (and (= |inline$$bc_BasicCoin_deposit'#0'$0$$t6@0| (|$value#$bc_BasicCoin_Coin'#0'| $t4@0)) (= _$t0 _$t0)) (and (= $t4@0 $t4@0) (= (ControlFlow 0 26) 25))) |inline$$bc_BasicCoin_balance_of'#0'$0$anon0_correct|))))
(let ((anon0$1_correct  (=> (|$IsValid'address'| _$t0) (=> (and (|$IsValid'u64'| _$t1) (forall (($a_0 Int) ) (! (let (($rsc (|Select__T@[Int]$bc_BasicCoin_Balance'#0'_| (|contents#$Memory_56677| |$bc_BasicCoin_Balance'#0'_$memory|) $a_0)))
(|$IsValid'$bc_BasicCoin_Balance'#0''| $rsc))
 :qid |outputbpl.5167:20|
 :skolemid |176|
 :pattern ( (|Select__T@[Int]$bc_BasicCoin_Balance'#0'_| (|contents#$Memory_56677| |$bc_BasicCoin_Balance'#0'_$memory|) $a_0))
))) (=> (and (and (and (= $t3 (|$value#$bc_BasicCoin_Coin'#0'| (|$coin#$bc_BasicCoin_Balance'#0'| (|Select__T@[Int]$bc_BasicCoin_Balance'#0'_| (|contents#$Memory_56677| |$bc_BasicCoin_Balance'#0'_$memory|) _$t0)))) (= _$t0 _$t0)) (and (= _$t1 _$t1) (= _$t2 _$t2))) (and (and (= $t4@0 (|$bc_BasicCoin_Coin'#0'| _$t1)) (= $t5 (|$value#$bc_BasicCoin_Coin'#0'| (|$coin#$bc_BasicCoin_Balance'#0'| (|Select__T@[Int]$bc_BasicCoin_Balance'#0'_| (|contents#$Memory_56677| |$bc_BasicCoin_Balance'#0'_$memory|) _$t0))))) (and (= $t6 (|$value#$bc_BasicCoin_Coin'#0'| $t4@0)) (= (ControlFlow 0 27) 26)))) |inline$$bc_BasicCoin_deposit'#0'$0$anon0_correct|)))))
(let ((inline$$InitVerification$0$anon3_Else_correct  (=> $cur_index_initialized (=> (and (= $cur_index@0 $cur_index) (= (ControlFlow 0 29) 27)) anon0$1_correct))))
(let ((inline$$InitVerification$0$anon3_Then_correct  (=> (not $cur_index_initialized) (=> (and (= $cur_index@0 0) (= (ControlFlow 0 28) 27)) anon0$1_correct))))
(let ((anon0_correct  (and (=> (= (ControlFlow 0 30) 28) inline$$InitVerification$0$anon3_Then_correct) (=> (= (ControlFlow 0 30) 29) inline$$InitVerification$0$anon3_Else_correct))))
anon0_correct)))))))))))))))))))))))))))
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
(declare-sort T@T_11073 0)
(declare-sort T@T2_11267 0)
(declare-sort |T@[Int]Bool| 0)
(declare-sort |T@#0| 0)
(declare-sort |T@[Int]#0| 0)
(declare-sort |T@[Int]$bc_BasicCoin_Balance'#0'| 0)
(declare-datatypes ((T@$Memory_56317 0)) ((($Memory_56317 (|domain#$Memory_56317| |T@[Int]Bool|) (|contents#$Memory_56317| |T@[Int]#0|) ) ) ))
(declare-datatypes ((T@$bc_ProphecyBenchmark3Levels2Fields_Node1 0)) ((($bc_ProphecyBenchmark3Levels2Fields_Node1 (|$v0#$bc_ProphecyBenchmark3Levels2Fields_Node1| Int) (|$v1#$bc_ProphecyBenchmark3Levels2Fields_Node1| Int) (|$v2#$bc_ProphecyBenchmark3Levels2Fields_Node1| Int) (|$v3#$bc_ProphecyBenchmark3Levels2Fields_Node1| Int) (|$v4#$bc_ProphecyBenchmark3Levels2Fields_Node1| Int) (|$v5#$bc_ProphecyBenchmark3Levels2Fields_Node1| Int) (|$v6#$bc_ProphecyBenchmark3Levels2Fields_Node1| Int) (|$v7#$bc_ProphecyBenchmark3Levels2Fields_Node1| Int) ) ) ))
(declare-datatypes ((T@$bc_ProphecyBenchmark3Levels2Fields_Node2 0)) ((($bc_ProphecyBenchmark3Levels2Fields_Node2 (|$v0#$bc_ProphecyBenchmark3Levels2Fields_Node2| T@$bc_ProphecyBenchmark3Levels2Fields_Node1) (|$v1#$bc_ProphecyBenchmark3Levels2Fields_Node2| T@$bc_ProphecyBenchmark3Levels2Fields_Node1) (|$v2#$bc_ProphecyBenchmark3Levels2Fields_Node2| T@$bc_ProphecyBenchmark3Levels2Fields_Node1) (|$v3#$bc_ProphecyBenchmark3Levels2Fields_Node2| T@$bc_ProphecyBenchmark3Levels2Fields_Node1) (|$v4#$bc_ProphecyBenchmark3Levels2Fields_Node2| T@$bc_ProphecyBenchmark3Levels2Fields_Node1) (|$v5#$bc_ProphecyBenchmark3Levels2Fields_Node2| T@$bc_ProphecyBenchmark3Levels2Fields_Node1) (|$v6#$bc_ProphecyBenchmark3Levels2Fields_Node2| T@$bc_ProphecyBenchmark3Levels2Fields_Node1) (|$v7#$bc_ProphecyBenchmark3Levels2Fields_Node2| T@$bc_ProphecyBenchmark3Levels2Fields_Node1) ) ) ))
(declare-datatypes ((T@$bc_ProphecyBenchmark3Levels2Fields_Node3 0)) ((($bc_ProphecyBenchmark3Levels2Fields_Node3 (|$v0#$bc_ProphecyBenchmark3Levels2Fields_Node3| T@$bc_ProphecyBenchmark3Levels2Fields_Node2) (|$v1#$bc_ProphecyBenchmark3Levels2Fields_Node3| T@$bc_ProphecyBenchmark3Levels2Fields_Node2) (|$v2#$bc_ProphecyBenchmark3Levels2Fields_Node3| T@$bc_ProphecyBenchmark3Levels2Fields_Node2) (|$v3#$bc_ProphecyBenchmark3Levels2Fields_Node3| T@$bc_ProphecyBenchmark3Levels2Fields_Node2) (|$v4#$bc_ProphecyBenchmark3Levels2Fields_Node3| T@$bc_ProphecyBenchmark3Levels2Fields_Node2) (|$v5#$bc_ProphecyBenchmark3Levels2Fields_Node3| T@$bc_ProphecyBenchmark3Levels2Fields_Node2) (|$v6#$bc_ProphecyBenchmark3Levels2Fields_Node3| T@$bc_ProphecyBenchmark3Levels2Fields_Node2) (|$v7#$bc_ProphecyBenchmark3Levels2Fields_Node3| T@$bc_ProphecyBenchmark3Levels2Fields_Node2) ) ) ))
(declare-datatypes ((|T@$bc_BasicCoin_Coin'#0'| 0)) (((|$bc_BasicCoin_Coin'#0'| (|$value#$bc_BasicCoin_Coin'#0'| Int) ) ) ))
(declare-datatypes ((|T@$bc_BasicCoin_Balance'#0'| 0)) (((|$bc_BasicCoin_Balance'#0'| (|$coin#$bc_BasicCoin_Balance'#0'| |T@$bc_BasicCoin_Coin'#0'|) ) ) ))
(declare-datatypes ((T@$Memory_56677 0)) ((($Memory_56677 (|domain#$Memory_56677| |T@[Int]Bool|) (|contents#$Memory_56677| |T@[Int]$bc_BasicCoin_Balance'#0'|) ) ) ))
(declare-datatypes ((T@Vec_11028 0)) (((Vec_11028 (|v#Vec_11028| |T@[Int]Int|) (|l#Vec_11028| Int) ) ) ))
(declare-datatypes ((T@$TypeParamInfo 0)) ((($TypeParamBool ) ($TypeParamU8 ) ($TypeParamU16 ) ($TypeParamU32 ) ($TypeParamU64 ) ($TypeParamU128 ) ($TypeParamU256 ) ($TypeParamI8 ) ($TypeParamI16 ) ($TypeParamI32 ) ($TypeParamI64 ) ($TypeParamI128 ) ($TypeParamI256 ) ($TypeParamAddress ) ($TypeParamSigner ) ($TypeParamVector (|e#$TypeParamVector| T@$TypeParamInfo) ) ($TypeParamStruct (|a#$TypeParamStruct| Int) (|m#$TypeParamStruct| T@Vec_11028) (|s#$TypeParamStruct| T@Vec_11028) ) ) ))
(declare-datatypes ((T@$signer 0)) ((($signer (|$addr#$signer| Int) ) ($permissioned_signer (|$addr#$permissioned_signer| Int) (|$permission_addr#$permissioned_signer| Int) ) ) ))
(declare-datatypes ((T@$Location 0)) ((($Global (|a#$Global| Int) ) ($Local (|i#$Local| Int) ) ($Param (|i#$Param| Int) ) ($Uninitialized ) ) ))
(declare-datatypes ((T@$Mutation_64216 0)) ((($Mutation_64216 (|l#$Mutation_64216| T@$Location) (|p#$Mutation_64216| T@Vec_11028) (|v#$Mutation_64216| T@$bc_ProphecyBenchmark3Levels2Fields_Node1) (|v_final#$Mutation_64216| T@$bc_ProphecyBenchmark3Levels2Fields_Node1) ) ) ))
(declare-datatypes ((T@$Mutation_64193 0)) ((($Mutation_64193 (|l#$Mutation_64193| T@$Location) (|p#$Mutation_64193| T@Vec_11028) (|v#$Mutation_64193| T@$bc_ProphecyBenchmark3Levels2Fields_Node2) (|v_final#$Mutation_64193| T@$bc_ProphecyBenchmark3Levels2Fields_Node2) ) ) ))
(declare-datatypes ((T@$Mutation_64170 0)) ((($Mutation_64170 (|l#$Mutation_64170| T@$Location) (|p#$Mutation_64170| T@Vec_11028) (|v#$Mutation_64170| T@$bc_ProphecyBenchmark3Levels2Fields_Node3) (|v_final#$Mutation_64170| T@$bc_ProphecyBenchmark3Levels2Fields_Node3) ) ) ))
(declare-datatypes ((T@$Mutation_57370 0)) ((($Mutation_57370 (|l#$Mutation_57370| T@$Location) (|p#$Mutation_57370| T@Vec_11028) (|v#$Mutation_57370| |T@$bc_BasicCoin_Coin'#0'|) (|v_final#$Mutation_57370| |T@$bc_BasicCoin_Coin'#0'|) ) ) ))
(declare-datatypes ((T@$Mutation_57347 0)) ((($Mutation_57347 (|l#$Mutation_57347| T@$Location) (|p#$Mutation_57347| T@Vec_11028) (|v#$Mutation_57347| |T@$bc_BasicCoin_Balance'#0'|) (|v_final#$Mutation_57347| |T@$bc_BasicCoin_Balance'#0'|) ) ) ))
(declare-datatypes ((T@$Mutation_21031 0)) ((($Mutation_21031 (|l#$Mutation_21031| T@$Location) (|p#$Mutation_21031| T@Vec_11028) (|v#$Mutation_21031| Int) (|v_final#$Mutation_21031| Int) ) ) ))
(declare-datatypes ((T@$Mutation_49529 0)) ((($Mutation_49529 (|l#$Mutation_49529| T@$Location) (|p#$Mutation_49529| T@Vec_11028) (|v#$Mutation_49529| T@Vec_11028) (|v_final#$Mutation_49529| T@Vec_11028) ) ) ))
(declare-datatypes ((T@$Mutation_36883 0)) ((($Mutation_36883 (|l#$Mutation_36883| T@$Location) (|p#$Mutation_36883| T@Vec_11028) (|v#$Mutation_36883| T@T2_11267) (|v_final#$Mutation_36883| T@T2_11267) ) ) ))
(declare-datatypes ((T@$Mutation_36750 0)) ((($Mutation_36750 (|l#$Mutation_36750| T@$Location) (|p#$Mutation_36750| T@Vec_11028) (|v#$Mutation_36750| T@T_11073) (|v_final#$Mutation_36750| T@T_11073) ) ) ))
(declare-datatypes ((T@$Range 0)) ((($Range (|lb#$Range| Int) (|ub#$Range| Int) ) ) ))
(declare-fun $MAX_U128 () Int)
(declare-fun $MAX_I128 () Int)
(declare-fun $TypeName (T@$TypeParamInfo) T@Vec_11028)
(declare-fun |$IsEqual'vec'u8''| (T@Vec_11028 T@Vec_11028) Bool)
(declare-fun |Store__T@[Int]Int_| (|T@[Int]Int| Int Int) |T@[Int]Int|)
(declare-fun |Select__T@[Int]Int_| (|T@[Int]Int| Int) Int)
(assert (forall ( ( ?x0 |T@[Int]Int|) ( ?x1 Int) ( ?x2 Int)) (! (= (|Select__T@[Int]Int_| (|Store__T@[Int]Int_| ?x0 ?x1 ?x2) ?x1)  ?x2) :weight 0)))
(assert (forall ( ( ?x0 |T@[Int]Int|) ( ?x1 Int) ( ?y1 Int) ( ?x2 Int)) (! (=>  (not (= ?x1 ?y1)) (= (|Select__T@[Int]Int_| (|Store__T@[Int]Int_| ?x0 ?x1 ?x2) ?y1) (|Select__T@[Int]Int_| ?x0 ?y1))) :weight 0)))
(declare-fun MapConstVec_19835 (Int) |T@[Int]Int|)
(declare-fun DefaultVecElem_19835 () Int)
(declare-fun $MIN_I128 () Int)
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
(declare-fun $ConstMemoryDomain (Bool) |T@[Int]Bool|)
(declare-fun |lambda#4| (Bool) |T@[Int]Bool|)
(declare-fun InRangeVec_19490 (T@Vec_11028 Int) Bool)
(declare-fun |$IsPrefix'vec'u8''| (T@Vec_11028 T@Vec_11028) Bool)
(declare-fun DefaultTableKeyExistsArray_990 () |T@[Int]Bool|)
(declare-fun IndexOfVec_11028 (T@Vec_11028 Int) Int)
(declare-fun $1_Signature_$ed25519_verify (T@Vec_11028 T@Vec_11028 T@Vec_11028) Bool)
(declare-fun |lambda#0| (Int Int Int |T@[Int]Int| |T@[Int]Int| Int Int) |T@[Int]Int|)
(declare-fun |lambda#3| (Int Int Int |T@[Int]Int| |T@[Int]Int| Int Int) |T@[Int]Int|)
(declare-fun |$IsValid'bv32'| ((_ BitVec 32)) Bool)
(declare-fun |$IsValid'address'| (Int) Bool)
(declare-fun |$IsSuffix'vec'u8''| (T@Vec_11028 T@Vec_11028) Bool)
(declare-fun |lambda#2| (Int Int |T@[Int]Int| Int Int) |T@[Int]Int|)
(declare-fun $shl (Int Int) Int)
(declare-fun $castBv64to8 ((_ BitVec 64)) (_ BitVec 8))
(declare-fun |$Arbitrary_value_of'bv8'| () (_ BitVec 8))
(declare-fun $castBv256to8 ((_ BitVec 256)) (_ BitVec 8))
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
(declare-fun |$IsValid'vec'u8''| (T@Vec_11028) Bool)
(declare-fun |$IsValid'u64'| (Int) Bool)
(declare-fun |$IsValid'u8'| (Int) Bool)
(declare-fun |Select__T@[Int]Bool_| (|T@[Int]Bool| Int) Bool)
(declare-fun |$IsValid'num'| (Int) Bool)
(declare-fun $castBv8to64 ((_ BitVec 8)) (_ BitVec 64))
(declare-fun $castBv64to256 ((_ BitVec 64)) (_ BitVec 256))
(declare-fun $castBv8to256 ((_ BitVec 8)) (_ BitVec 256))
(declare-fun $undefined_int () Int)
(declare-fun |$IsValid'$bc_BasicCoin_Balance'#0''| (|T@$bc_BasicCoin_Balance'#0'|) Bool)
(declare-fun |$IsValid'$bc_BasicCoin_Coin'#0''| (|T@$bc_BasicCoin_Coin'#0'|) Bool)
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
(declare-fun |$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node1'| (T@$bc_ProphecyBenchmark3Levels2Fields_Node1) Bool)
(declare-fun |$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node2'| (T@$bc_ProphecyBenchmark3Levels2Fields_Node2) Bool)
(declare-fun |$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node3'| (T@$bc_ProphecyBenchmark3Levels2Fields_Node3) Bool)
(declare-fun $castBv8to8 ((_ BitVec 8)) (_ BitVec 8))
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
(declare-fun $1_Signature_$ed25519_validate_pubkey (T@Vec_11028) Bool)
(declare-fun |$IsValid'bv8'| ((_ BitVec 8)) Bool)
(declare-fun |$IsValid'bv64'| ((_ BitVec 64)) Bool)
(declare-fun |$IsValid'bv16'| ((_ BitVec 16)) Bool)
(declare-fun |$IsValid'bv256'| ((_ BitVec 256)) Bool)
(declare-fun |$IndexOfVec'u8'| (T@Vec_11028 Int) Int)
(declare-fun |$IsValid'bv128'| ((_ BitVec 128)) Bool)
(declare-fun $1_hash_sha2 (T@Vec_11028) T@Vec_11028)
(declare-fun $1_hash_sha3 (T@Vec_11028) T@Vec_11028)
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
(assert (forall ((t T@$TypeParamInfo) ) (!  (=> (is-$TypeParamU128 t) (|$IsEqual'vec'u8''| ($TypeName t) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 117) 1 49) 2 50) 3 56) 4)))
 :qid |outputbpl.4348:15|
 :skolemid |147|
 :pattern ( ($TypeName t))
)))
(assert (= $MIN_I128 (- 0 170141183460469231731687303715884105728)))
(assert (forall ((t@@0 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamU256 t@@0) (|$IsEqual'vec'u8''| ($TypeName t@@0) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 117) 1 50) 2 53) 3 54) 4)))
 :qid |outputbpl.4350:15|
 :skolemid |149|
 :pattern ( ($TypeName t@@0))
)))
(assert (forall ((|l#0| Int) (|l#1| Int) (|l#2| |T@[Int]Int|) (|l#3| Int) (|l#4| Int) (|l#5| Int) (i Int) ) (! (= (|Select__T@[Int]Int_| (|lambda#1| |l#0| |l#1| |l#2| |l#3| |l#4| |l#5|) i) (ite  (and (<= |l#0| i) (< i |l#1|)) (|Select__T@[Int]Int_| |l#2| (- (- |l#3| i) |l#4|)) |l#5|))
 :qid |outputbpl.83:30|
 :skolemid |184|
 :pattern ( (|Select__T@[Int]Int_| (|lambda#1| |l#0| |l#1| |l#2| |l#3| |l#4| |l#5|) i))
)))
(assert (forall ((src1 Int) (p Int) ) (! (= ($shr src1 p) (div src1 ($pow 2 p)))
 :qid |outputbpl.1010:15|
 :skolemid |22|
 :pattern ( ($shr src1 p))
)))
(assert (forall ((src1@@0 Int) (p@@0 Int) ) (! (= ($shlU8 src1@@0 p@@0) (mod (* src1@@0 ($pow 2 p@@0)) (+ $MAX_U8 1)))
 :qid |outputbpl.1025:17|
 :skolemid |23|
 :pattern ( ($shlU8 src1@@0 p@@0))
)))
(assert (forall ((src1@@1 Int) (p@@1 Int) ) (! (= ($shlU16 src1@@1 p@@1) (mod (* src1@@1 ($pow 2 p@@1)) (+ $MAX_U16 1)))
 :qid |outputbpl.1056:18|
 :skolemid |24|
 :pattern ( ($shlU16 src1@@1 p@@1))
)))
(assert (forall ((src1@@2 Int) (p@@2 Int) ) (! (= ($shlU32 src1@@2 p@@2) (mod (* src1@@2 ($pow 2 p@@2)) (+ $MAX_U32 1)))
 :qid |outputbpl.1087:18|
 :skolemid |25|
 :pattern ( ($shlU32 src1@@2 p@@2))
)))
(assert (forall ((src1@@3 Int) (p@@3 Int) ) (! (= ($shlU64 src1@@3 p@@3) (mod (* src1@@3 ($pow 2 p@@3)) (+ $MAX_U64 1)))
 :qid |outputbpl.1118:18|
 :skolemid |26|
 :pattern ( ($shlU64 src1@@3 p@@3))
)))
(assert (forall ((src1@@4 Int) (p@@4 Int) ) (! (= ($shlU128 src1@@4 p@@4) (mod (* src1@@4 ($pow 2 p@@4)) (+ $MAX_U128 1)))
 :qid |outputbpl.1149:19|
 :skolemid |27|
 :pattern ( ($shlU128 src1@@4 p@@4))
)))
(assert (forall ((src1@@5 Int) (p@@5 Int) ) (! (= ($shlU256 src1@@5 p@@5) (mod (* src1@@5 ($pow 2 p@@5)) (+ $MAX_U256 1)))
 :qid |outputbpl.1180:19|
 :skolemid |28|
 :pattern ( ($shlU256 src1@@5 p@@5))
)))
(assert (= ($ConstMemoryDomain false) (|lambda#4| false)))
(assert (= ($ConstMemoryDomain true) (|lambda#4| true)))
(assert (forall ((v1 T@Vec_11028) (v2 T@Vec_11028) ) (! (= (|$IsEqual'vec'u8''| v1 v2)  (and (= (|l#Vec_11028| v1) (|l#Vec_11028| v2)) (forall ((i@@0 Int) ) (!  (=> (InRangeVec_19490 v1 i@@0) (= (|Select__T@[Int]Int_| (|v#Vec_11028| v1) i@@0) (|Select__T@[Int]Int_| (|v#Vec_11028| v2) i@@0)))
 :qid |outputbpl.3825:13|
 :skolemid |122|
))))
 :qid |outputbpl.3823:28|
 :skolemid |123|
 :pattern ( (|$IsEqual'vec'u8''| v1 v2))
)))
(assert (forall ((v T@Vec_11028) (prefix T@Vec_11028) ) (! (= (|$IsPrefix'vec'u8''| v prefix)  (and (>= (|l#Vec_11028| v) (|l#Vec_11028| prefix)) (forall ((i@@1 Int) ) (!  (=> (InRangeVec_19490 prefix i@@1) (= (|Select__T@[Int]Int_| (|v#Vec_11028| v) i@@1) (|Select__T@[Int]Int_| (|v#Vec_11028| prefix) i@@1)))
 :qid |outputbpl.3831:13|
 :skolemid |124|
))))
 :qid |outputbpl.3829:29|
 :skolemid |125|
 :pattern ( (|$IsPrefix'vec'u8''| v prefix))
)))
(assert (= DefaultTableKeyExistsArray_990 (|lambda#4| false)))
(assert (forall ((v@@0 T@Vec_11028) (e Int) ) (! (let ((i@@2 (IndexOfVec_11028 v@@0 e)))
(ite  (not (exists ((i@@3 Int) ) (!  (and (InRangeVec_19490 v@@0 i@@3) (= (|Select__T@[Int]Int_| (|v#Vec_11028| v@@0) i@@3) e))
 :qid |outputbpl.110:13|
 :skolemid |0|
))) (= i@@2 (- 0 1))  (and (and (InRangeVec_19490 v@@0 i@@2) (= (|Select__T@[Int]Int_| (|v#Vec_11028| v@@0) i@@2) e)) (forall ((j Int) ) (!  (=> (and (>= j 0) (< j i@@2)) (not (= (|Select__T@[Int]Int_| (|v#Vec_11028| v@@0) j) e)))
 :qid |outputbpl.118:17|
 :skolemid |1|
)))))
 :qid |outputbpl.114:32|
 :skolemid |2|
 :pattern ( (IndexOfVec_11028 v@@0 e))
)))
(assert (forall ((t@@1 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamI128 t@@1) (|$IsEqual'vec'u8''| ($TypeName t@@1) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 105) 1 49) 2 50) 3 56) 4)))
 :qid |outputbpl.4360:15|
 :skolemid |159|
 :pattern ( ($TypeName t@@1))
)))
(assert (forall ((t@@2 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamI256 t@@2) (|$IsEqual'vec'u8''| ($TypeName t@@2) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 105) 1 50) 2 53) 3 54) 4)))
 :qid |outputbpl.4362:15|
 :skolemid |161|
 :pattern ( ($TypeName t@@2))
)))
(assert (forall ((s1 T@Vec_11028) (s2 T@Vec_11028) (k1 T@Vec_11028) (k2 T@Vec_11028) (m1 T@Vec_11028) (m2 T@Vec_11028) ) (!  (=> (and (and (|$IsEqual'vec'u8''| s1 s2) (|$IsEqual'vec'u8''| k1 k2)) (|$IsEqual'vec'u8''| m1 m2)) (= ($1_Signature_$ed25519_verify s1 k1 m1) ($1_Signature_$ed25519_verify s2 k2 m2)))
 :qid |outputbpl.4277:15|
 :skolemid |136|
 :pattern ( ($1_Signature_$ed25519_verify s1 k1 m1) ($1_Signature_$ed25519_verify s2 k2 m2))
)))
(assert (forall ((|l#0@@0| Int) (|l#1@@0| Int) (|l#2@@0| Int) (|l#3@@0| |T@[Int]Int|) (|l#4@@0| |T@[Int]Int|) (|l#5@@0| Int) (|l#6| Int) (i@@4 Int) ) (! (= (|Select__T@[Int]Int_| (|lambda#0| |l#0@@0| |l#1@@0| |l#2@@0| |l#3@@0| |l#4@@0| |l#5@@0| |l#6|) i@@4) (ite  (and (>= i@@4 |l#0@@0|) (< i@@4 |l#1@@0|)) (ite (< i@@4 |l#2@@0|) (|Select__T@[Int]Int_| |l#3@@0| i@@4) (|Select__T@[Int]Int_| |l#4@@0| (- i@@4 |l#5@@0|))) |l#6|))
 :qid |outputbpl.74:19|
 :skolemid |183|
 :pattern ( (|Select__T@[Int]Int_| (|lambda#0| |l#0@@0| |l#1@@0| |l#2@@0| |l#3@@0| |l#4@@0| |l#5@@0| |l#6|) i@@4))
)))
(assert (forall ((|l#0@@1| Int) (|l#1@@1| Int) (|l#2@@1| Int) (|l#3@@1| |T@[Int]Int|) (|l#4@@1| |T@[Int]Int|) (|l#5@@1| Int) (|l#6@@0| Int) (j@@0 Int) ) (! (= (|Select__T@[Int]Int_| (|lambda#3| |l#0@@1| |l#1@@1| |l#2@@1| |l#3@@1| |l#4@@1| |l#5@@1| |l#6@@0|) j@@0) (ite  (and (>= j@@0 |l#0@@1|) (< j@@0 |l#1@@1|)) (ite (< j@@0 |l#2@@1|) (|Select__T@[Int]Int_| |l#3@@1| j@@0) (|Select__T@[Int]Int_| |l#4@@1| (+ j@@0 |l#5@@1|))) |l#6@@0|))
 :qid |outputbpl.64:20|
 :skolemid |186|
 :pattern ( (|Select__T@[Int]Int_| (|lambda#3| |l#0@@1| |l#1@@1| |l#2@@1| |l#3@@1| |l#4@@1| |l#5@@1| |l#6@@0|) j@@0))
)))
(assert (forall ((v@@1 (_ BitVec 32)) ) (! (= (|$IsValid'bv32'| v@@1)  (and (bvuge v@@1 #x00000000) (bvule v@@1 #x7fffffff)))
 :qid |outputbpl.1657:25|
 :skolemid |31|
 :pattern ( (|$IsValid'bv32'| v@@1))
)))
(assert (forall ((v@@2 Int) ) (! (= (|$IsValid'address'| v@@2) (>= v@@2 0))
 :qid |outputbpl.2069:28|
 :skolemid |36|
 :pattern ( (|$IsValid'address'| v@@2))
)))
(assert (forall ((t@@3 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamSigner t@@3) (|$IsEqual'vec'u8''| ($TypeName t@@3) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 115) 1 105) 2 103) 3 110) 4 101) 5 114) 6)))
 :qid |outputbpl.4366:15|
 :skolemid |165|
 :pattern ( ($TypeName t@@3))
)))
(assert (forall ((v@@3 T@Vec_11028) (suffix T@Vec_11028) ) (! (= (|$IsSuffix'vec'u8''| v@@3 suffix)  (and (>= (|l#Vec_11028| v@@3) (|l#Vec_11028| suffix)) (forall ((i@@5 Int) ) (!  (=> (InRangeVec_19490 suffix i@@5) (= (|Select__T@[Int]Int_| (|v#Vec_11028| v@@3) (+ (- (|l#Vec_11028| v@@3) (|l#Vec_11028| suffix)) i@@5)) (|Select__T@[Int]Int_| (|v#Vec_11028| suffix) i@@5)))
 :qid |outputbpl.3837:13|
 :skolemid |126|
))))
 :qid |outputbpl.3835:29|
 :skolemid |127|
 :pattern ( (|$IsSuffix'vec'u8''| v@@3 suffix))
)))
(assert (forall ((|l#0@@2| Int) (|l#1@@2| Int) (|l#2@@2| |T@[Int]Int|) (|l#3@@2| Int) (|l#4@@2| Int) (k Int) ) (! (= (|Select__T@[Int]Int_| (|lambda#2| |l#0@@2| |l#1@@2| |l#2@@2| |l#3@@2| |l#4@@2|) k) (ite  (and (<= |l#0@@2| k) (< k |l#1@@2|)) (|Select__T@[Int]Int_| |l#2@@2| (+ |l#3@@2| k)) |l#4@@2|))
 :qid |outputbpl.91:14|
 :skolemid |185|
 :pattern ( (|Select__T@[Int]Int_| (|lambda#2| |l#0@@2| |l#1@@2| |l#2@@2| |l#3@@2| |l#4@@2|) k))
)))
(assert (forall ((src1@@6 Int) (p@@6 Int) ) (! (= ($shl src1@@6 p@@6) (* src1@@6 ($pow 2 p@@6)))
 :qid |outputbpl.1006:15|
 :skolemid |21|
 :pattern ( ($shl src1@@6 p@@6))
)))
(assert (forall ((t@@4 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@4) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 117) 1 49) 2 54) 3)) (is-$TypeParamU16 t@@4))
 :qid |outputbpl.4343:15|
 :skolemid |142|
 :pattern ( ($TypeName t@@4))
)))
(assert (forall ((t@@5 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@5) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 117) 1 51) 2 50) 3)) (is-$TypeParamU32 t@@5))
 :qid |outputbpl.4345:15|
 :skolemid |144|
 :pattern ( ($TypeName t@@5))
)))
(assert (forall ((t@@6 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@6) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 117) 1 54) 2 52) 3)) (is-$TypeParamU64 t@@6))
 :qid |outputbpl.4347:15|
 :skolemid |146|
 :pattern ( ($TypeName t@@6))
)))
(assert (forall ((t@@7 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamAddress t@@7) (|$IsEqual'vec'u8''| ($TypeName t@@7) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 97) 1 100) 2 100) 3 114) 4 101) 5 115) 6 115) 7)))
 :qid |outputbpl.4364:15|
 :skolemid |163|
 :pattern ( ($TypeName t@@7))
)))
(assert (forall ((t@@8 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamVector t@@8) (|$IsEqual'vec'u8''| ($TypeName t@@8) (let ((m2@@0 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 62) 1))))
(let ((l2 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 62) 1))))
(let ((m1@@0 (|v#Vec_11028| (let ((m2@@1 (|v#Vec_11028| ($TypeName (|e#$TypeParamVector| t@@8)))))
(let ((l2@@0 (|l#Vec_11028| ($TypeName (|e#$TypeParamVector| t@@8)))))
(let ((m1@@1 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 118) 1 101) 2 99) 3 116) 4 111) 5 114) 6 60) 7))))
(let ((l1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 118) 1 101) 2 99) 3 116) 4 111) 5 114) 6 60) 7))))
(Vec_11028 (|lambda#0| 0 (+ l1 l2@@0) l1 m1@@1 m2@@1 l1 DefaultVecElem_19835) (+ l1 l2@@0)))))))))
(let ((l1@@0 (|l#Vec_11028| (let ((m2@@1 (|v#Vec_11028| ($TypeName (|e#$TypeParamVector| t@@8)))))
(let ((l2@@0 (|l#Vec_11028| ($TypeName (|e#$TypeParamVector| t@@8)))))
(let ((m1@@1 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 118) 1 101) 2 99) 3 116) 4 111) 5 114) 6 60) 7))))
(let ((l1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 118) 1 101) 2 99) 3 116) 4 111) 5 114) 6 60) 7))))
(Vec_11028 (|lambda#0| 0 (+ l1 l2@@0) l1 m1@@1 m2@@1 l1 DefaultVecElem_19835) (+ l1 l2@@0)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@0 l2) l1@@0 m1@@0 m2@@0 l1@@0 DefaultVecElem_19835) (+ l1@@0 l2))))))))
 :qid |outputbpl.4368:15|
 :skolemid |167|
 :pattern ( ($TypeName t@@8))
)))
(assert (forall ((src (_ BitVec 64)) ) (! (= ($castBv64to8 src) (ite (bvugt src #x00000000000000ff) |$Arbitrary_value_of'bv8'| ((_ extract 7 0) src)))
 :qid |outputbpl.2505:23|
 :skolemid |48|
 :pattern ( ($castBv64to8 src))
)))
(assert (forall ((src@@0 (_ BitVec 256)) ) (! (= ($castBv256to8 src@@0) (ite (bvugt src@@0 #x00000000000000000000000000000000000000000000000000000000000000ff) |$Arbitrary_value_of'bv8'| ((_ extract 7 0) src@@0)))
 :qid |outputbpl.2595:24|
 :skolemid |53|
 :pattern ( ($castBv256to8 src@@0))
)))
(assert (forall ((src@@1 (_ BitVec 256)) ) (! (= ($castBv256to64 src@@1) (ite (bvugt src@@1 #x000000000000000000000000000000000000000000000000ffffffffffffffff) |$Arbitrary_value_of'bv64'| ((_ extract 63 0) src@@1)))
 :qid |outputbpl.3315:25|
 :skolemid |92|
 :pattern ( ($castBv256to64 src@@1))
)))
(assert (= $MAX_I32 2147483647))
(assert (= $MIN_I32 (- 0 2147483648)))
(assert (forall ((t@@9 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@9) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 98) 1 111) 2 111) 3 108) 4)) (is-$TypeParamBool t@@9))
 :qid |outputbpl.4339:15|
 :skolemid |138|
 :pattern ( ($TypeName t@@9))
)))
(assert (forall ((src1@@7 (_ BitVec 8)) (src2 (_ BitVec 16)) ) (! (= ($shlBv8From16 src1@@7 src2) (bvshl src1@@7 ((_ extract 7 0) src2)))
 :qid |outputbpl.2424:24|
 :skolemid |44|
 :pattern ( ($shlBv8From16 src1@@7 src2))
)))
(assert (forall ((src1@@8 (_ BitVec 8)) (src2@@0 (_ BitVec 16)) ) (! (= ($shrBv8From16 src1@@8 src2@@0) (bvlshr src1@@8 ((_ extract 7 0) src2@@0)))
 :qid |outputbpl.2439:24|
 :skolemid |45|
 :pattern ( ($shrBv8From16 src1@@8 src2@@0))
)))
(assert (forall ((src1@@9 (_ BitVec 8)) (src2@@1 (_ BitVec 32)) ) (! (= ($shlBv8From32 src1@@9 src2@@1) (bvshl src1@@9 ((_ extract 7 0) src2@@1)))
 :qid |outputbpl.2465:24|
 :skolemid |46|
 :pattern ( ($shlBv8From32 src1@@9 src2@@1))
)))
(assert (forall ((src1@@10 (_ BitVec 8)) (src2@@2 (_ BitVec 32)) ) (! (= ($shrBv8From32 src1@@10 src2@@2) (bvlshr src1@@10 ((_ extract 7 0) src2@@2)))
 :qid |outputbpl.2480:24|
 :skolemid |47|
 :pattern ( ($shrBv8From32 src1@@10 src2@@2))
)))
(assert (forall ((src1@@11 (_ BitVec 8)) (src2@@3 (_ BitVec 64)) ) (! (= ($shlBv8From64 src1@@11 src2@@3) (bvshl src1@@11 ((_ extract 7 0) src2@@3)))
 :qid |outputbpl.2514:24|
 :skolemid |49|
 :pattern ( ($shlBv8From64 src1@@11 src2@@3))
)))
(assert (forall ((src1@@12 (_ BitVec 8)) (src2@@4 (_ BitVec 64)) ) (! (= ($shrBv8From64 src1@@12 src2@@4) (bvlshr src1@@12 ((_ extract 7 0) src2@@4)))
 :qid |outputbpl.2529:24|
 :skolemid |50|
 :pattern ( ($shrBv8From64 src1@@12 src2@@4))
)))
(assert (forall ((src1@@13 (_ BitVec 8)) (src2@@5 (_ BitVec 128)) ) (! (= ($shlBv8From128 src1@@13 src2@@5) (bvshl src1@@13 ((_ extract 7 0) src2@@5)))
 :qid |outputbpl.2555:25|
 :skolemid |51|
 :pattern ( ($shlBv8From128 src1@@13 src2@@5))
)))
(assert (forall ((src1@@14 (_ BitVec 8)) (src2@@6 (_ BitVec 128)) ) (! (= ($shrBv8From128 src1@@14 src2@@6) (bvlshr src1@@14 ((_ extract 7 0) src2@@6)))
 :qid |outputbpl.2570:25|
 :skolemid |52|
 :pattern ( ($shrBv8From128 src1@@14 src2@@6))
)))
(assert (forall ((src1@@15 (_ BitVec 8)) (src2@@7 (_ BitVec 256)) ) (! (= ($shlBv8From256 src1@@15 src2@@7) (bvshl src1@@15 ((_ extract 7 0) src2@@7)))
 :qid |outputbpl.2604:25|
 :skolemid |54|
 :pattern ( ($shlBv8From256 src1@@15 src2@@7))
)))
(assert (forall ((src1@@16 (_ BitVec 8)) (src2@@8 (_ BitVec 256)) ) (! (= ($shrBv8From256 src1@@16 src2@@8) (bvlshr src1@@16 ((_ extract 7 0) src2@@8)))
 :qid |outputbpl.2619:25|
 :skolemid |55|
 :pattern ( ($shrBv8From256 src1@@16 src2@@8))
)))
(assert (forall ((src1@@17 (_ BitVec 16)) (src2@@9 (_ BitVec 32)) ) (! (= ($shlBv16From32 src1@@17 src2@@9) (bvshl src1@@17 ((_ extract 15 0) src2@@9)))
 :qid |outputbpl.2719:25|
 :skolemid |60|
 :pattern ( ($shlBv16From32 src1@@17 src2@@9))
)))
(assert (forall ((src1@@18 (_ BitVec 16)) (src2@@10 (_ BitVec 32)) ) (! (= ($shrBv16From32 src1@@18 src2@@10) (bvlshr src1@@18 ((_ extract 15 0) src2@@10)))
 :qid |outputbpl.2734:25|
 :skolemid |61|
 :pattern ( ($shrBv16From32 src1@@18 src2@@10))
)))
(assert (forall ((src1@@19 (_ BitVec 16)) (src2@@11 (_ BitVec 64)) ) (! (= ($shlBv16From64 src1@@19 src2@@11) (bvshl src1@@19 ((_ extract 15 0) src2@@11)))
 :qid |outputbpl.2760:25|
 :skolemid |62|
 :pattern ( ($shlBv16From64 src1@@19 src2@@11))
)))
(assert (forall ((src1@@20 (_ BitVec 16)) (src2@@12 (_ BitVec 64)) ) (! (= ($shrBv16From64 src1@@20 src2@@12) (bvlshr src1@@20 ((_ extract 15 0) src2@@12)))
 :qid |outputbpl.2775:25|
 :skolemid |63|
 :pattern ( ($shrBv16From64 src1@@20 src2@@12))
)))
(assert (forall ((src1@@21 (_ BitVec 16)) (src2@@13 (_ BitVec 128)) ) (! (= ($shlBv16From128 src1@@21 src2@@13) (bvshl src1@@21 ((_ extract 15 0) src2@@13)))
 :qid |outputbpl.2801:26|
 :skolemid |64|
 :pattern ( ($shlBv16From128 src1@@21 src2@@13))
)))
(assert (forall ((src1@@22 (_ BitVec 16)) (src2@@14 (_ BitVec 128)) ) (! (= ($shrBv16From128 src1@@22 src2@@14) (bvlshr src1@@22 ((_ extract 15 0) src2@@14)))
 :qid |outputbpl.2816:26|
 :skolemid |65|
 :pattern ( ($shrBv16From128 src1@@22 src2@@14))
)))
(assert (forall ((src1@@23 (_ BitVec 16)) (src2@@15 (_ BitVec 256)) ) (! (= ($shlBv16From256 src1@@23 src2@@15) (bvshl src1@@23 ((_ extract 15 0) src2@@15)))
 :qid |outputbpl.2842:26|
 :skolemid |66|
 :pattern ( ($shlBv16From256 src1@@23 src2@@15))
)))
(assert (forall ((src1@@24 (_ BitVec 16)) (src2@@16 (_ BitVec 256)) ) (! (= ($shrBv16From256 src1@@24 src2@@16) (bvlshr src1@@24 ((_ extract 15 0) src2@@16)))
 :qid |outputbpl.2857:26|
 :skolemid |67|
 :pattern ( ($shrBv16From256 src1@@24 src2@@16))
)))
(assert (forall ((src1@@25 (_ BitVec 32)) (src2@@17 (_ BitVec 64)) ) (! (= ($shlBv32From64 src1@@25 src2@@17) (bvshl src1@@25 ((_ extract 31 0) src2@@17)))
 :qid |outputbpl.2994:25|
 :skolemid |74|
 :pattern ( ($shlBv32From64 src1@@25 src2@@17))
)))
(assert (forall ((src1@@26 (_ BitVec 32)) (src2@@18 (_ BitVec 64)) ) (! (= ($shrBv32From64 src1@@26 src2@@18) (bvlshr src1@@26 ((_ extract 31 0) src2@@18)))
 :qid |outputbpl.3009:25|
 :skolemid |75|
 :pattern ( ($shrBv32From64 src1@@26 src2@@18))
)))
(assert (forall ((src1@@27 (_ BitVec 32)) (src2@@19 (_ BitVec 128)) ) (! (= ($shlBv32From128 src1@@27 src2@@19) (bvshl src1@@27 ((_ extract 31 0) src2@@19)))
 :qid |outputbpl.3035:26|
 :skolemid |76|
 :pattern ( ($shlBv32From128 src1@@27 src2@@19))
)))
(assert (forall ((src1@@28 (_ BitVec 32)) (src2@@20 (_ BitVec 128)) ) (! (= ($shrBv32From128 src1@@28 src2@@20) (bvlshr src1@@28 ((_ extract 31 0) src2@@20)))
 :qid |outputbpl.3050:26|
 :skolemid |77|
 :pattern ( ($shrBv32From128 src1@@28 src2@@20))
)))
(assert (forall ((src1@@29 (_ BitVec 32)) (src2@@21 (_ BitVec 256)) ) (! (= ($shlBv32From256 src1@@29 src2@@21) (bvshl src1@@29 ((_ extract 31 0) src2@@21)))
 :qid |outputbpl.3076:26|
 :skolemid |78|
 :pattern ( ($shlBv32From256 src1@@29 src2@@21))
)))
(assert (forall ((src1@@30 (_ BitVec 32)) (src2@@22 (_ BitVec 256)) ) (! (= ($shrBv32From256 src1@@30 src2@@22) (bvlshr src1@@30 ((_ extract 31 0) src2@@22)))
 :qid |outputbpl.3091:26|
 :skolemid |79|
 :pattern ( ($shrBv32From256 src1@@30 src2@@22))
)))
(assert (forall ((src1@@31 (_ BitVec 64)) (src2@@23 (_ BitVec 128)) ) (! (= ($shlBv64From128 src1@@31 src2@@23) (bvshl src1@@31 ((_ extract 63 0) src2@@23)))
 :qid |outputbpl.3275:26|
 :skolemid |90|
 :pattern ( ($shlBv64From128 src1@@31 src2@@23))
)))
(assert (forall ((src1@@32 (_ BitVec 64)) (src2@@24 (_ BitVec 128)) ) (! (= ($shrBv64From128 src1@@32 src2@@24) (bvlshr src1@@32 ((_ extract 63 0) src2@@24)))
 :qid |outputbpl.3290:26|
 :skolemid |91|
 :pattern ( ($shrBv64From128 src1@@32 src2@@24))
)))
(assert (forall ((src1@@33 (_ BitVec 64)) (src2@@25 (_ BitVec 256)) ) (! (= ($shlBv64From256 src1@@33 src2@@25) (bvshl src1@@33 ((_ extract 63 0) src2@@25)))
 :qid |outputbpl.3324:26|
 :skolemid |93|
 :pattern ( ($shlBv64From256 src1@@33 src2@@25))
)))
(assert (forall ((src1@@34 (_ BitVec 64)) (src2@@26 (_ BitVec 256)) ) (! (= ($shrBv64From256 src1@@34 src2@@26) (bvlshr src1@@34 ((_ extract 63 0) src2@@26)))
 :qid |outputbpl.3339:26|
 :skolemid |94|
 :pattern ( ($shrBv64From256 src1@@34 src2@@26))
)))
(assert (forall ((src1@@35 (_ BitVec 128)) (src2@@27 (_ BitVec 256)) ) (! (= ($shlBv128From256 src1@@35 src2@@27) (bvshl src1@@35 ((_ extract 127 0) src2@@27)))
 :qid |outputbpl.3550:27|
 :skolemid |105|
 :pattern ( ($shlBv128From256 src1@@35 src2@@27))
)))
(assert (forall ((src1@@36 (_ BitVec 128)) (src2@@28 (_ BitVec 256)) ) (! (= ($shrBv128From256 src1@@36 src2@@28) (bvlshr src1@@36 ((_ extract 127 0) src2@@28)))
 :qid |outputbpl.3565:27|
 :skolemid |106|
 :pattern ( ($shrBv128From256 src1@@36 src2@@28))
)))
(assert (forall ((t@@10 T@$TypeParamInfo) ) (!  (=> (and (|$IsPrefix'vec'u8''| ($TypeName t@@10) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 118) 1 101) 2 99) 3 116) 4 111) 5 114) 6 60) 7)) (|$IsSuffix'vec'u8''| ($TypeName t@@10) (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 62) 1))) (is-$TypeParamVector t@@10))
 :qid |outputbpl.4369:15|
 :skolemid |168|
 :pattern ( ($TypeName t@@10))
)))
(assert (forall ((t@@11 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamI16 t@@11) (|$IsEqual'vec'u8''| ($TypeName t@@11) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 105) 1 49) 2 54) 3)))
 :qid |outputbpl.4354:15|
 :skolemid |153|
 :pattern ( ($TypeName t@@11))
)))
(assert (forall ((t@@12 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamI32 t@@12) (|$IsEqual'vec'u8''| ($TypeName t@@12) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 105) 1 51) 2 50) 3)))
 :qid |outputbpl.4356:15|
 :skolemid |155|
 :pattern ( ($TypeName t@@12))
)))
(assert (forall ((t@@13 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamI64 t@@13) (|$IsEqual'vec'u8''| ($TypeName t@@13) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 105) 1 54) 2 52) 3)))
 :qid |outputbpl.4358:15|
 :skolemid |157|
 :pattern ( ($TypeName t@@13))
)))
(assert (forall ((t@@14 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@14) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 115) 1 105) 2 103) 3 110) 4 101) 5 114) 6)) (is-$TypeParamSigner t@@14))
 :qid |outputbpl.4367:15|
 :skolemid |166|
 :pattern ( ($TypeName t@@14))
)))
(assert (forall ((v@@4 T@Vec_11028) ) (! (= (|$IsValid'vec'u8''| v@@4)  (and (|$IsValid'u64'| (|l#Vec_11028| v@@4)) (forall ((i@@6 Int) ) (!  (=> (InRangeVec_19490 v@@4 i@@6) (|$IsValid'u8'| (|Select__T@[Int]Int_| (|v#Vec_11028| v@@4) i@@6)))
 :qid |outputbpl.3843:13|
 :skolemid |128|
))))
 :qid |outputbpl.3841:28|
 :skolemid |129|
 :pattern ( (|$IsValid'vec'u8''| v@@4))
)))
(assert (forall ((|l#0@@3| Bool) (i@@7 Int) ) (! (= (|Select__T@[Int]Bool_| (|lambda#4| |l#0@@3|) i@@7) |l#0@@3|)
 :qid |outputbpl.194:57|
 :skolemid |187|
 :pattern ( (|Select__T@[Int]Bool_| (|lambda#4| |l#0@@3|) i@@7))
)))
(assert (forall ((v@@5 Int) ) (! (= (|$IsValid'num'| v@@5) true)
 :qid |outputbpl.2065:24|
 :skolemid |35|
 :pattern ( (|$IsValid'num'| v@@5))
)))
(assert (forall ((t@@15 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamI8 t@@15) (|$IsEqual'vec'u8''| ($TypeName t@@15) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 105) 1 56) 2)))
 :qid |outputbpl.4352:15|
 :skolemid |151|
 :pattern ( ($TypeName t@@15))
)))
(assert (forall ((t@@16 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamU8 t@@16) (|$IsEqual'vec'u8''| ($TypeName t@@16) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 117) 1 56) 2)))
 :qid |outputbpl.4340:15|
 :skolemid |139|
 :pattern ( ($TypeName t@@16))
)))
(assert (forall ((src@@2 (_ BitVec 8)) ) (! (= ($castBv8to64 src@@2) (concat #x00000000000000 src@@2))
 :qid |outputbpl.3112:23|
 :skolemid |80|
 :pattern ( ($castBv8to64 src@@2))
)))
(assert (forall ((src@@3 (_ BitVec 64)) ) (! (= ($castBv64to256 src@@3) (concat #x000000000000000000000000000000000000000000000000 src@@3))
 :qid |outputbpl.3694:25|
 :skolemid |114|
 :pattern ( ($castBv64to256 src@@3))
)))
(assert (forall ((src@@4 (_ BitVec 8)) ) (! (= ($castBv8to256 src@@4) (concat #x00000000000000000000000000000000000000000000000000000000000000 src@@4))
 :qid |outputbpl.3586:24|
 :skolemid |107|
 :pattern ( ($castBv8to256 src@@4))
)))
(assert (forall ((n Int) (e@@0 Int) ) (! (= ($pow n e@@0) (ite  (and (not (= n 0)) (= e@@0 0)) 1 (ite (> e@@0 0) (* n ($pow n (- e@@0 1))) $undefined_int)))
 :qid |outputbpl.1000:15|
 :skolemid |20|
 :pattern ( ($pow n e@@0))
)))
(assert (forall ((t@@17 T@$TypeParamInfo) ) (!  (=> (|$IsPrefix'vec'u8''| ($TypeName t@@17) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2)) (is-$TypeParamVector t@@17))
 :qid |outputbpl.4371:15|
 :skolemid |170|
 :pattern ( ($TypeName t@@17))
)))
(assert (forall ((t@@18 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@18) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 105) 1 56) 2)) (is-$TypeParamI8 t@@18))
 :qid |outputbpl.4353:15|
 :skolemid |152|
 :pattern ( ($TypeName t@@18))
)))
(assert (forall ((t@@19 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@19) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 117) 1 56) 2)) (is-$TypeParamU8 t@@19))
 :qid |outputbpl.4341:15|
 :skolemid |140|
 :pattern ( ($TypeName t@@19))
)))
(assert (forall ((s |T@$bc_BasicCoin_Balance'#0'|) ) (! (= (|$IsValid'$bc_BasicCoin_Balance'#0''| s) (|$IsValid'$bc_BasicCoin_Coin'#0''| (|$coin#$bc_BasicCoin_Balance'#0'| s)))
 :qid |outputbpl.4565:46|
 :skolemid |171|
 :pattern ( (|$IsValid'$bc_BasicCoin_Balance'#0''| s))
)))
(assert (forall ((s@@0 |T@$bc_BasicCoin_Coin'#0'|) ) (! (= (|$IsValid'$bc_BasicCoin_Coin'#0''| s@@0) (|$IsValid'u64'| (|$value#$bc_BasicCoin_Coin'#0'| s@@0)))
 :qid |outputbpl.4580:43|
 :skolemid |172|
 :pattern ( (|$IsValid'$bc_BasicCoin_Coin'#0''| s@@0))
)))
(assert (forall ((src1@@37 (_ BitVec 16)) (src2@@29 (_ BitVec 8)) ) (! (= ($shlBv16From8 src1@@37 src2@@29) (bvshl src1@@37 (concat #x00 src2@@29)))
 :qid |outputbpl.2641:24|
 :skolemid |56|
 :pattern ( ($shlBv16From8 src1@@37 src2@@29))
)))
(assert (forall ((src1@@38 (_ BitVec 16)) (src2@@30 (_ BitVec 8)) ) (! (= ($shrBv16From8 src1@@38 src2@@30) (bvlshr src1@@38 (concat #x00 src2@@30)))
 :qid |outputbpl.2656:24|
 :skolemid |57|
 :pattern ( ($shrBv16From8 src1@@38 src2@@30))
)))
(assert (forall ((src1@@39 (_ BitVec 32)) (src2@@31 (_ BitVec 16)) ) (! (= ($shlBv32From16 src1@@39 src2@@31) (bvshl src1@@39 (concat #x0000 src2@@31)))
 :qid |outputbpl.2916:25|
 :skolemid |70|
 :pattern ( ($shlBv32From16 src1@@39 src2@@31))
)))
(assert (forall ((src1@@40 (_ BitVec 32)) (src2@@32 (_ BitVec 16)) ) (! (= ($shrBv32From16 src1@@40 src2@@32) (bvlshr src1@@40 (concat #x0000 src2@@32)))
 :qid |outputbpl.2931:25|
 :skolemid |71|
 :pattern ( ($shrBv32From16 src1@@40 src2@@32))
)))
(assert (forall ((src1@@41 (_ BitVec 32)) (src2@@33 (_ BitVec 8)) ) (! (= ($shlBv32From8 src1@@41 src2@@33) (bvshl src1@@41 (concat #x000000 src2@@33)))
 :qid |outputbpl.2879:24|
 :skolemid |68|
 :pattern ( ($shlBv32From8 src1@@41 src2@@33))
)))
(assert (forall ((src1@@42 (_ BitVec 32)) (src2@@34 (_ BitVec 8)) ) (! (= ($shrBv32From8 src1@@42 src2@@34) (bvlshr src1@@42 (concat #x000000 src2@@34)))
 :qid |outputbpl.2894:24|
 :skolemid |69|
 :pattern ( ($shrBv32From8 src1@@42 src2@@34))
)))
(assert (forall ((src1@@43 (_ BitVec 64)) (src2@@35 (_ BitVec 32)) ) (! (= ($shlBv64From32 src1@@43 src2@@35) (bvshl src1@@43 (concat #x00000000 src2@@35)))
 :qid |outputbpl.3192:25|
 :skolemid |85|
 :pattern ( ($shlBv64From32 src1@@43 src2@@35))
)))
(assert (forall ((src1@@44 (_ BitVec 64)) (src2@@36 (_ BitVec 32)) ) (! (= ($shrBv64From32 src1@@44 src2@@36) (bvlshr src1@@44 (concat #x00000000 src2@@36)))
 :qid |outputbpl.3207:25|
 :skolemid |86|
 :pattern ( ($shrBv64From32 src1@@44 src2@@36))
)))
(assert (forall ((src1@@45 (_ BitVec 64)) (src2@@37 (_ BitVec 16)) ) (! (= ($shlBv64From16 src1@@45 src2@@37) (bvshl src1@@45 (concat #x000000000000 src2@@37)))
 :qid |outputbpl.3155:25|
 :skolemid |83|
 :pattern ( ($shlBv64From16 src1@@45 src2@@37))
)))
(assert (forall ((src1@@46 (_ BitVec 64)) (src2@@38 (_ BitVec 16)) ) (! (= ($shrBv64From16 src1@@46 src2@@38) (bvlshr src1@@46 (concat #x000000000000 src2@@38)))
 :qid |outputbpl.3170:25|
 :skolemid |84|
 :pattern ( ($shrBv64From16 src1@@46 src2@@38))
)))
(assert (forall ((src1@@47 (_ BitVec 64)) (src2@@39 (_ BitVec 8)) ) (! (= ($shlBv64From8 src1@@47 src2@@39) (bvshl src1@@47 (concat #x00000000000000 src2@@39)))
 :qid |outputbpl.3118:24|
 :skolemid |81|
 :pattern ( ($shlBv64From8 src1@@47 src2@@39))
)))
(assert (forall ((src1@@48 (_ BitVec 64)) (src2@@40 (_ BitVec 8)) ) (! (= ($shrBv64From8 src1@@48 src2@@40) (bvlshr src1@@48 (concat #x00000000000000 src2@@40)))
 :qid |outputbpl.3133:24|
 :skolemid |82|
 :pattern ( ($shrBv64From8 src1@@48 src2@@40))
)))
(assert (forall ((src1@@49 (_ BitVec 128)) (src2@@41 (_ BitVec 64)) ) (! (= ($shlBv128From64 src1@@49 src2@@41) (bvshl src1@@49 (concat #x0000000000000000 src2@@41)))
 :qid |outputbpl.3472:26|
 :skolemid |101|
 :pattern ( ($shlBv128From64 src1@@49 src2@@41))
)))
(assert (forall ((src1@@50 (_ BitVec 128)) (src2@@42 (_ BitVec 64)) ) (! (= ($shrBv128From64 src1@@50 src2@@42) (bvlshr src1@@50 (concat #x0000000000000000 src2@@42)))
 :qid |outputbpl.3487:26|
 :skolemid |102|
 :pattern ( ($shrBv128From64 src1@@50 src2@@42))
)))
(assert (forall ((src1@@51 (_ BitVec 128)) (src2@@43 (_ BitVec 32)) ) (! (= ($shlBv128From32 src1@@51 src2@@43) (bvshl src1@@51 (concat #x000000000000000000000000 src2@@43)))
 :qid |outputbpl.3435:26|
 :skolemid |99|
 :pattern ( ($shlBv128From32 src1@@51 src2@@43))
)))
(assert (forall ((src1@@52 (_ BitVec 128)) (src2@@44 (_ BitVec 32)) ) (! (= ($shrBv128From32 src1@@52 src2@@44) (bvlshr src1@@52 (concat #x000000000000000000000000 src2@@44)))
 :qid |outputbpl.3450:26|
 :skolemid |100|
 :pattern ( ($shrBv128From32 src1@@52 src2@@44))
)))
(assert (forall ((src1@@53 (_ BitVec 128)) (src2@@45 (_ BitVec 16)) ) (! (= ($shlBv128From16 src1@@53 src2@@45) (bvshl src1@@53 (concat #x0000000000000000000000000000 src2@@45)))
 :qid |outputbpl.3398:26|
 :skolemid |97|
 :pattern ( ($shlBv128From16 src1@@53 src2@@45))
)))
(assert (forall ((src1@@54 (_ BitVec 128)) (src2@@46 (_ BitVec 16)) ) (! (= ($shrBv128From16 src1@@54 src2@@46) (bvlshr src1@@54 (concat #x0000000000000000000000000000 src2@@46)))
 :qid |outputbpl.3413:26|
 :skolemid |98|
 :pattern ( ($shrBv128From16 src1@@54 src2@@46))
)))
(assert (forall ((src1@@55 (_ BitVec 128)) (src2@@47 (_ BitVec 8)) ) (! (= ($shlBv128From8 src1@@55 src2@@47) (bvshl src1@@55 (concat #x000000000000000000000000000000 src2@@47)))
 :qid |outputbpl.3361:25|
 :skolemid |95|
 :pattern ( ($shlBv128From8 src1@@55 src2@@47))
)))
(assert (forall ((src1@@56 (_ BitVec 128)) (src2@@48 (_ BitVec 8)) ) (! (= ($shrBv128From8 src1@@56 src2@@48) (bvlshr src1@@56 (concat #x000000000000000000000000000000 src2@@48)))
 :qid |outputbpl.3376:25|
 :skolemid |96|
 :pattern ( ($shrBv128From8 src1@@56 src2@@48))
)))
(assert (forall ((src1@@57 (_ BitVec 256)) (src2@@49 (_ BitVec 128)) ) (! (= ($shlBv256From128 src1@@57 src2@@49) (bvshl src1@@57 (concat #x00000000000000000000000000000000 src2@@49)))
 :qid |outputbpl.3737:27|
 :skolemid |117|
 :pattern ( ($shlBv256From128 src1@@57 src2@@49))
)))
(assert (forall ((src1@@58 (_ BitVec 256)) (src2@@50 (_ BitVec 128)) ) (! (= ($shrBv256From128 src1@@58 src2@@50) (bvlshr src1@@58 (concat #x00000000000000000000000000000000 src2@@50)))
 :qid |outputbpl.3752:27|
 :skolemid |118|
 :pattern ( ($shrBv256From128 src1@@58 src2@@50))
)))
(assert (forall ((src1@@59 (_ BitVec 256)) (src2@@51 (_ BitVec 64)) ) (! (= ($shlBv256From64 src1@@59 src2@@51) (bvshl src1@@59 (concat #x000000000000000000000000000000000000000000000000 src2@@51)))
 :qid |outputbpl.3700:26|
 :skolemid |115|
 :pattern ( ($shlBv256From64 src1@@59 src2@@51))
)))
(assert (forall ((src1@@60 (_ BitVec 256)) (src2@@52 (_ BitVec 64)) ) (! (= ($shrBv256From64 src1@@60 src2@@52) (bvlshr src1@@60 (concat #x000000000000000000000000000000000000000000000000 src2@@52)))
 :qid |outputbpl.3715:26|
 :skolemid |116|
 :pattern ( ($shrBv256From64 src1@@60 src2@@52))
)))
(assert (forall ((src1@@61 (_ BitVec 256)) (src2@@53 (_ BitVec 32)) ) (! (= ($shlBv256From32 src1@@61 src2@@53) (bvshl src1@@61 (concat #x00000000000000000000000000000000000000000000000000000000 src2@@53)))
 :qid |outputbpl.3658:26|
 :skolemid |112|
 :pattern ( ($shlBv256From32 src1@@61 src2@@53))
)))
(assert (forall ((src1@@62 (_ BitVec 256)) (src2@@54 (_ BitVec 32)) ) (! (= ($shrBv256From32 src1@@62 src2@@54) (bvlshr src1@@62 (concat #x00000000000000000000000000000000000000000000000000000000 src2@@54)))
 :qid |outputbpl.3673:26|
 :skolemid |113|
 :pattern ( ($shrBv256From32 src1@@62 src2@@54))
)))
(assert (forall ((src1@@63 (_ BitVec 256)) (src2@@55 (_ BitVec 16)) ) (! (= ($shlBv256From16 src1@@63 src2@@55) (bvshl src1@@63 (concat #x000000000000000000000000000000000000000000000000000000000000 src2@@55)))
 :qid |outputbpl.3621:26|
 :skolemid |110|
 :pattern ( ($shlBv256From16 src1@@63 src2@@55))
)))
(assert (forall ((src1@@64 (_ BitVec 256)) (src2@@56 (_ BitVec 16)) ) (! (= ($shrBv256From16 src1@@64 src2@@56) (bvlshr src1@@64 (concat #x000000000000000000000000000000000000000000000000000000000000 src2@@56)))
 :qid |outputbpl.3636:26|
 :skolemid |111|
 :pattern ( ($shrBv256From16 src1@@64 src2@@56))
)))
(assert (forall ((src1@@65 (_ BitVec 256)) (src2@@57 (_ BitVec 8)) ) (! (= ($shlBv256From8 src1@@65 src2@@57) (bvshl src1@@65 (concat #x00000000000000000000000000000000000000000000000000000000000000 src2@@57)))
 :qid |outputbpl.3592:25|
 :skolemid |108|
 :pattern ( ($shlBv256From8 src1@@65 src2@@57))
)))
(assert (forall ((src1@@66 (_ BitVec 256)) (src2@@58 (_ BitVec 8)) ) (! (= ($shrBv256From8 src1@@66 src2@@58) (bvlshr src1@@66 (concat #x00000000000000000000000000000000000000000000000000000000000000 src2@@58)))
 :qid |outputbpl.3603:25|
 :skolemid |109|
 :pattern ( ($shrBv256From8 src1@@66 src2@@58))
)))
(assert (forall ((t@@20 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamU16 t@@20) (|$IsEqual'vec'u8''| ($TypeName t@@20) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 117) 1 49) 2 54) 3)))
 :qid |outputbpl.4342:15|
 :skolemid |141|
 :pattern ( ($TypeName t@@20))
)))
(assert (forall ((t@@21 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamU32 t@@21) (|$IsEqual'vec'u8''| ($TypeName t@@21) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 117) 1 51) 2 50) 3)))
 :qid |outputbpl.4344:15|
 :skolemid |143|
 :pattern ( ($TypeName t@@21))
)))
(assert (forall ((t@@22 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamU64 t@@22) (|$IsEqual'vec'u8''| ($TypeName t@@22) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 117) 1 54) 2 52) 3)))
 :qid |outputbpl.4346:15|
 :skolemid |145|
 :pattern ( ($TypeName t@@22))
)))
(assert (forall ((s@@1 T@$bc_ProphecyBenchmark3Levels2Fields_Node1) ) (! (= (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node1'| s@@1)  (and (and (and (and (and (and (and (|$IsValid'u64'| (|$v0#$bc_ProphecyBenchmark3Levels2Fields_Node1| s@@1)) (|$IsValid'u64'| (|$v1#$bc_ProphecyBenchmark3Levels2Fields_Node1| s@@1))) (|$IsValid'u64'| (|$v2#$bc_ProphecyBenchmark3Levels2Fields_Node1| s@@1))) (|$IsValid'u64'| (|$v3#$bc_ProphecyBenchmark3Levels2Fields_Node1| s@@1))) (|$IsValid'u64'| (|$v4#$bc_ProphecyBenchmark3Levels2Fields_Node1| s@@1))) (|$IsValid'u64'| (|$v5#$bc_ProphecyBenchmark3Levels2Fields_Node1| s@@1))) (|$IsValid'u64'| (|$v6#$bc_ProphecyBenchmark3Levels2Fields_Node1| s@@1))) (|$IsValid'u64'| (|$v7#$bc_ProphecyBenchmark3Levels2Fields_Node1| s@@1))))
 :qid |outputbpl.6065:62|
 :skolemid |180|
 :pattern ( (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node1'| s@@1))
)))
(assert (forall ((s@@2 T@$bc_ProphecyBenchmark3Levels2Fields_Node2) ) (! (= (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node2'| s@@2)  (and (and (and (and (and (and (and (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node1'| (|$v0#$bc_ProphecyBenchmark3Levels2Fields_Node2| s@@2)) (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node1'| (|$v1#$bc_ProphecyBenchmark3Levels2Fields_Node2| s@@2))) (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node1'| (|$v2#$bc_ProphecyBenchmark3Levels2Fields_Node2| s@@2))) (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node1'| (|$v3#$bc_ProphecyBenchmark3Levels2Fields_Node2| s@@2))) (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node1'| (|$v4#$bc_ProphecyBenchmark3Levels2Fields_Node2| s@@2))) (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node1'| (|$v5#$bc_ProphecyBenchmark3Levels2Fields_Node2| s@@2))) (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node1'| (|$v6#$bc_ProphecyBenchmark3Levels2Fields_Node2| s@@2))) (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node1'| (|$v7#$bc_ProphecyBenchmark3Levels2Fields_Node2| s@@2))))
 :qid |outputbpl.6107:62|
 :skolemid |181|
 :pattern ( (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node2'| s@@2))
)))
(assert (forall ((s@@3 T@$bc_ProphecyBenchmark3Levels2Fields_Node3) ) (! (= (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node3'| s@@3)  (and (and (and (and (and (and (and (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node2'| (|$v0#$bc_ProphecyBenchmark3Levels2Fields_Node3| s@@3)) (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node2'| (|$v1#$bc_ProphecyBenchmark3Levels2Fields_Node3| s@@3))) (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node2'| (|$v2#$bc_ProphecyBenchmark3Levels2Fields_Node3| s@@3))) (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node2'| (|$v3#$bc_ProphecyBenchmark3Levels2Fields_Node3| s@@3))) (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node2'| (|$v4#$bc_ProphecyBenchmark3Levels2Fields_Node3| s@@3))) (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node2'| (|$v5#$bc_ProphecyBenchmark3Levels2Fields_Node3| s@@3))) (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node2'| (|$v6#$bc_ProphecyBenchmark3Levels2Fields_Node3| s@@3))) (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node2'| (|$v7#$bc_ProphecyBenchmark3Levels2Fields_Node3| s@@3))))
 :qid |outputbpl.6149:62|
 :skolemid |182|
 :pattern ( (|$IsValid'$bc_ProphecyBenchmark3Levels2Fields_Node3'| s@@3))
)))
(assert (forall ((src@@5 (_ BitVec 8)) ) (! (= ($castBv8to8 src@@5) src@@5)
 :qid |outputbpl.2377:22|
 :skolemid |41|
 :pattern ( ($castBv8to8 src@@5))
)))
(assert (forall ((src@@6 (_ BitVec 64)) ) (! (= ($castBv64to64 src@@6) src@@6)
 :qid |outputbpl.3228:24|
 :skolemid |87|
 :pattern ( ($castBv64to64 src@@6))
)))
(assert (forall ((src@@7 (_ BitVec 256)) ) (! (= ($castBv256to256 src@@7) src@@7)
 :qid |outputbpl.3773:26|
 :skolemid |119|
 :pattern ( ($castBv256to256 src@@7))
)))
(assert (forall ((t@@23 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@23) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 117) 1 49) 2 50) 3 56) 4)) (is-$TypeParamU128 t@@23))
 :qid |outputbpl.4349:15|
 :skolemid |148|
 :pattern ( ($TypeName t@@23))
)))
(assert (forall ((src1@@67 (_ BitVec 8)) (src2@@59 (_ BitVec 8)) ) (! (= ($shlBv8From8 src1@@67 src2@@59) (bvshl src1@@67 src2@@59))
 :qid |outputbpl.2383:23|
 :skolemid |42|
 :pattern ( ($shlBv8From8 src1@@67 src2@@59))
)))
(assert (forall ((src1@@68 (_ BitVec 8)) (src2@@60 (_ BitVec 8)) ) (! (= ($shrBv8From8 src1@@68 src2@@60) (bvlshr src1@@68 src2@@60))
 :qid |outputbpl.2398:23|
 :skolemid |43|
 :pattern ( ($shrBv8From8 src1@@68 src2@@60))
)))
(assert (forall ((src1@@69 (_ BitVec 16)) (src2@@61 (_ BitVec 16)) ) (! (= ($shlBv16From16 src1@@69 src2@@61) (bvshl src1@@69 src2@@61))
 :qid |outputbpl.2678:25|
 :skolemid |58|
 :pattern ( ($shlBv16From16 src1@@69 src2@@61))
)))
(assert (forall ((src1@@70 (_ BitVec 16)) (src2@@62 (_ BitVec 16)) ) (! (= ($shrBv16From16 src1@@70 src2@@62) (bvlshr src1@@70 src2@@62))
 :qid |outputbpl.2693:25|
 :skolemid |59|
 :pattern ( ($shrBv16From16 src1@@70 src2@@62))
)))
(assert (forall ((src1@@71 (_ BitVec 32)) (src2@@63 (_ BitVec 32)) ) (! (= ($shlBv32From32 src1@@71 src2@@63) (bvshl src1@@71 src2@@63))
 :qid |outputbpl.2953:25|
 :skolemid |72|
 :pattern ( ($shlBv32From32 src1@@71 src2@@63))
)))
(assert (forall ((src1@@72 (_ BitVec 32)) (src2@@64 (_ BitVec 32)) ) (! (= ($shrBv32From32 src1@@72 src2@@64) (bvlshr src1@@72 src2@@64))
 :qid |outputbpl.2968:25|
 :skolemid |73|
 :pattern ( ($shrBv32From32 src1@@72 src2@@64))
)))
(assert (forall ((src1@@73 (_ BitVec 64)) (src2@@65 (_ BitVec 64)) ) (! (= ($shlBv64From64 src1@@73 src2@@65) (bvshl src1@@73 src2@@65))
 :qid |outputbpl.3234:25|
 :skolemid |88|
 :pattern ( ($shlBv64From64 src1@@73 src2@@65))
)))
(assert (forall ((src1@@74 (_ BitVec 64)) (src2@@66 (_ BitVec 64)) ) (! (= ($shrBv64From64 src1@@74 src2@@66) (bvlshr src1@@74 src2@@66))
 :qid |outputbpl.3249:25|
 :skolemid |89|
 :pattern ( ($shrBv64From64 src1@@74 src2@@66))
)))
(assert (forall ((src1@@75 (_ BitVec 128)) (src2@@67 (_ BitVec 128)) ) (! (= ($shlBv128From128 src1@@75 src2@@67) (bvshl src1@@75 src2@@67))
 :qid |outputbpl.3509:27|
 :skolemid |103|
 :pattern ( ($shlBv128From128 src1@@75 src2@@67))
)))
(assert (forall ((src1@@76 (_ BitVec 128)) (src2@@68 (_ BitVec 128)) ) (! (= ($shrBv128From128 src1@@76 src2@@68) (bvlshr src1@@76 src2@@68))
 :qid |outputbpl.3524:27|
 :skolemid |104|
 :pattern ( ($shrBv128From128 src1@@76 src2@@68))
)))
(assert (forall ((src1@@77 (_ BitVec 256)) (src2@@69 (_ BitVec 256)) ) (! (= ($shlBv256From256 src1@@77 src2@@69) (bvshl src1@@77 src2@@69))
 :qid |outputbpl.3779:27|
 :skolemid |120|
 :pattern ( ($shlBv256From256 src1@@77 src2@@69))
)))
(assert (forall ((src1@@78 (_ BitVec 256)) (src2@@70 (_ BitVec 256)) ) (! (= ($shrBv256From256 src1@@78 src2@@70) (bvlshr src1@@78 src2@@70))
 :qid |outputbpl.3794:27|
 :skolemid |121|
 :pattern ( ($shrBv256From256 src1@@78 src2@@70))
)))
(assert (forall ((k1@@0 T@Vec_11028) (k2@@0 T@Vec_11028) ) (!  (=> (|$IsEqual'vec'u8''| k1@@0 k2@@0) (= ($1_Signature_$ed25519_validate_pubkey k1@@0) ($1_Signature_$ed25519_validate_pubkey k2@@0)))
 :qid |outputbpl.4274:15|
 :skolemid |135|
 :pattern ( ($1_Signature_$ed25519_validate_pubkey k1@@0) ($1_Signature_$ed25519_validate_pubkey k2@@0))
)))
(assert (forall ((v@@6 (_ BitVec 8)) ) (! (= (|$IsValid'bv8'| v@@6)  (and (bvuge v@@6 #x00) (bvule v@@6 #xff)))
 :qid |outputbpl.1407:24|
 :skolemid |29|
 :pattern ( (|$IsValid'bv8'| v@@6))
)))
(assert (forall ((v@@7 (_ BitVec 64)) ) (! (= (|$IsValid'bv64'| v@@7)  (and (bvuge v@@7 #x0000000000000000) (bvule v@@7 #xffffffffffffffff)))
 :qid |outputbpl.1782:25|
 :skolemid |32|
 :pattern ( (|$IsValid'bv64'| v@@7))
)))
(assert (forall ((v@@8 (_ BitVec 16)) ) (! (= (|$IsValid'bv16'| v@@8)  (and (bvuge v@@8 #x0000) (bvule v@@8 #xffff)))
 :qid |outputbpl.1532:25|
 :skolemid |30|
 :pattern ( (|$IsValid'bv16'| v@@8))
)))
(assert (forall ((v@@9 (_ BitVec 256)) ) (! (= (|$IsValid'bv256'| v@@9)  (and (bvuge v@@9 #x0000000000000000000000000000000000000000000000000000000000000000) (bvule v@@9 #xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)))
 :qid |outputbpl.2032:26|
 :skolemid |34|
 :pattern ( (|$IsValid'bv256'| v@@9))
)))
(assert (forall ((v@@10 T@Vec_11028) (e@@1 Int) ) (! (let ((i@@8 (|$IndexOfVec'u8'| v@@10 e@@1)))
(ite  (not (exists ((i@@9 Int) ) (!  (and (and (|$IsValid'u64'| i@@9) (InRangeVec_19490 v@@10 i@@9)) (= (|Select__T@[Int]Int_| (|v#Vec_11028| v@@10) i@@9) e@@1))
 :qid |outputbpl.3848:13|
 :skolemid |130|
))) (= i@@8 (- 0 1))  (and (and (and (|$IsValid'u64'| i@@8) (InRangeVec_19490 v@@10 i@@8)) (= (|Select__T@[Int]Int_| (|v#Vec_11028| v@@10) i@@8) e@@1)) (forall ((j@@1 Int) ) (!  (=> (and (and (|$IsValid'u64'| j@@1) (>= j@@1 0)) (< j@@1 i@@8)) (not (= (|Select__T@[Int]Int_| (|v#Vec_11028| v@@10) j@@1) e@@1)))
 :qid |outputbpl.3856:17|
 :skolemid |131|
)))))
 :qid |outputbpl.3852:15|
 :skolemid |132|
 :pattern ( (|$IndexOfVec'u8'| v@@10 e@@1))
)))
(assert (forall ((t@@24 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@24) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 105) 1 49) 2 50) 3 56) 4)) (is-$TypeParamI128 t@@24))
 :qid |outputbpl.4361:15|
 :skolemid |160|
 :pattern ( ($TypeName t@@24))
)))
(assert (forall ((t@@25 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamBool t@@25) (|$IsEqual'vec'u8''| ($TypeName t@@25) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 98) 1 111) 2 111) 3 108) 4)))
 :qid |outputbpl.4338:15|
 :skolemid |137|
 :pattern ( ($TypeName t@@25))
)))
(assert (forall ((v@@11 (_ BitVec 128)) ) (! (= (|$IsValid'bv128'| v@@11)  (and (bvuge v@@11 #x00000000000000000000000000000000) (bvule v@@11 #xffffffffffffffffffffffffffffffff)))
 :qid |outputbpl.1907:26|
 :skolemid |33|
 :pattern ( (|$IsValid'bv128'| v@@11))
)))
(assert (forall ((v1@@0 T@Vec_11028) (v2@@0 T@Vec_11028) ) (! (= (|$IsEqual'vec'u8''| v1@@0 v2@@0) (|$IsEqual'vec'u8''| ($1_hash_sha2 v1@@0) ($1_hash_sha2 v2@@0)))
 :qid |outputbpl.4149:15|
 :skolemid |133|
 :pattern ( ($1_hash_sha2 v1@@0) ($1_hash_sha2 v2@@0))
)))
(assert (forall ((v1@@1 T@Vec_11028) (v2@@1 T@Vec_11028) ) (! (= (|$IsEqual'vec'u8''| v1@@1 v2@@1) (|$IsEqual'vec'u8''| ($1_hash_sha3 v1@@1) ($1_hash_sha3 v2@@1)))
 :qid |outputbpl.4165:15|
 :skolemid |134|
 :pattern ( ($1_hash_sha3 v1@@1) ($1_hash_sha3 v2@@1))
)))
(assert (forall ((t@@26 T@$TypeParamInfo) ) (!  (=> (is-$TypeParamStruct t@@26) (|$IsEqual'vec'u8''| ($TypeName t@@26) (let ((m2@@2 (|v#Vec_11028| (|s#$TypeParamStruct| t@@26))))
(let ((l2@@1 (|l#Vec_11028| (|s#$TypeParamStruct| t@@26))))
(let ((m1@@2 (|v#Vec_11028| (let ((m2@@3 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((l2@@2 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((m1@@3 (|v#Vec_11028| (let ((m2@@4 (|v#Vec_11028| (|m#$TypeParamStruct| t@@26))))
(let ((l2@@3 (|l#Vec_11028| (|m#$TypeParamStruct| t@@26))))
(let ((m1@@4 (|v#Vec_11028| (let ((m2@@5 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((l2@@4 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((m1@@5 (|v#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(let ((l1@@2 (|l#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@2 l2@@4) l1@@2 m1@@5 m2@@5 l1@@2 DefaultVecElem_19835) (+ l1@@2 l2@@4)))))))))
(let ((l1@@3 (|l#Vec_11028| (let ((m2@@5 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((l2@@4 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((m1@@5 (|v#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(let ((l1@@2 (|l#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@2 l2@@4) l1@@2 m1@@5 m2@@5 l1@@2 DefaultVecElem_19835) (+ l1@@2 l2@@4)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@3 l2@@3) l1@@3 m1@@4 m2@@4 l1@@3 DefaultVecElem_19835) (+ l1@@3 l2@@3)))))))))
(let ((l1@@4 (|l#Vec_11028| (let ((m2@@4 (|v#Vec_11028| (|m#$TypeParamStruct| t@@26))))
(let ((l2@@3 (|l#Vec_11028| (|m#$TypeParamStruct| t@@26))))
(let ((m1@@4 (|v#Vec_11028| (let ((m2@@5 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((l2@@4 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((m1@@5 (|v#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(let ((l1@@2 (|l#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@2 l2@@4) l1@@2 m1@@5 m2@@5 l1@@2 DefaultVecElem_19835) (+ l1@@2 l2@@4)))))))))
(let ((l1@@3 (|l#Vec_11028| (let ((m2@@5 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((l2@@4 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((m1@@5 (|v#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(let ((l1@@2 (|l#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@2 l2@@4) l1@@2 m1@@5 m2@@5 l1@@2 DefaultVecElem_19835) (+ l1@@2 l2@@4)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@3 l2@@3) l1@@3 m1@@4 m2@@4 l1@@3 DefaultVecElem_19835) (+ l1@@3 l2@@3)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@4 l2@@2) l1@@4 m1@@3 m2@@3 l1@@4 DefaultVecElem_19835) (+ l1@@4 l2@@2)))))))))
(let ((l1@@5 (|l#Vec_11028| (let ((m2@@3 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((l2@@2 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((m1@@3 (|v#Vec_11028| (let ((m2@@4 (|v#Vec_11028| (|m#$TypeParamStruct| t@@26))))
(let ((l2@@3 (|l#Vec_11028| (|m#$TypeParamStruct| t@@26))))
(let ((m1@@4 (|v#Vec_11028| (let ((m2@@5 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((l2@@4 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((m1@@5 (|v#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(let ((l1@@2 (|l#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@2 l2@@4) l1@@2 m1@@5 m2@@5 l1@@2 DefaultVecElem_19835) (+ l1@@2 l2@@4)))))))))
(let ((l1@@3 (|l#Vec_11028| (let ((m2@@5 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((l2@@4 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((m1@@5 (|v#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(let ((l1@@2 (|l#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@2 l2@@4) l1@@2 m1@@5 m2@@5 l1@@2 DefaultVecElem_19835) (+ l1@@2 l2@@4)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@3 l2@@3) l1@@3 m1@@4 m2@@4 l1@@3 DefaultVecElem_19835) (+ l1@@3 l2@@3)))))))))
(let ((l1@@4 (|l#Vec_11028| (let ((m2@@4 (|v#Vec_11028| (|m#$TypeParamStruct| t@@26))))
(let ((l2@@3 (|l#Vec_11028| (|m#$TypeParamStruct| t@@26))))
(let ((m1@@4 (|v#Vec_11028| (let ((m2@@5 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((l2@@4 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((m1@@5 (|v#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(let ((l1@@2 (|l#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@2 l2@@4) l1@@2 m1@@5 m2@@5 l1@@2 DefaultVecElem_19835) (+ l1@@2 l2@@4)))))))))
(let ((l1@@3 (|l#Vec_11028| (let ((m2@@5 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((l2@@4 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 58) 1 58) 2))))
(let ((m1@@5 (|v#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(let ((l1@@2 (|l#Vec_11028| (let ((m2@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((l2@@5 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 (|a#$TypeParamStruct| t@@26)) 1))))
(let ((m1@@6 (|v#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(let ((l1@@1 (|l#Vec_11028| (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 48) 1 120) 2))))
(Vec_11028 (|lambda#0| 0 (+ l1@@1 l2@@5) l1@@1 m1@@6 m2@@6 l1@@1 DefaultVecElem_19835) (+ l1@@1 l2@@5)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@2 l2@@4) l1@@2 m1@@5 m2@@5 l1@@2 DefaultVecElem_19835) (+ l1@@2 l2@@4)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@3 l2@@3) l1@@3 m1@@4 m2@@4 l1@@3 DefaultVecElem_19835) (+ l1@@3 l2@@3)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@4 l2@@2) l1@@4 m1@@3 m2@@3 l1@@4 DefaultVecElem_19835) (+ l1@@4 l2@@2)))))))))
(Vec_11028 (|lambda#0| 0 (+ l1@@5 l2@@1) l1@@5 m1@@2 m2@@2 l1@@5 DefaultVecElem_19835) (+ l1@@5 l2@@1))))))))
 :qid |outputbpl.4370:15|
 :skolemid |169|
 :pattern ( ($TypeName t@@26))
)))
(assert (forall ((t@@27 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@27) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 105) 1 49) 2 54) 3)) (is-$TypeParamI16 t@@27))
 :qid |outputbpl.4355:15|
 :skolemid |154|
 :pattern ( ($TypeName t@@27))
)))
(assert (forall ((t@@28 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@28) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 105) 1 51) 2 50) 3)) (is-$TypeParamI32 t@@28))
 :qid |outputbpl.4357:15|
 :skolemid |156|
 :pattern ( ($TypeName t@@28))
)))
(assert (forall ((t@@29 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@29) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 105) 1 54) 2 52) 3)) (is-$TypeParamI64 t@@29))
 :qid |outputbpl.4359:15|
 :skolemid |158|
 :pattern ( ($TypeName t@@29))
)))
(assert (forall ((v@@12 Int) ) (! (= (|$IsValid'u8'| v@@12)  (and (>= v@@12 $MIN_U8) (<= v@@12 $MAX_U8)))
 :qid |outputbpl.315:23|
 :skolemid |8|
 :pattern ( (|$IsValid'u8'| v@@12))
)))
(assert (forall ((v@@13 Int) ) (! (= (|$IsValid'u16'| v@@13)  (and (>= v@@13 $MIN_U16) (<= v@@13 $MAX_U16)))
 :qid |outputbpl.370:24|
 :skolemid |9|
 :pattern ( (|$IsValid'u16'| v@@13))
)))
(assert (forall ((v@@14 Int) ) (! (= (|$IsValid'u32'| v@@14)  (and (>= v@@14 $MIN_U32) (<= v@@14 $MAX_U32)))
 :qid |outputbpl.425:24|
 :skolemid |10|
 :pattern ( (|$IsValid'u32'| v@@14))
)))
(assert (forall ((v@@15 Int) ) (! (= (|$IsValid'u64'| v@@15)  (and (>= v@@15 $MIN_U64) (<= v@@15 $MAX_U64)))
 :qid |outputbpl.480:24|
 :skolemid |11|
 :pattern ( (|$IsValid'u64'| v@@15))
)))
(assert (forall ((v@@16 Int) ) (! (= (|$IsValid'u128'| v@@16)  (and (>= v@@16 $MIN_U128) (<= v@@16 $MAX_U128)))
 :qid |outputbpl.535:25|
 :skolemid |12|
 :pattern ( (|$IsValid'u128'| v@@16))
)))
(assert (forall ((v@@17 Int) ) (! (= (|$IsValid'u256'| v@@17)  (and (>= v@@17 $MIN_U256) (<= v@@17 $MAX_U256)))
 :qid |outputbpl.590:25|
 :skolemid |13|
 :pattern ( (|$IsValid'u256'| v@@17))
)))
(assert (forall ((v@@18 Int) ) (! (= (|$IsValid'i8'| v@@18)  (and (>= v@@18 $MIN_I8) (<= v@@18 $MAX_I8)))
 :qid |outputbpl.645:23|
 :skolemid |14|
 :pattern ( (|$IsValid'i8'| v@@18))
)))
(assert (forall ((v@@19 Int) ) (! (= (|$IsValid'i16'| v@@19)  (and (>= v@@19 $MIN_I16) (<= v@@19 $MAX_I16)))
 :qid |outputbpl.700:24|
 :skolemid |15|
 :pattern ( (|$IsValid'i16'| v@@19))
)))
(assert (forall ((v@@20 Int) ) (! (= (|$IsValid'i32'| v@@20)  (and (>= v@@20 $MIN_I32) (<= v@@20 $MAX_I32)))
 :qid |outputbpl.755:24|
 :skolemid |16|
 :pattern ( (|$IsValid'i32'| v@@20))
)))
(assert (forall ((v@@21 Int) ) (! (= (|$IsValid'i64'| v@@21)  (and (>= v@@21 $MIN_I64) (<= v@@21 $MAX_I64)))
 :qid |outputbpl.810:24|
 :skolemid |17|
 :pattern ( (|$IsValid'i64'| v@@21))
)))
(assert (forall ((v@@22 Int) ) (! (= (|$IsValid'i128'| v@@22)  (and (>= v@@22 $MIN_I128) (<= v@@22 $MAX_I128)))
 :qid |outputbpl.865:25|
 :skolemid |18|
 :pattern ( (|$IsValid'i128'| v@@22))
)))
(assert (forall ((v@@23 Int) ) (! (= (|$IsValid'i256'| v@@23)  (and (>= v@@23 $MIN_I256) (<= v@@23 $MAX_I256)))
 :qid |outputbpl.920:25|
 :skolemid |19|
 :pattern ( (|$IsValid'i256'| v@@23))
)))
(assert (forall ((v@@24 T@Vec_11028) (i@@10 Int) ) (! (= (InRangeVec_19490 v@@24 i@@10)  (and (>= i@@10 0) (< i@@10 (|l#Vec_11028| v@@24))))
 :qid |outputbpl.123:24|
 :skolemid |3|
 :pattern ( (InRangeVec_19490 v@@24 i@@10))
)))
(assert (forall ((t@@30 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@30) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 117) 1 50) 2 53) 3 54) 4)) (is-$TypeParamU256 t@@30))
 :qid |outputbpl.4351:15|
 :skolemid |150|
 :pattern ( ($TypeName t@@30))
)))
(assert (forall ((r T@$Range) (i@@11 Int) ) (! (= ($InRange r i@@11)  (and (<= (|lb#$Range| r) i@@11) (< i@@11 (|ub#$Range| r))))
 :qid |outputbpl.2079:19|
 :skolemid |37|
 :pattern ( ($InRange r i@@11))
)))
(assert (forall ((t@@31 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@31) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 105) 1 50) 2 53) 3 54) 4)) (is-$TypeParamI256 t@@31))
 :qid |outputbpl.4363:15|
 :skolemid |162|
 :pattern ( ($TypeName t@@31))
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
(assert (forall ((t@@32 T@$TypeParamInfo) ) (!  (=> (|$IsEqual'vec'u8''| ($TypeName t@@32) (Vec_11028 (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (|Store__T@[Int]Int_| (MapConstVec_19835 DefaultVecElem_19835) 0 97) 1 100) 2 100) 3 114) 4 101) 5 115) 6 115) 7)) (is-$TypeParamAddress t@@32))
 :qid |outputbpl.4365:15|
 :skolemid |164|
 :pattern ( ($TypeName t@@32))
)))
(assert (= $MAX_U256 115792089237316195423570985008687907853269984665640564039457584007913129639935))
(assert (= $MAX_I256 57896044618658097711785492504343953926634992332820282019728792003956564819967))
(assert (= $EXEC_FAILURE_CODE (- 0 1)))
(assert (= $MIN_I8 (- 0 128)))
(assert (= $MIN_I64 (- 0 9223372036854775808)))
(assert (= $MIN_I16 (- 0 32768)))
(assert (= $MIN_I256 (- 0 57896044618658097711785492504343953926634992332820282019728792003956564819968)))
; Valid

