import Tests.Hub.ShardAHw
import Tests.Field.NativeRefinement

theorem shardAMulHw_eq_nativeMul (a b : UInt64) :
    shardAMulHw a b = LeanVmXmss.Model.Field.nativeMul a b := by
  simp only [shardAMulHw, shardAReduceHw, LeanVmXmss.Model.Field.nativeMul,
    LeanVmXmss.Model.Field.nativeReduce, clmul64_eq_nativeClmulLo, clmul64Hi_eq_nativeClmulHi]

theorem shardAClmulLoHw_eq_nativeClmulLo (a b : UInt64) :
    shardAClmulLoHw a b = LeanVmXmss.Model.Field.nativeClmulLo a b :=
  clmul64_eq_nativeClmulLo a b

theorem shardAClmulHiHw_eq_nativeClmulHi (a b : UInt64) :
    shardAClmulHiHw a b = LeanVmXmss.Model.Field.nativeClmulHi a b :=
  clmul64Hi_eq_nativeClmulHi a b

theorem shardASquareHw_eq_nativeSquare (a : UInt64) :
    shardASquareHw a = LeanVmXmss.Model.Field.nativeSquare a := by
  simp only [shardASquareHw, LeanVmXmss.Model.Field.nativeSquare, shardAMulHw_eq_nativeMul]

theorem shardAKaratsuba0Hw_eq_nativeKaratsuba0 (a0 a1 a2 b0 b1 b2 : UInt64) :
    shardAKaratsuba0Hw a0 a1 a2 b0 b1 b2 =
      LeanVmXmss.Model.Field.nativeKaratsuba0 a0 a1 a2 b0 b1 b2 := by
  simp only [shardAKaratsuba0Hw, LeanVmXmss.Model.Field.nativeKaratsuba0, shardAMulHw_eq_nativeMul]

theorem shardAKaratsuba1Hw_eq_nativeKaratsuba1 (a0 a1 a2 b0 b1 b2 : UInt64) :
    shardAKaratsuba1Hw a0 a1 a2 b0 b1 b2 =
      LeanVmXmss.Model.Field.nativeKaratsuba1 a0 a1 a2 b0 b1 b2 := by
  simp only [shardAKaratsuba1Hw, LeanVmXmss.Model.Field.nativeKaratsuba1, shardAMulHw_eq_nativeMul]

theorem shardAKaratsuba2Hw_eq_nativeKaratsuba2 (a0 a1 a2 b0 b1 b2 : UInt64) :
    shardAKaratsuba2Hw a0 a1 a2 b0 b1 b2 =
      LeanVmXmss.Model.Field.nativeKaratsuba2 a0 a1 a2 b0 b1 b2 := by
  simp only [shardAKaratsuba2Hw, LeanVmXmss.Model.Field.nativeKaratsuba2, shardAMulHw_eq_nativeMul]
