import Model.Prim.Slice64
import Model.Field.NativeKernel

namespace LeanVmXmss.Native.Kernels

@[inline] def gf64Reduce (lo hi : UInt64) : UInt64 :=
  let spill := (hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60)
  let v := hi ^^^ spill
  lo ^^^ v ^^^ (v <<< 1) ^^^ (v <<< 3) ^^^ (v <<< 4)

@[noinline, export ln_xmss_field_clmul_lo]
def fieldClmulLo (a b : UInt64) : UInt64 :=
  Model.Prim.clmul64 a b

@[noinline, export ln_xmss_field_clmul_hi]
def fieldClmulHi (a b : UInt64) : UInt64 :=
  Model.Prim.clmul64Hi a b

@[noinline, export ln_xmss_field_mul64]
def fieldMul64 (a b : UInt64) : UInt64 :=
  gf64Reduce (Model.Prim.clmul64 a b) (Model.Prim.clmul64Hi a b)

@[noinline, export ln_xmss_field_sq64]
def fieldSq64 (a : UInt64) : UInt64 :=
  fieldMul64 a a

@[noinline, export ln_xmss_field_gf2_affine64]
def fieldGf2Affine64 (x m : UInt64) : UInt64 :=
  Model.Prim.gf2Affine64 x m

@[noinline, export ln_xmss_field_ternary64]
def fieldTernary64 (a b c : UInt64) (imm8 : UInt8) : UInt64 :=
  Model.Prim.ternaryLogic64 a b c imm8

@[noinline, export ln_xmss_field_ext_c0]
def fieldExtMulC0 (a0 a1 a2 b0 b1 b2 : UInt64) : UInt64 :=
  let p0 := fieldMul64 a0 b0
  let p1 := fieldMul64 a1 b1
  let p2 := fieldMul64 a2 b2
  let e3 := fieldMul64 (a1 ^^^ a2) (b1 ^^^ b2) ^^^ p1 ^^^ p2
  p0 ^^^ e3

@[noinline, export ln_xmss_field_ext_c1]
def fieldExtMulC1 (a0 a1 a2 b0 b1 b2 : UInt64) : UInt64 :=
  let p0 := fieldMul64 a0 b0
  let p1 := fieldMul64 a1 b1
  let p2 := fieldMul64 a2 b2
  let e1 := fieldMul64 (a0 ^^^ a1) (b0 ^^^ b1) ^^^ p0 ^^^ p1
  let e3 := fieldMul64 (a1 ^^^ a2) (b1 ^^^ b2) ^^^ p1 ^^^ p2
  e1 ^^^ e3 ^^^ p2

@[noinline, export ln_xmss_field_ext_c2]
def fieldExtMulC2 (a0 a1 a2 b0 b1 b2 : UInt64) : UInt64 :=
  let p0 := fieldMul64 a0 b0
  let p1 := fieldMul64 a1 b1
  let p2 := fieldMul64 a2 b2
  let e2 := fieldMul64 (a0 ^^^ a2) (b0 ^^^ b2) ^^^ p0 ^^^ p2 ^^^ p1
  e2 ^^^ p2

end LeanVmXmss.Native.Kernels
