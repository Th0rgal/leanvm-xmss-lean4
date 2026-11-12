import Native.Kernels.FieldSimd

namespace LeanVmXmss.Native.Kernels

@[noinline, export ln_xmss_ntt_butterfly_u]
def nttButterflyU (u v twiddle : UInt64) : UInt64 :=
  u ^^^ fieldMul64 v twiddle

@[noinline, export ln_xmss_ntt_butterfly_v]
def nttButterflyV (u v twiddle : UInt64) : UInt64 :=
  let u1 := u ^^^ fieldMul64 v twiddle
  u1 ^^^ v

@[noinline, export ln_xmss_merkle_xor_mix]
def merkleXorMix (a b c : UInt64) : UInt64 :=
  Model.Prim.ternaryLogic64 a b c 0x96

@[noinline, export ln_xmss_whir_fold_c0]
def whirFoldC0 (e00 e01 e02 e10 e11 e12 w0 w1 w2 : UInt64) : UInt64 :=
  let d0 := e00 ^^^ e10
  let d1 := e01 ^^^ e11
  let d2 := e02 ^^^ e12
  e00 ^^^ fieldExtMulC0 d0 d1 d2 w0 w1 w2

end LeanVmXmss.Native.Kernels
