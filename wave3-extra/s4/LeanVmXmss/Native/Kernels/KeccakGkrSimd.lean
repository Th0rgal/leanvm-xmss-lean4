import Native.Kernels.FieldSimd

namespace LeanVmXmss.Native.Kernels

@[inline] def rotl64 (x : UInt64) (r : UInt64) : UInt64 :=
  let s := r &&& 63
  if decide (s = 0) then x else (x <<< s) ||| (x >>> (64 - s))

@[noinline, export ln_xmss_keccak_chi_lane]
def keccakChiLane (a0 a1 a2 : UInt64) : UInt64 :=
  Model.Prim.ternaryLogic64 a0 a1 a2 0xd2

@[noinline, export ln_xmss_keccak_xor5_lane]
def keccakXor5Lane (a0 a1 a2 a3 a4 : UInt64) : UInt64 :=
  let t := Model.Prim.ternaryLogic64 a0 a1 a2 0x96
  Model.Prim.ternaryLogic64 t a3 a4 0x96

@[noinline, export ln_xmss_keccak_theta_d]
def keccakThetaD (cPrev cNext : UInt64) : UInt64 :=
  cPrev ^^^ rotl64 cNext 1

@[noinline, export ln_xmss_keccak_gkr_and_eval_c0]
def keccakGkrAndEvalC0 (x0 x1 x2 y0 y1 y2 : UInt64) : UInt64 :=
  fieldExtMulC0 x0 x1 x2 y0 y1 y2

end LeanVmXmss.Native.Kernels
