import Native.Kernels.KeccakGkr.Support

namespace LeanVmXmss.Native.Kernels.KeccakGkr

set_option compiler.ignoreBorrowAnnotation true

@[inline]
def gatherColumnWord (inp : ByteArray) (blockBase col : USize) : UInt64 :=
  let b := blockBase + col
  (byteAt inp b).toUInt64 |||
  ((byteAt inp (b + 8)).toUInt64 <<< 8) |||
  ((byteAt inp (b + 16)).toUInt64 <<< 16) |||
  ((byteAt inp (b + 24)).toUInt64 <<< 24) |||
  ((byteAt inp (b + 32)).toUInt64 <<< 32) |||
  ((byteAt inp (b + 40)).toUInt64 <<< 40) |||
  ((byteAt inp (b + 48)).toUInt64 <<< 48) |||
  ((byteAt inp (b + 56)).toUInt64 <<< 56)

@[inline]
def transposeBlock64Bytes (inp : ByteArray) (blockIdx : USize) (acc : ByteArray) : ByteArray :=
  let base := blockIdx <<< 6
  let a0 := pushU64LE acc (transpose8x8Bits (gatherColumnWord inp base 0))
  let a1 := pushU64LE a0 (transpose8x8Bits (gatherColumnWord inp base 1))
  let a2 := pushU64LE a1 (transpose8x8Bits (gatherColumnWord inp base 2))
  let a3 := pushU64LE a2 (transpose8x8Bits (gatherColumnWord inp base 3))
  let a4 := pushU64LE a3 (transpose8x8Bits (gatherColumnWord inp base 4))
  let a5 := pushU64LE a4 (transpose8x8Bits (gatherColumnWord inp base 5))
  let a6 := pushU64LE a5 (transpose8x8Bits (gatherColumnWord inp base 6))
  pushU64LE a6 (transpose8x8Bits (gatherColumnWord inp base 7))

@[noinline, export lean_xmss_bit_transpose_64x64]
def bitTranspose64x64 (inp : ByteArray) (nBlocks : USize) : ByteArray :=
  let cap := nBlocks.toNat * 64
  Nat.rec (motive := fun _ => ByteArray) (ByteArray.emptyWithCapacity cap)
    (fun idx prev => transposeBlock64Bytes inp (USize.ofNat idx) prev)
    nBlocks.toNat

end LeanVmXmss.Native.Kernels.KeccakGkr
