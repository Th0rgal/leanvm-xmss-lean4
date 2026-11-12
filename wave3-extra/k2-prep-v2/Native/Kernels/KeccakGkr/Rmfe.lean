import Native.Kernels.KeccakGkr.Support

namespace LeanVmXmss.Native.Kernels.KeccakGkr

set_option compiler.ignoreBorrowAnnotation true

@[inline] def packMtx00 : UInt64 := 0x32d242327de8f701
@[inline] def packMtx01 : UInt64 := 0x419f4afa667dd413
@[inline] def packMtx02 : UInt64 := 0x009f8abaa6621e36
@[inline] def packMtx03 : UInt64 := 0x0000000000000000
@[inline] def packMtx10 : UInt64 := 0x593f2aaf1bcfc200
@[inline] def packMtx11 : UInt64 := 0x9271597f9b3fe260
@[inline] def packMtx12 : UInt64 := 0x80302866553424ad
@[inline] def packMtx13 : UInt64 := 0x0000000000000000

@[inline] def unpackMtx00 : UInt64 := 0x1f2197b9a7e9ff01
@[inline] def unpackMtx01 : UInt64 := 0xbbcdcb5cd374ff00
@[inline] def unpackMtx02 : UInt64 := 0x42c7e52ee93aff00
@[inline] def unpackMtx03 : UInt64 := 0x9aae7297749dff00
@[inline] def unpackMtx04 : UInt64 := 0x8f90b9cb3a4eff00
@[inline] def unpackMtx05 : UInt64 := 0x5d665c651d277f00
@[inline] def unpackMtx10 : UInt64 := 0x00d09fa1509fa190
@[inline] def unpackMtx11 : UInt64 := 0x008a0c1537256ee6
@[inline] def unpackMtx12 : UInt64 := 0x00fbadf73ed47c63
@[inline] def unpackMtx13 : UInt64 := 0x0064b8c94b8d9657
@[inline] def unpackMtx14 : UInt64 := 0x00684fd0a8cf5048
@[inline] def unpackMtx15 : UInt64 := 0x4045060a1b123773

@[inline]
def rmfeEmbedU16 (bits16 : UInt64) : UInt64 :=
  let lo := bits16 &&& 0xff
  let hi := (bits16 >>> 8) &&& 0xff
  let b0 := gf2Affine64 lo packMtx00 ^^^ gf2Affine64 hi packMtx10
  let b1 := gf2Affine64 lo packMtx01 ^^^ gf2Affine64 hi packMtx11
  let b2 := gf2Affine64 lo packMtx02 ^^^ gf2Affine64 hi packMtx12
  let b3 := gf2Affine64 lo packMtx03 ^^^ gf2Affine64 hi packMtx13
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)

@[inline]
def rmfeProjectU64 (prod : UInt64) : UInt64 :=
  let p0 := (prod >>> 0) &&& 0xff
  let p1 := (prod >>> 8) &&& 0xff
  let p2 := (prod >>> 16) &&& 0xff
  let p3 := (prod >>> 24) &&& 0xff
  let p4 := (prod >>> 32) &&& 0xff
  let p5 := (prod >>> 40) &&& 0xff
  let lo :=
    gf2Affine64 p0 unpackMtx00 ^^^ gf2Affine64 p1 unpackMtx01 ^^^
    gf2Affine64 p2 unpackMtx02 ^^^ gf2Affine64 p3 unpackMtx03 ^^^
    gf2Affine64 p4 unpackMtx04 ^^^ gf2Affine64 p5 unpackMtx05
  let hi :=
    gf2Affine64 p0 unpackMtx10 ^^^ gf2Affine64 p1 unpackMtx11 ^^^
    gf2Affine64 p2 unpackMtx12 ^^^ gf2Affine64 p3 unpackMtx13 ^^^
    gf2Affine64 p4 unpackMtx14 ^^^ gf2Affine64 p5 unpackMtx15
  lo ||| (hi <<< 8)

@[noinline, export lean_xmss_rmfe_pack_batch]
def rmfePackBatch (inp : ByteArray) (n : USize) : ByteArray :=
  let cap := n.toNat * 4
  Nat.rec (motive := fun _ => ByteArray) (ByteArray.emptyWithCapacity cap)
    (fun i prev =>
      let bits := readU16LE inp ((USize.ofNat i) <<< 1)
      pushU32LE prev (rmfeEmbedU16 bits))
    n.toNat

@[noinline, export lean_xmss_rmfe_unpack_batch]
def rmfeUnpackBatch (inp : ByteArray) (n : USize) : ByteArray :=
  let cap := n.toNat * 2
  Nat.rec (motive := fun _ => ByteArray) (ByteArray.emptyWithCapacity cap)
    (fun i prev =>
      let prod := readWordAt inp (USize.ofNat i)
      pushU16LE prev (rmfeProjectU64 prod))
    n.toNat

end LeanVmXmss.Native.Kernels.KeccakGkr
