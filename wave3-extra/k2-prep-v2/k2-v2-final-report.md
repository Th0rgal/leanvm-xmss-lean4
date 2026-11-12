All standalone pure-Lean K2 Umbrella Kernel Island modules (`LeanVmXmss/Native/Kernels/KeccakGkr.lean` and submodules) and the strict audit/differential/benchmark suite (`Tests/Unit/NativeKeccakGkrKernelTest.lean`) are implemented, verified, compiled via `lean-native`, and saved with `manifest.json` (`sha256: ca62a30d6ef3c87a1897bf801e0f605d7916697b8aa5f342edd9af9f0dd784cc`) under `/var/lib/orb-node/work/caches/xmss-hub-v3/wave3/k2-prep/`.

### 1. Plain UTF-8 File Contents

#### `LeanVmXmss/Native/Kernels/KeccakGkr.lean` (`sha256: 394f1401f4048a96c029d12e0fdce5172c738ec2c3694c8ad7e63b83286411f1`)
```lean
import Native.Kernels.KeccakGkr.Support
import Native.Kernels.KeccakGkr.Transpose
import Native.Kernels.KeccakGkr.Chi
import Native.Kernels.KeccakGkr.Planes
import Native.Kernels.KeccakGkr.Rmfe
import Native.Kernels.KeccakGkr.Fold
```

#### `LeanVmXmss/Native/Kernels/KeccakGkr/Support.lean` (`sha256: b0b2d2547e8e1672a4fb005c6d7c725b556e8ecdb6eb32296251284336fafab8`)
```lean
namespace LeanVmXmss.Native.Kernels.KeccakGkr

set_option compiler.ignoreBorrowAnnotation true

@[inline]
def byteAt (b : ByteArray) (i : USize) : UInt8 :=
  if h : i < b.usize then
    b.uget i (by
      rw [USize.lt_iff_toNat_lt] at h
      exact Nat.lt_of_lt_of_le h (Nat.mod_le b.size USize.size))
  else 0

@[inline]
def readU16LE (b : ByteArray) (byteOff : USize) : UInt64 :=
  (byteAt b byteOff).toUInt64 |||
  ((byteAt b (byteOff + 1)).toUInt64 <<< 8)

@[inline]
def readU32LE (b : ByteArray) (byteOff : USize) : UInt64 :=
  (byteAt b byteOff).toUInt64 |||
  ((byteAt b (byteOff + 1)).toUInt64 <<< 8) |||
  ((byteAt b (byteOff + 2)).toUInt64 <<< 16) |||
  ((byteAt b (byteOff + 3)).toUInt64 <<< 24)

@[inline]
def readU64LE (b : ByteArray) (byteOff : USize) : UInt64 :=
  (byteAt b byteOff).toUInt64 |||
  ((byteAt b (byteOff + 1)).toUInt64 <<< 8) |||
  ((byteAt b (byteOff + 2)).toUInt64 <<< 16) |||
  ((byteAt b (byteOff + 3)).toUInt64 <<< 24) |||
  ((byteAt b (byteOff + 4)).toUInt64 <<< 32) |||
  ((byteAt b (byteOff + 5)).toUInt64 <<< 40) |||
  ((byteAt b (byteOff + 6)).toUInt64 <<< 48) |||
  ((byteAt b (byteOff + 7)).toUInt64 <<< 56)

@[inline]
def readWordAt (b : ByteArray) (wordIdx : USize) : UInt64 :=
  readU64LE b (wordIdx <<< 3)

@[inline]
def pushU16LE (b : ByteArray) (w : UInt64) : ByteArray :=
  let b0 := b.push w.toUInt8
  b0.push (w >>> 8).toUInt8

@[inline]
def pushU32LE (b : ByteArray) (w : UInt64) : ByteArray :=
  let b0 := b.push w.toUInt8
  let b1 := b0.push (w >>> 8).toUInt8
  let b2 := b1.push (w >>> 16).toUInt8
  b2.push (w >>> 24).toUInt8

@[inline]
def pushU64LE (b : ByteArray) (w : UInt64) : ByteArray :=
  let b0 := b.push w.toUInt8
  let b1 := b0.push (w >>> 8).toUInt8
  let b2 := b1.push (w >>> 16).toUInt8
  let b3 := b2.push (w >>> 24).toUInt8
  let b4 := b3.push (w >>> 32).toUInt8
  let b5 := b4.push (w >>> 40).toUInt8
  let b6 := b5.push (w >>> 48).toUInt8
  b6.push (w >>> 56).toUInt8

@[inline]
def ternaryLogic64 (a b c imm8 : UInt64) : UInt64 :=
  let z : UInt64 := 0
  let m0 : UInt64 := z - ((imm8 >>> 0) &&& 1)
  let m1 : UInt64 := z - ((imm8 >>> 1) &&& 1)
  let m2 : UInt64 := z - ((imm8 >>> 2) &&& 1)
  let m3 : UInt64 := z - ((imm8 >>> 3) &&& 1)
  let m4 : UInt64 := z - ((imm8 >>> 4) &&& 1)
  let m5 : UInt64 := z - ((imm8 >>> 5) &&& 1)
  let m6 : UInt64 := z - ((imm8 >>> 6) &&& 1)
  let m7 : UInt64 := z - ((imm8 >>> 7) &&& 1)
  let na := ~~~a
  let nb := ~~~b
  let nc := ~~~c
  ((na &&& nb &&& nc) &&& m0) |||
  ((na &&& nb &&& c) &&& m1) |||
  ((na &&& b &&& nc) &&& m2) |||
  ((na &&& b &&& c) &&& m3) |||
  ((a &&& nb &&& nc) &&& m4) |||
  ((a &&& nb &&& c) &&& m5) |||
  ((a &&& b &&& nc) &&& m6) |||
  ((a &&& b &&& c) &&& m7)

@[inline]
def chiWordD2 (a b c : UInt64) : UInt64 :=
  ternaryLogic64 a b c 0xD2

@[inline]
def gf2Parity8 (v : UInt64) : UInt64 :=
  let p0 := v &&& 0xff
  let p1 := p0 ^^^ (p0 >>> 4)
  let p2 := p1 ^^^ (p1 >>> 2)
  let p3 := p2 ^^^ (p2 >>> 1)
  p3 &&& 1

@[inline]
def gf2Affine64 (x m : UInt64) : UInt64 :=
  let xb := x &&& 0xff
  (gf2Parity8 ((m >>> 0) &&& xb) <<< 0) |||
  (gf2Parity8 ((m >>> 8) &&& xb) <<< 1) |||
  (gf2Parity8 ((m >>> 16) &&& xb) <<< 2) |||
  (gf2Parity8 ((m >>> 24) &&& xb) <<< 3) |||
  (gf2Parity8 ((m >>> 32) &&& xb) <<< 4) |||
  (gf2Parity8 ((m >>> 40) &&& xb) <<< 5) |||
  (gf2Parity8 ((m >>> 48) &&& xb) <<< 6) |||
  (gf2Parity8 ((m >>> 56) &&& xb) <<< 7)

@[inline]
def selectBit (a b i : UInt64) : UInt64 :=
  a &&& (0 - ((b >>> i) &&& 1))

@[inline]
def clmulByte (a b : UInt64) : UInt64 :=
  selectBit a b 0 ^^^ selectBit (a <<< 1) b 1 ^^^
  selectBit (a <<< 2) b 2 ^^^ selectBit (a <<< 3) b 3 ^^^
  selectBit (a <<< 4) b 4 ^^^ selectBit (a <<< 5) b 5 ^^^
  selectBit (a <<< 6) b 6 ^^^ selectBit (a <<< 7) b 7

@[inline]
def clmulLo (a b : UInt64) : UInt64 :=
  clmulByte a b ^^^ (clmulByte a (b >>> 8) <<< 8) ^^^
  (clmulByte a (b >>> 16) <<< 16) ^^^ (clmulByte a (b >>> 24) <<< 24) ^^^
  (clmulByte a (b >>> 32) <<< 32) ^^^ (clmulByte a (b >>> 40) <<< 40) ^^^
  (clmulByte a (b >>> 48) <<< 48) ^^^ (clmulByte a (b >>> 56) <<< 56)

@[inline]
def clmulHi (a b : UInt64) : UInt64 :=
  selectBit (a >>> 63) b 1 ^^^ selectBit (a >>> 62) b 2 ^^^
  selectBit (a >>> 61) b 3 ^^^ selectBit (a >>> 60) b 4 ^^^
  selectBit (a >>> 59) b 5 ^^^ selectBit (a >>> 58) b 6 ^^^
  selectBit (a >>> 57) b 7 ^^^ selectBit (a >>> 56) b 8 ^^^
  selectBit (a >>> 55) b 9 ^^^ selectBit (a >>> 54) b 10 ^^^
  selectBit (a >>> 53) b 11 ^^^ selectBit (a >>> 52) b 12 ^^^
  selectBit (a >>> 51) b 13 ^^^ selectBit (a >>> 50) b 14 ^^^
  selectBit (a >>> 49) b 15 ^^^ selectBit (a >>> 48) b 16 ^^^
  selectBit (a >>> 47) b 17 ^^^ selectBit (a >>> 46) b 18 ^^^
  selectBit (a >>> 45) b 19 ^^^ selectBit (a >>> 44) b 20 ^^^
  selectBit (a >>> 43) b 21 ^^^ selectBit (a >>> 42) b 22 ^^^
  selectBit (a >>> 41) b 23 ^^^ selectBit (a >>> 40) b 24 ^^^
  selectBit (a >>> 39) b 25 ^^^ selectBit (a >>> 38) b 26 ^^^
  selectBit (a >>> 37) b 27 ^^^ selectBit (a >>> 36) b 28 ^^^
  selectBit (a >>> 35) b 29 ^^^ selectBit (a >>> 34) b 30 ^^^
  selectBit (a >>> 33) b 31 ^^^ selectBit (a >>> 32) b 32 ^^^
  selectBit (a >>> 31) b 33 ^^^ selectBit (a >>> 30) b 34 ^^^
  selectBit (a >>> 29) b 35 ^^^ selectBit (a >>> 28) b 36 ^^^
  selectBit (a >>> 27) b 37 ^^^ selectBit (a >>> 26) b 38 ^^^
  selectBit (a >>> 25) b 39 ^^^ selectBit (a >>> 24) b 40 ^^^
  selectBit (a >>> 23) b 41 ^^^ selectBit (a >>> 22) b 42 ^^^
  selectBit (a >>> 21) b 43 ^^^ selectBit (a >>> 20) b 44 ^^^
  selectBit (a >>> 19) b 45 ^^^ selectBit (a >>> 18) b 46 ^^^
  selectBit (a >>> 17) b 47 ^^^ selectBit (a >>> 16) b 48 ^^^
  selectBit (a >>> 15) b 49 ^^^ selectBit (a >>> 14) b 50 ^^^
  selectBit (a >>> 13) b 51 ^^^ selectBit (a >>> 12) b 52 ^^^
  selectBit (a >>> 11) b 53 ^^^ selectBit (a >>> 10) b 54 ^^^
  selectBit (a >>> 9) b 55 ^^^ selectBit (a >>> 8) b 56 ^^^
  selectBit (a >>> 7) b 57 ^^^ selectBit (a >>> 6) b 58 ^^^
  selectBit (a >>> 5) b 59 ^^^ selectBit (a >>> 4) b 60 ^^^
  selectBit (a >>> 3) b 61 ^^^ selectBit (a >>> 2) b 62 ^^^
  selectBit (a >>> 1) b 63

@[inline]
def reduceGf64 (lo hi : UInt64) : UInt64 :=
  let spill := (hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60)
  let v := hi ^^^ spill
  lo ^^^ v ^^^ (v <<< 1) ^^^ (v <<< 3) ^^^ (v <<< 4)

@[noinline]
def mulGf64 (a b : UInt64) : UInt64 :=
  reduceGf64 (clmulLo a b) (clmulHi a b)

@[noinline]
def karatsuba0 (a0 a1 a2 b0 b1 b2 : UInt64) : UInt64 :=
  let p0 := mulGf64 a0 b0
  let p1 := mulGf64 a1 b1
  let p2 := mulGf64 a2 b2
  let e3 := mulGf64 (a1 ^^^ a2) (b1 ^^^ b2) ^^^ p1 ^^^ p2
  p0 ^^^ e3

@[noinline]
def karatsuba1 (a0 a1 a2 b0 b1 b2 : UInt64) : UInt64 :=
  let p0 := mulGf64 a0 b0
  let p1 := mulGf64 a1 b1
  let p2 := mulGf64 a2 b2
  let e1 := mulGf64 (a0 ^^^ a1) (b0 ^^^ b1) ^^^ p0 ^^^ p1
  let e3 := mulGf64 (a1 ^^^ a2) (b1 ^^^ b2) ^^^ p1 ^^^ p2
  e1 ^^^ e3 ^^^ p2

@[noinline]
def karatsuba2 (a0 a1 a2 b0 b1 b2 : UInt64) : UInt64 :=
  let p0 := mulGf64 a0 b0
  let p1 := mulGf64 a1 b1
  let p2 := mulGf64 a2 b2
  let e2 := mulGf64 (a0 ^^^ a2) (b0 ^^^ b2) ^^^ p0 ^^^ p2 ^^^ p1
  e2 ^^^ p2

@[inline]
def transpose8x8Bits (x : UInt64) : UInt64 :=
  let t0 := (x ^^^ (x >>> 7)) &&& 0x00aa00aa00aa00aa
  let x1 := x ^^^ t0 ^^^ (t0 <<< 7)
  let t1 := (x1 ^^^ (x1 >>> 14)) &&& 0x0000cccc0000cccc
  let x2 := x1 ^^^ t1 ^^^ (t1 <<< 14)
  let t2 := (x2 ^^^ (x2 >>> 28)) &&& 0x00000000f0f0f0f0
  x2 ^^^ t2 ^^^ (t2 <<< 28)

end LeanVmXmss.Native.Kernels.KeccakGkr
```

#### `LeanVmXmss/Native/Kernels/KeccakGkr/Transpose.lean` (`sha256: 6c55927b25674fbbef9d950eb7e6b38cb8f7ec96e6008a5386753d22dc02afc8`)
```lean
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
```

#### `LeanVmXmss/Native/Kernels/KeccakGkr/Chi.lean` (`sha256: 777a62d88c299d017751064e25fc4b29b01e1aa376bb51a8a87fe4f2b973c5ed`)
```lean
import Native.Kernels.KeccakGkr.Support

namespace LeanVmXmss.Native.Kernels.KeccakGkr

set_option compiler.ignoreBorrowAnnotation true

@[inline]
def alongPos (j k : USize) : USize :=
  let lane := j / 64
  let z := j % 64
  let nextLane := (lane % 5 + k) % 5 + 5 * (lane / 5)
  64 * nextLane + z

def chiWordsAt (block : ByteArray) (n baseA baseB baseC : USize) (acc : ByteArray) : ByteArray :=
  Nat.rec (motive := fun _ => ByteArray) acc
    (fun w prev =>
      let uw := USize.ofNat w
      let wa := readWordAt block (baseA + uw)
      let wb := readWordAt block (baseB + uw)
      let wc := readWordAt block (baseC + uw)
      pushU64LE prev (chiWordD2 wa wb wc))
    n.toNat

@[noinline, export lean_xmss_keccak_chi_planes]
def keccakChiPlanes (block : ByteArray) (n : USize) : ByteArray :=
  let cap := 1600 * n.toNat * 8
  Nat.rec (motive := fun _ => ByteArray) (ByteArray.emptyWithCapacity cap)
    (fun j prev =>
      let uj := USize.ofNat j
      let p1 := alongPos uj 1
      let p2 := alongPos uj 2
      chiWordsAt block n (n * uj) (n * p1) (n * p2) prev)
    1600

end LeanVmXmss.Native.Kernels.KeccakGkr
```

#### `LeanVmXmss/Native/Kernels/KeccakGkr/Planes.lean` (`sha256: 4dd45ea203a3aa496c0cd125d08962ef0ee057ea03c019db1824cfc39718d553`)
```lean
import Native.Kernels.KeccakGkr.Support

namespace LeanVmXmss.Native.Kernels.KeccakGkr

set_option compiler.ignoreBorrowAnnotation true

@[inline]
def rhoOffset (lane : USize) : USize :=
  let r0 : UInt64 := 0x1c3e0100
  let r1 : UInt64 := 0x062c241b
  let r2 : UInt64 := 0x0a031437
  let r3 : UInt64 := 0x2927192b
  let r4 : UInt64 := 0x08150f2d
  let r5 : UInt64 := 0x383d0212
  let idx := lane.toUInt64
  if idx < 4 then
    ((r0 >>> ((idx &&& 3) <<< 3)) &&& 0xff).toUSize
  else if idx < 8 then
    ((r1 >>> (((idx - 4) &&& 3) <<< 3)) &&& 0xff).toUSize
  else if idx < 12 then
    ((r2 >>> (((idx - 8) &&& 3) <<< 3)) &&& 0xff).toUSize
  else if idx < 16 then
    ((r3 >>> (((idx - 12) &&& 3) <<< 3)) &&& 0xff).toUSize
  else if idx < 20 then
    ((r4 >>> (((idx - 16) &&& 3) <<< 3)) &&& 0xff).toUSize
  else if idx < 24 then
    ((r5 >>> (((idx - 20) &&& 3) <<< 3)) &&& 0xff).toUSize
  else 14

@[inline]
def iotaMaskWord (rc : UInt64) (pos : USize) : UInt64 :=
  if pos < 64 then
    let bit := (rc >>> pos.toUInt64) &&& 1
    (0 : UInt64) - bit
  else 0

@[inline]
def readPlaneWordIota (inp : ByteArray) (n pos w : USize) (rc : UInt64) : UInt64 :=
  readWordAt inp (n * pos + w) ^^^ iotaMaskWord rc pos

@[inline]
def columnParityWord (inp : ByteArray) (n x z w : USize) (rc : UInt64) : UInt64 :=
  let p0 := 64 * x + z
  let p1 := 64 * (x + 5) + z
  let p2 := 64 * (x + 10) + z
  let p3 := 64 * (x + 15) + z
  let p4 := 64 * (x + 20) + z
  readPlaneWordIota inp n p0 w rc ^^^
  readPlaneWordIota inp n p1 w rc ^^^
  readPlaneWordIota inp n p2 w rc ^^^
  readPlaneWordIota inp n p3 w rc ^^^
  readPlaneWordIota inp n p4 w rc

def columnWordsAt (inp : ByteArray) (n x z : USize) (rc : UInt64) (acc : ByteArray) : ByteArray :=
  Nat.rec (motive := fun _ => ByteArray) acc
    (fun w prev =>
      let cw := columnParityWord inp n x z (USize.ofNat w) rc
      pushU64LE prev cw)
    n.toNat

def buildColumnParities (inp : ByteArray) (n : USize) (rc : UInt64) : ByteArray :=
  let cap := 320 * n.toNat * 8
  Nat.rec (motive := fun _ => ByteArray) (ByteArray.emptyWithCapacity cap)
    (fun col prev =>
      let ucol := USize.ofNat col
      columnWordsAt inp n (ucol / 64) (ucol % 64) rc prev)
    320

def linearPositionWords (inp cols : ByteArray) (n outPos : USize) (rc : UInt64) (acc : ByteArray) : ByteArray :=
  let outLane := outPos / 64
  let outZ := outPos % 64
  let srcLane := (outLane % 5 + 3 * (outLane / 5)) % 5 + 5 * (outLane % 5)
  let rot := rhoOffset srcLane
  let srcZ := (outZ + 64 - rot) % 64
  let srcPos := 64 * srcLane + srcZ
  let xm := (srcLane % 5 + 4) % 5
  let xp := (srcLane % 5 + 1) % 5
  let baseA := n * (64 * xm + srcZ)
  let baseB := n * (64 * xp + ((srcZ + 63) % 64))
  Nat.rec (motive := fun _ => ByteArray) acc
    (fun w prev =>
      let uw := USize.ofNat w
      let aw := readPlaneWordIota inp n srcPos uw rc
      let c1 := readWordAt cols (baseA + uw)
      let c2 := readWordAt cols (baseB + uw)
      pushU64LE prev (aw ^^^ c1 ^^^ c2))
    n.toNat

@[noinline, export lean_xmss_keccak_theta_rho_pi_iota_planes]
def keccakThetaRhoPiIotaPlanes (inp : ByteArray) (n : USize) (rc : UInt64) : ByteArray :=
  let cols := buildColumnParities inp n rc
  let cap := 1600 * n.toNat * 8
  Nat.rec (motive := fun _ => ByteArray) (ByteArray.emptyWithCapacity cap)
    (fun outPos prev => linearPositionWords inp cols n (USize.ofNat outPos) rc prev)
    1600

end LeanVmXmss.Native.Kernels.KeccakGkr
```

#### `LeanVmXmss/Native/Kernels/KeccakGkr/Rmfe.lean` (`sha256: 76b420165b7cd1b8f3c038ac5cf53ce23b65d754ee69aeeb96e5021cf2ae6818`)
```lean
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
```

#### `LeanVmXmss/Native/Kernels/KeccakGkr/Fold.lean` (`sha256: 6365d3e2b8b5f629e8eef49d9ca4edc5440a12df026ccc91a3c4571dd6f8a7c7`)
```lean
import Native.Kernels.KeccakGkr.Support

namespace LeanVmXmss.Native.Kernels.KeccakGkr

set_option compiler.ignoreBorrowAnnotation true

@[noinline]
def foldStepOne (lo hi : ByteArray) (i : USize) (c0 c1 c2 : UInt64) (acc : ByteArray) : ByteArray :=
  let base := 3 * i
  let l0 := readWordAt lo base
  let l1 := readWordAt lo (base + 1)
  let l2 := readWordAt lo (base + 2)
  let h0 := readWordAt hi base
  let h1 := readWordAt hi (base + 1)
  let h2 := readWordAt hi (base + 2)
  let d0 := l0 ^^^ h0
  let d1 := l1 ^^^ h1
  let d2 := l2 ^^^ h2
  let m0 := karatsuba0 c0 c1 c2 d0 d1 d2
  let m1 := karatsuba1 c0 c1 c2 d0 d1 d2
  let m2 := karatsuba2 c0 c1 c2 d0 d1 d2
  let a0 := pushU64LE acc (l0 ^^^ m0)
  let a1 := pushU64LE a0 (l1 ^^^ m1)
  pushU64LE a1 (l2 ^^^ m2)

@[noinline, export lean_xmss_gkr_fold_even_odd]
def gkrFoldEvenOdd (lo hi : ByteArray) (n : USize) (c0 c1 c2 : UInt64) : ByteArray :=
  let cap := n.toNat * 24
  Nat.rec (motive := fun _ => ByteArray) (ByteArray.emptyWithCapacity cap)
    (fun i prev => foldStepOne lo hi (USize.ofNat i) c0 c1 c2 prev)
    n.toNat

end LeanVmXmss.Native.Kernels.KeccakGkr
```

#### `Tests/Unit/NativeKeccakGkrKernelTest.lean` (`sha256: 453e8be28a4d890072a691081cd0d6ff81337cc5b2355ffddad6743c39fd71c7`)
```lean
import Lean
import Spec.Field.Basic
import Spec.Keccak.Basic
import Spec.KeccakGkr.Basic
import Model.Field.NativeKernel
import Model.KeccakGkr.Scalar
import Native.Kernels.KeccakGkr

open Lean Elab Command

def hasSubstr (haystack needle : String) : Bool :=
  match haystack.splitOn needle with
  | _ :: _ :: _ => true
  | _ => false

run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  let mut rejected : Nat := 0
  for (name, info) in env.constants.toList do
    let text := name.toString
    if hasSubstr text "LeanVmXmss.Native.Kernels.KeccakGkr" then
      if hasSubstr text "._unsafe_rec" then
        logError m!"Forbidden generated name: {name}"
        rejected := rejected + 1
      if info.isUnsafe then
        logError m!"Unsafe declaration: {name}"
        rejected := rejected + 1
      if Lean.isExtern env name then
        logError m!"External declaration: {name}"
        rejected := rejected + 1
      let dependencies ← Lean.collectAxioms name
      for dependency in dependencies do
        unless #[`propext, `Quot.sound].contains dependency do
          logError m!"Forbidden transitive dependency in {name}: {dependency}"
          rejected := rejected + 1
      count := count + 1
  if count = 0 then throwError "Empty Native.Kernels.KeccakGkr declaration inventory"
  if rejected > 0 then throwError "Strict Native.Kernels.KeccakGkr audit rejected {rejected} declarations"
  logInfo m!"NATIVE_KECCAK_GKR_STRICT_AUDIT_COUNT {count}"
  logInfo m!"NATIVE_KECCAK_GKR_STRICT_AUDIT_REJECTIONS {rejected}"

#print axioms LeanVmXmss.Native.Kernels.KeccakGkr.keccakChiPlanes
#print axioms LeanVmXmss.Native.Kernels.KeccakGkr.keccakThetaRhoPiIotaPlanes
#print axioms LeanVmXmss.Native.Kernels.KeccakGkr.rmfePackBatch
#print axioms LeanVmXmss.Native.Kernels.KeccakGkr.rmfeUnpackBatch
#print axioms LeanVmXmss.Native.Kernels.KeccakGkr.gkrFoldEvenOdd
#print axioms LeanVmXmss.Native.Kernels.KeccakGkr.bitTranspose64x64

namespace LeanVmXmss.Tests.Unit.NativeKeccakGkrKernelTest

open Spec.Field (E eadd)
open Model.Field (nativeKaratsuba)
open Model.Pcs.Ntt (foldRange)
open Native.Kernels.KeccakGkr

def prngNext (state : UInt64) : UInt64 :=
  let s1 := state ^^^ (state <<< 13)
  let s2 := s1 ^^^ (s1 >>> 7)
  s2 ^^^ (s2 <<< 17)

def genWords (seed : UInt64) (count : Nat) : Array UInt64 :=
  let (arr, _) := foldRange count
    (fun (acc, st) _ =>
      let next := prngNext st
      (acc.push next, next))
    (Array.emptyWithCapacity count, seed)
  arr

def sliceStatesToBlock (states : Array (Array UInt64)) (nWords : Nat) : ByteArray :=
  let nInst := states.size
  foldRange 1600
    (fun acc pos =>
      let lane := pos / 64
      let z := UInt64.ofNat (pos % 64)
      foldRange nWords
        (fun cur w =>
          let word := foldRange 64
            (fun wAcc b =>
              let instIdx := 64 * w + b
              if instIdx < nInst then
                let st := states[instIdx]?.getD Spec.Keccak.zero
                let laneWord := st[lane]?.getD 0
                let bit := (laneWord >>> z) &&& 1
                wAcc ||| (bit <<< UInt64.ofNat b)
              else wAcc)
            (0 : UInt64)
          pushU64LE cur word)
        acc)
    (ByteArray.emptyWithCapacity (1600 * nWords * 8))

def unsliceBlockToStates (block : ByteArray) (nWords nInst : Nat) : Array (Array UInt64) :=
  foldRange nInst
    (fun acc instIdx =>
      let w := instIdx / 64
      let b := UInt64.ofNat (instIdx % 64)
      let st := foldRange 25
        (fun sAcc lane =>
          let laneWord := foldRange 64
            (fun lAcc z =>
              let pos := 64 * lane + z
              let pw := readWordAt block (USize.ofNat (nWords * pos + w))
              let bit := (pw >>> b) &&& 1
              lAcc ||| (bit <<< UInt64.ofNat z))
            (0 : UInt64)
          sAcc.push laneWord)
        (Array.emptyWithCapacity 25)
      acc.push st)
    (Array.emptyWithCapacity nInst)

def applyFinalIotaPlanes (block : ByteArray) (n : USize) (rc : UInt64) : ByteArray :=
  foldRange 1600
    (fun acc pos =>
      let upos := USize.ofNat pos
      let mask := iotaMaskWord rc upos
      let base := n * upos
      foldRange n.toNat
        (fun cur w =>
          let v := readWordAt block (base + USize.ofNat w) ^^^ mask
          pushU64LE cur v)
        acc)
    (ByteArray.emptyWithCapacity block.size)

def runBitSlicedKeccak24 (block0 : ByteArray) (n : USize) : ByteArray :=
  let s24 := foldRange 24
    (fun cur r =>
      let prevRc := if r = 0 then (0 : UInt64) else Spec.Keccak.rc[r - 1]?.getD 0
      let u := keccakThetaRhoPiIotaPlanes cur n prevRc
      keccakChiPlanes u n)
    block0
  let lastRc := Spec.Keccak.rc[23]?.getD 0
  applyFinalIotaPlanes s24 n lastRc

def checkTernaryD2 : Bool :=
  let words := genWords 0x13579bdf2468ace1 96
  foldRange 32
    (fun ok i =>
      let a := words[3 * i]?.getD 0
      let b := words[3 * i + 1]?.getD 0
      let c := words[3 * i + 2]?.getD 0
      let t := ternaryLogic64 a b c 0xD2
      let d := a ^^^ ((~~~b) &&& c)
      ok && decide (t = d))
    true

def checkKeccakPlanesDifferential : Bool :=
  let nWords : Nat := 2
  let nInst : Nat := 128
  let rawWords := genWords 0xdeadbeefcafebabe (nInst * 25)
  let states := foldRange nInst
    (fun acc i =>
      let st := foldRange 25
        (fun s l => s.push (rawWords[25 * i + l]?.getD 0))
        (Array.emptyWithCapacity 25)
      acc.push st)
    (Array.emptyWithCapacity nInst)
  let block0 := sliceStatesToBlock states nWords
  let blockOut := runBitSlicedKeccak24 block0 (USize.ofNat nWords)
  let gotStates := unsliceBlockToStates blockOut nWords nInst
  foldRange nInst
    (fun ok i =>
      let expected := Spec.Keccak.keccakF1600 (states[i]?.getD Spec.Keccak.zero)
      let got := gotStates[i]?.getD Spec.Keccak.zero
      let laneOk := foldRange 25
        (fun lOk l =>
          let ew := expected[l]?.getD 0
          let gw := got[l]?.getD 0
          lOk && decide (ew = gw))
        true
      ok && laneOk)
    true

def checkRmfePackUnpackDifferential : Bool :=
  let count : Nat := 256
  let words := genWords 0x0123456789abcdef (count * 2)
  let u16A := foldRange count (fun acc i => acc.push ((words[2 * i]?.getD 0) &&& 0xffff)) #[]
  let u16B := foldRange count (fun acc i => acc.push ((words[2 * i + 1]?.getD 0) &&& 0xffff)) #[]
  let bytesA := foldRange count (fun b i => pushU16LE b (u16A[i]?.getD 0)) (ByteArray.emptyWithCapacity (count * 2))
  let bytesB := foldRange count (fun b i => pushU16LE b (u16B[i]?.getD 0)) (ByteArray.emptyWithCapacity (count * 2))
  let packedA := rmfePackBatch bytesA (USize.ofNat count)
  let packedB := rmfePackBatch bytesB (USize.ofNat count)
  let packOk := foldRange count
    (fun ok i =>
      let a := u16A[i]?.getD 0
      let gotA := readU32LE packedA (USize.ofNat (4 * i))
      let refA := Spec.KeccakGkr.embedUnit a
      ok && decide (gotA = refA))
    true
  let prodBytes := foldRange count
    (fun b i =>
      let ea := readU32LE packedA (USize.ofNat (4 * i))
      let eb := readU32LE packedB (USize.ofNat (4 * i))
      let prod := Spec.KeccakGkr.carryless ea eb
      pushU64LE b prod)
    (ByteArray.emptyWithCapacity (count * 8))
  let unpacked := rmfeUnpackBatch prodBytes (USize.ofNat count)
  let unpackOk := foldRange count
    (fun ok i =>
      let a := u16A[i]?.getD 0
      let b := u16B[i]?.getD 0
      let got := readU16LE unpacked (USize.ofNat (2 * i))
      let expected := a &&& b
      ok && decide (got = expected))
    true
  packOk && unpackOk

def checkGkrFoldDifferential : Bool :=
  let count : Nat := 256
  let words := genWords 0xfedcba9876543210 (count * 6 + 3)
  let ch : E := ⟨words[0]?.getD 0, words[1]?.getD 0, words[2]?.getD 0⟩
  let (loBytes, hiBytes, table) := foldRange count
    (fun (lb, hb, tb) i =>
      let base := 3 + 6 * i
      let loE : E := ⟨words[base]?.getD 0, words[base + 1]?.getD 0, words[base + 2]?.getD 0⟩
      let hiE : E := ⟨words[base + 3]?.getD 0, words[base + 4]?.getD 0, words[base + 5]?.getD 0⟩
      let lb1 := pushU64LE (pushU64LE (pushU64LE lb loE.c0) loE.c1) loE.c2
      let hb1 := pushU64LE (pushU64LE (pushU64LE hb hiE.c0) hiE.c1) hiE.c2
      (lb1, hb1, (tb.push loE).push hiE))
    (ByteArray.emptyWithCapacity (count * 24),
     ByteArray.emptyWithCapacity (count * 24),
     Array.emptyWithCapacity (count * 2))
  let expected := Model.KeccakGkr.fold1 table ch
  let gotBytes := gkrFoldEvenOdd loBytes hiBytes (USize.ofNat count) ch.c0 ch.c1 ch.c2
  foldRange count
    (fun ok i =>
      let expE := expected[i]?.getD Spec.Field.zero
      let g0 := readWordAt gotBytes (USize.ofNat (3 * i))
      let g1 := readWordAt gotBytes (USize.ofNat (3 * i + 1))
      let g2 := readWordAt gotBytes (USize.ofNat (3 * i + 2))
      ok && decide (g0 = expE.c0) && decide (g1 = expE.c1) && decide (g2 = expE.c2))
    true

def refBitTranspose64Block (inp : ByteArray) (blockBase : Nat) : ByteArray :=
  foldRange 8
    (fun acc b =>
      foldRange 8
        (fun cur t =>
          let byteVal := foldRange 8
            (fun bv x =>
              let inByte := byteAt inp (USize.ofNat (blockBase + 8 * x + b))
              let bit := (inByte.toUInt64 >>> UInt64.ofNat t) &&& 1
              bv ||| (bit <<< UInt64.ofNat x))
            (0 : UInt64)
          cur.push byteVal.toUInt8)
        acc)
    (ByteArray.emptyWithCapacity 64)

def checkBitTranspose64x64Differential : Bool :=
  let nBlocks : Nat := 16
  let words := genWords 0x8877665544332211 (nBlocks * 8)
  let inp := foldRange (nBlocks * 8)
    (fun b i => pushU64LE b (words[i]?.getD 0))
    (ByteArray.emptyWithCapacity (nBlocks * 64))
  let got := bitTranspose64x64 inp (USize.ofNat nBlocks)
  foldRange nBlocks
    (fun ok blk =>
      let refBlk := refBitTranspose64Block inp (64 * blk)
      let blkOk := foldRange 64
        (fun bOk off =>
          let gByte := byteAt got (USize.ofNat (64 * blk + off))
          let rByte := byteAt refBlk (USize.ofNat off)
          bOk && decide (gByte = rByte))
        true
      ok && blkOk)
    true

end LeanVmXmss.Tests.Unit.NativeKeccakGkrKernelTest

open LeanVmXmss.Tests.Unit.NativeKeccakGkrKernelTest
open LeanVmXmss.Native.Kernels.KeccakGkr

def runBenchIters (iters : Nat) (step : UInt64 → ByteArray) : IO (Nat × UInt64) := do
  let warm := step 0
  let t0 ← IO.monoNanosNow
  let mut acc : UInt64 := readWordAt warm 0
  for i in [:iters] do
    let out := step (UInt64.ofNat i)
    acc := acc ^^^ readWordAt out (USize.ofNat (i % 4))
  let t1 ← IO.monoNanosNow
  let elapsed := t1 - t0
  return (elapsed / iters, acc)

def main : IO Unit := do
  unless checkTernaryD2 do
    throw (IO.userError "checkTernaryD2 failed")
  IO.println "PASS: checkTernaryD2 (vpternlogq 0xD2 matches a xor not-b-and-c)"
  unless checkKeccakPlanesDifferential do
    throw (IO.userError "checkKeccakPlanesDifferential failed")
  IO.println "PASS: checkKeccakPlanesDifferential (128 instances x 24 rounds bit-sliced vs Spec.Keccak.keccakF1600)"
  unless checkRmfePackUnpackDifferential do
    throw (IO.userError "checkRmfePackUnpackDifferential failed")
  IO.println "PASS: checkRmfePackUnpackDifferential (256 packs gf2Affine64 8-matrix embed + project vs Spec.KeccakGkr)"
  unless checkGkrFoldDifferential do
    throw (IO.userError "checkGkrFoldDifferential failed")
  IO.println "PASS: checkGkrFoldDifferential (256 F192 pairs planar fold vs Model.KeccakGkr.fold1)"
  unless checkBitTranspose64x64Differential do
    throw (IO.userError "checkBitTranspose64x64Differential failed")
  IO.println "PASS: checkBitTranspose64x64Differential (16x64-byte 64x64 bit transpose vs bit-by-bit reference)"

  let blockWords : USize := 8
  let benchBlock := ByteArray.mk (Array.replicate 102408 0xa5)
  let (chiNs, chiChk) ← runBenchIters 20
    (fun k => keccakChiPlanes (benchBlock.push k.toUInt8) blockWords)
  let (triNs, triChk) ← runBenchIters 20
    (fun k => keccakThetaRhoPiIotaPlanes benchBlock blockWords (0x800000008000808b ^^^ k))

  let rmfeCount : USize := 4096
  let rmfeIn := ByteArray.mk (Array.replicate 8192 0x5a)
  let (packNs, packChk) ← runBenchIters 20
    (fun k => rmfePackBatch (rmfeIn.push k.toUInt8) rmfeCount)
  let rmfeProdIn := ByteArray.mk (Array.replicate 32768 0x3c)
  let (unpackNs, unpackChk) ← runBenchIters 20
    (fun k => rmfeUnpackBatch (rmfeProdIn.push k.toUInt8) rmfeCount)

  let foldCount : USize := 2048
  let foldLo := ByteArray.mk (Array.replicate 49152 0x11)
  let foldHi := ByteArray.mk (Array.replicate 49152 0x22)
  let (foldNs, foldChk) ← runBenchIters 20
    (fun k => gkrFoldEvenOdd foldLo foldHi foldCount (0x123456789abcdef0 ^^^ k) 0xfedcba9876543210 0x0f1e2d3c4b5a6978)

  let trBlocks : USize := 256
  let trIn := ByteArray.mk (Array.replicate 16384 0x9c)
  let (trNs, trChk) ← runBenchIters 20
    (fun k => bitTranspose64x64 (trIn.push k.toUInt8) trBlocks)

  IO.println s!"BENCH_NS lean_xmss_keccak_chi_planes (1600x8 words): {chiNs} ns/iter (chk={chiChk})"
  IO.println s!"BENCH_NS lean_xmss_keccak_theta_rho_pi_iota_planes (1600x8 words): {triNs} ns/iter (chk={triChk})"
  IO.println s!"BENCH_NS lean_xmss_rmfe_pack_batch (4096 u16): {packNs} ns/iter (chk={packChk})"
  IO.println s!"BENCH_NS lean_xmss_rmfe_unpack_batch (4096 u64): {unpackNs} ns/iter (chk={unpackChk})"
  IO.println s!"BENCH_NS lean_xmss_gkr_fold_even_odd (2048 F192): {foldNs} ns/iter (chk={foldChk})"
  IO.println s!"BENCH_NS lean_xmss_bit_transpose_64x64 (256x64B blocks): {trNs} ns/iter (chk={trChk})"
  IO.println "ALL_NATIVE_KECCAK_GKR_KERNEL_TESTS_PASSED"
```

### 2. Strict Audit & `#print axioms` Output
```text
NATIVE_KECCAK_GKR_STRICT_AUDIT_COUNT 63
NATIVE_KECCAK_GKR_STRICT_AUDIT_REJECTIONS 0
'LeanVmXmss.Native.Kernels.KeccakGkr.keccakChiPlanes' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.KeccakGkr.keccakThetaRhoPiIotaPlanes' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.KeccakGkr.rmfePackBatch' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.KeccakGkr.rmfeUnpackBatch' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.KeccakGkr.gkrFoldEvenOdd' depends on axioms: [propext, Quot.sound]
'LeanVmXmss.Native.Kernels.KeccakGkr.bitTranspose64x64' depends on axioms: [propext, Quot.sound]
```

### 3. `lean-native` Differential Test & Benchmark Output
```text
PASS: checkTernaryD2 (vpternlogq 0xD2 matches a xor not-b-and-c)
PASS: checkKeccakPlanesDifferential (128 instances x 24 rounds bit-sliced vs Spec.Keccak.keccakF1600)
PASS: checkRmfePackUnpackDifferential (256 packs gf2Affine64 8-matrix embed + project vs Spec.KeccakGkr)
PASS: checkGkrFoldDifferential (256 F192 pairs planar fold vs Model.KeccakGkr.fold1)
PASS: checkBitTranspose64x64Differential (16x64-byte 64x64 bit transpose vs bit-by-bit reference)
BENCH_NS lean_xmss_keccak_chi_planes (1600x8 words): 1019189 ns/iter (chk=11936128518282651045)
BENCH_NS lean_xmss_keccak_theta_rho_pi_iota_planes (1600x8 words): 1343550 ns/iter (chk=6510615555426900570)
BENCH_NS lean_xmss_rmfe_pack_batch (4096 u16): 89291 ns/iter (chk=17954500899752326)
BENCH_NS lean_xmss_rmfe_unpack_batch (4096 u64): 153661 ns/iter (chk=1847629939724261796)
BENCH_NS lean_xmss_gkr_fold_even_odd (2048 F192): 472550 ns/iter (chk=2454169114451728993)
BENCH_NS lean_xmss_bit_transpose_64x64 (256x64B blocks): 28423 ns/iter (chk=18374687579183185920)
ALL_NATIVE_KECCAK_GKR_KERNEL_TESTS_PASSED
```

GOAL_COMPLETE
<!-- GOAL_COMPLETE -->