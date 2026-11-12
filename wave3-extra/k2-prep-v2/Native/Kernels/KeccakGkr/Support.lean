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
