namespace LeanVmXmss.Model.Prim

theorem usize_lt_size {bs : ByteArray} {idx : USize} (h : idx < bs.usize) : idx.toNat < bs.size := by
  have h1 : idx.toNat < bs.usize.toNat := USize.lt_iff_toNat_lt.mp h
  rw [ByteArray.usize.eq_1] at h1
  exact Nat.lt_of_lt_of_le h1 (@USize.toNat_ofNat_le bs.size)

@[inline] def ugetByte (bs : ByteArray) (idx : USize) : UInt64 :=
  if h : idx < bs.usize then (bs.uget idx (usize_lt_size h)).toUInt64 else 0

@[inline] def usetByte (bs : ByteArray) (idx : USize) (b : UInt8) : ByteArray :=
  if h : idx < bs.usize then bs.uset idx b (usize_lt_size h) else bs

@[inline] def uget64LE (bs : ByteArray) (wordIdx : USize) : UInt64 :=
  let n : USize := bs.usize
  let base : USize := wordIdx * 8
  if base + 7 < n then
    if base ≤ base + 7 then
      let b0 := ugetByte bs base
      let b1 := ugetByte bs (base + 1)
      let b2 := ugetByte bs (base + 2)
      let b3 := ugetByte bs (base + 3)
      let b4 := ugetByte bs (base + 4)
      let b5 := ugetByte bs (base + 5)
      let b6 := ugetByte bs (base + 6)
      let b7 := ugetByte bs (base + 7)
      b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) |||
        (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56)
    else 0
  else 0

@[inline] def uset64LE (bs : ByteArray) (wordIdx : USize) (val : UInt64) : ByteArray :=
  let n : USize := bs.usize
  let base : USize := wordIdx * 8
  if base + 7 < n then
    if base ≤ base + 7 then
      let s0 := usetByte bs base val.toUInt8
      let s1 := usetByte s0 (base + 1) (val >>> 8).toUInt8
      let s2 := usetByte s1 (base + 2) (val >>> 16).toUInt8
      let s3 := usetByte s2 (base + 3) (val >>> 24).toUInt8
      let s4 := usetByte s3 (base + 4) (val >>> 32).toUInt8
      let s5 := usetByte s4 (base + 5) (val >>> 40).toUInt8
      let s6 := usetByte s5 (base + 6) (val >>> 48).toUInt8
      usetByte s6 (base + 7) (val >>> 56).toUInt8
    else bs
  else bs

@[inline] def bitMask64 (a b i : UInt64) : UInt64 :=
  a &&& (0 - ((b >>> i) &&& 1))

@[inline] def clmulByteLo (a b : UInt64) : UInt64 :=
  bitMask64 a b 0 ^^^ bitMask64 (a <<< 1) b 1 ^^^
  bitMask64 (a <<< 2) b 2 ^^^ bitMask64 (a <<< 3) b 3 ^^^
  bitMask64 (a <<< 4) b 4 ^^^ bitMask64 (a <<< 5) b 5 ^^^
  bitMask64 (a <<< 6) b 6 ^^^ bitMask64 (a <<< 7) b 7

@[inline] def clmul64 (a b : UInt64) : UInt64 :=
  clmulByteLo a b ^^^ (clmulByteLo a (b >>> 8) <<< 8) ^^^
  (clmulByteLo a (b >>> 16) <<< 16) ^^^ (clmulByteLo a (b >>> 24) <<< 24) ^^^
  (clmulByteLo a (b >>> 32) <<< 32) ^^^ (clmulByteLo a (b >>> 40) <<< 40) ^^^
  (clmulByteLo a (b >>> 48) <<< 48) ^^^ (clmulByteLo a (b >>> 56) <<< 56)

@[inline] def clmulHiOctet (a b base : UInt64) : UInt64 :=
  bitMask64 (a >>> (64 - base)) b base ^^^
  bitMask64 (a >>> (63 - base)) b (base + 1) ^^^
  bitMask64 (a >>> (62 - base)) b (base + 2) ^^^
  bitMask64 (a >>> (61 - base)) b (base + 3) ^^^
  bitMask64 (a >>> (60 - base)) b (base + 4) ^^^
  bitMask64 (a >>> (59 - base)) b (base + 5) ^^^
  bitMask64 (a >>> (58 - base)) b (base + 6) ^^^
  bitMask64 (a >>> (57 - base)) b (base + 7)

@[inline] def clmul64Hi (a b : UInt64) : UInt64 :=
  bitMask64 (a >>> 63) b 1 ^^^ bitMask64 (a >>> 62) b 2 ^^^
  bitMask64 (a >>> 61) b 3 ^^^ bitMask64 (a >>> 60) b 4 ^^^
  bitMask64 (a >>> 59) b 5 ^^^ bitMask64 (a >>> 58) b 6 ^^^
  bitMask64 (a >>> 57) b 7 ^^^
  clmulHiOctet a b 8 ^^^ clmulHiOctet a b 16 ^^^ clmulHiOctet a b 24 ^^^
  clmulHiOctet a b 32 ^^^ clmulHiOctet a b 40 ^^^ clmulHiOctet a b 48 ^^^
  clmulHiOctet a b 56

@[inline] def gf2Dot8 (row x : UInt64) : UInt64 :=
  let p := row &&& x &&& 0xff
  let p1 := p ^^^ (p >>> 4)
  let p2 := p1 ^^^ (p1 >>> 2)
  (p2 ^^^ (p2 >>> 1)) &&& 1

@[inline] def gf2AffineByte (xb m : UInt64) : UInt64 :=
  (gf2Dot8 ((m >>> 0) &&& 0xff) xb <<< 0) |||
  (gf2Dot8 ((m >>> 8) &&& 0xff) xb <<< 1) |||
  (gf2Dot8 ((m >>> 16) &&& 0xff) xb <<< 2) |||
  (gf2Dot8 ((m >>> 24) &&& 0xff) xb <<< 3) |||
  (gf2Dot8 ((m >>> 32) &&& 0xff) xb <<< 4) |||
  (gf2Dot8 ((m >>> 40) &&& 0xff) xb <<< 5) |||
  (gf2Dot8 ((m >>> 48) &&& 0xff) xb <<< 6) |||
  (gf2Dot8 ((m >>> 56) &&& 0xff) xb <<< 7)

@[inline] def gf2Affine64 (x m : UInt64) : UInt64 :=
  (gf2AffineByte ((x >>> 0) &&& 0xff) m <<< 0) |||
  (gf2AffineByte ((x >>> 8) &&& 0xff) m <<< 8) |||
  (gf2AffineByte ((x >>> 16) &&& 0xff) m <<< 16) |||
  (gf2AffineByte ((x >>> 24) &&& 0xff) m <<< 24) |||
  (gf2AffineByte ((x >>> 32) &&& 0xff) m <<< 32) |||
  (gf2AffineByte ((x >>> 40) &&& 0xff) m <<< 40) |||
  (gf2AffineByte ((x >>> 48) &&& 0xff) m <<< 48) |||
  (gf2AffineByte ((x >>> 56) &&& 0xff) m <<< 56)

@[inline] def ternaryLogic64 (a b c : UInt64) (imm8 : UInt8) : UInt64 :=
  let m := imm8.toUInt64
  let na := ~~~a
  let nb := ~~~b
  let nc := ~~~c
  bitMask64 (na &&& nb &&& nc) m 0 |||
  bitMask64 (na &&& nb &&& c) m 1 |||
  bitMask64 (na &&& b &&& nc) m 2 |||
  bitMask64 (na &&& b &&& c) m 3 |||
  bitMask64 (a &&& nb &&& nc) m 4 |||
  bitMask64 (a &&& nb &&& c) m 5 |||
  bitMask64 (a &&& b &&& nc) m 6 |||
  bitMask64 (a &&& b &&& c) m 7

structure U64x8 where
  v0 : UInt64
  v1 : UInt64
  v2 : UInt64
  v3 : UInt64
  v4 : UInt64
  v5 : UInt64
  v6 : UInt64
  v7 : UInt64
  deriving Inhabited, Repr, DecidableEq

namespace U64x8

@[inline] def zero : U64x8 := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

@[inline] def splat (x : UInt64) : U64x8 := ⟨x, x, x, x, x, x, x, x⟩

@[inline] def xor (a b : U64x8) : U64x8 :=
  ⟨a.v0 ^^^ b.v0, a.v1 ^^^ b.v1, a.v2 ^^^ b.v2, a.v3 ^^^ b.v3,
   a.v4 ^^^ b.v4, a.v5 ^^^ b.v5, a.v6 ^^^ b.v6, a.v7 ^^^ b.v7⟩

@[inline] def band (a b : U64x8) : U64x8 :=
  ⟨a.v0 &&& b.v0, a.v1 &&& b.v1, a.v2 &&& b.v2, a.v3 &&& b.v3,
   a.v4 &&& b.v4, a.v5 &&& b.v5, a.v6 &&& b.v6, a.v7 &&& b.v7⟩

@[inline] def bor (a b : U64x8) : U64x8 :=
  ⟨a.v0 ||| b.v0, a.v1 ||| b.v1, a.v2 ||| b.v2, a.v3 ||| b.v3,
   a.v4 ||| b.v4, a.v5 ||| b.v5, a.v6 ||| b.v6, a.v7 ||| b.v7⟩

@[inline] def bnot (a : U64x8) : U64x8 :=
  ⟨~~~a.v0, ~~~a.v1, ~~~a.v2, ~~~a.v3, ~~~a.v4, ~~~a.v5, ~~~a.v6, ~~~a.v7⟩

@[inline] def reduceXor (a : U64x8) : UInt64 :=
  (a.v0 ^^^ a.v1) ^^^ (a.v2 ^^^ a.v3) ^^^ (a.v4 ^^^ a.v5) ^^^ (a.v6 ^^^ a.v7)

@[inline] def loadLE (bs : ByteArray) (wordBase : USize) : U64x8 :=
  ⟨uget64LE bs wordBase,
   uget64LE bs (wordBase + 1),
   uget64LE bs (wordBase + 2),
   uget64LE bs (wordBase + 3),
   uget64LE bs (wordBase + 4),
   uget64LE bs (wordBase + 5),
   uget64LE bs (wordBase + 6),
   uget64LE bs (wordBase + 7)⟩

@[inline] def storeLE (bs : ByteArray) (wordBase : USize) (v : U64x8) : ByteArray :=
  let s0 := uset64LE bs wordBase v.v0
  let s1 := uset64LE s0 (wordBase + 1) v.v1
  let s2 := uset64LE s1 (wordBase + 2) v.v2
  let s3 := uset64LE s2 (wordBase + 3) v.v3
  let s4 := uset64LE s3 (wordBase + 4) v.v4
  let s5 := uset64LE s4 (wordBase + 5) v.v5
  let s6 := uset64LE s5 (wordBase + 6) v.v6
  uset64LE s6 (wordBase + 7) v.v7

end U64x8

structure PlanarSliceRange where
  wordOffset : USize
  wordLen : USize
  deriving Inhabited, Repr, DecidableEq

namespace PlanarSliceRange

@[inline] def byteOffset (r : PlanarSliceRange) : USize := r.wordOffset * 8

@[inline] def byteLen (r : PlanarSliceRange) : USize := r.wordLen * 8

@[inline] def inBounds (bs : ByteArray) (r : PlanarSliceRange) : Bool :=
  let bOff := r.wordOffset * 8
  let bEnd := (r.wordOffset + r.wordLen) * 8
  decide (r.wordOffset ≤ r.wordOffset + r.wordLen) &&
    decide (bOff ≤ bEnd) &&
    decide (bEnd ≤ bs.usize)

@[inline] def subrange (r : PlanarSliceRange) (subOff subLen : USize) : PlanarSliceRange :=
  ⟨r.wordOffset + subOff, if subOff + subLen ≤ r.wordLen then subLen else 0⟩

@[inline] def getWord (bs : ByteArray) (r : PlanarSliceRange) (idx : USize) : UInt64 :=
  if idx < r.wordLen then uget64LE bs (r.wordOffset + idx) else 0

@[inline] def setWord (bs : ByteArray) (r : PlanarSliceRange) (idx : USize) (val : UInt64) : ByteArray :=
  if idx < r.wordLen then uset64LE bs (r.wordOffset + idx) val else bs

@[inline] def getVec8 (bs : ByteArray) (r : PlanarSliceRange) (idx : USize) : U64x8 :=
  if idx + 8 ≤ r.wordLen && idx ≤ idx + 8 then U64x8.loadLE bs (r.wordOffset + idx) else U64x8.zero

@[inline] def setVec8 (bs : ByteArray) (r : PlanarSliceRange) (idx : USize) (v : U64x8) : ByteArray :=
  if idx + 8 ≤ r.wordLen && idx ≤ idx + 8 then U64x8.storeLE bs (r.wordOffset + idx) v else bs

end PlanarSliceRange

end LeanVmXmss.Model.Prim
