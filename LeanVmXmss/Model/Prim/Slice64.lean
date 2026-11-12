import Spec.Field.Basic

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

namespace LeanVmXmss.Model.Prim.Slice64

open Spec.Field (K E zero one)

theorem usize_lt_imp_size_lt {n : Nat} {i : USize} (h : i < n.toUSize) : i.toNat < n := by
  rw [USize.lt_iff_toNat_lt] at h
  exact Nat.lt_of_lt_of_le h (Nat.mod_le n USize.size)

theorem usize_le_lt_imp {n : Nat} {x y : USize}
    (hxy : x ≤ y) (hy : y < n.toUSize) : x.toNat < n := by
  have h1 : y.toNat < n := usize_lt_imp_size_lt hy
  rw [USize.le_iff_toNat_le] at hxy
  exact Nat.lt_of_le_of_lt hxy h1

theorem nat_or_and_le : ∀ (fuel a b m : Nat), a + b + m ≤ fuel →
    (a ||| (b &&& m)) ≤ (a ||| m)
  | 0, a, b, m, hf => by
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    have hm : m = 0 := by omega
    subst ha
    subst hb
    subst hm
    decide
  | fuel + 1, a, b, m, hf => by
    have ih := nat_or_and_le fuel (a >>> 1) (b >>> 1) (m >>> 1) (by
      simp only [Nat.shiftRight_eq_div_pow, Nat.pow_one]
      omega)
    have hdiv1 : ((a ||| (b &&& m)) >>> 1) = ((a >>> 1) ||| ((b >>> 1) &&& (m >>> 1))) := by
      rw [Nat.shiftRight_or_distrib, Nat.shiftRight_and_distrib]
    have hdiv2 : ((a ||| m) >>> 1) = ((a >>> 1) ||| (m >>> 1)) := by
      rw [Nat.shiftRight_or_distrib]
    simp only [Nat.shiftRight_eq_div_pow, Nat.pow_one] at hdiv1 hdiv2 ih
    have hbit1 : ((a ||| (b &&& m)) &&& 1) = ((a &&& 1) ||| ((b &&& 1) &&& (m &&& 1))) := by
      have h1 : (1 : Nat) = 1 &&& 1 := rfl
      rw [Nat.and_or_distrib_right]
      congr 1
      conv =>
        lhs
        rw [h1]
      ac_rfl
    have hbit2 : ((a ||| m) &&& 1) = ((a &&& 1) ||| (m &&& 1)) := by
      rw [Nat.and_or_distrib_right]
    simp only [Nat.and_one_is_mod] at hbit1 hbit2
    have hma : a % 2 = 0 ∨ a % 2 = 1 := by omega
    have hmb : b % 2 = 0 ∨ b % 2 = 1 := by omega
    have hmm : m % 2 = 0 ∨ m % 2 = 1 := by omega
    have hmod : (a ||| (b &&& m)) % 2 ≤ (a ||| m) % 2 := by
      rw [hbit1, hbit2]
      rcases hma with ha | ha
      · rcases hmb with hb | hb
        · rcases hmm with hm | hm
          · simp [ha, hb, hm]
          · simp [ha, hb, hm]
        · rcases hmm with hm | hm
          · simp [ha, hb, hm]
          · simp [ha, hb, hm]
      · rcases hmb with hb | hb
        · rcases hmm with hm | hm
          · simp [ha, hb, hm]
          · simp [ha, hb, hm]
        · rcases hmm with hm | hm
          · simp [ha, hb, hm]
          · simp [ha, hb, hm]
    omega

theorem usize_or_and7_le (base k : USize) :
    (base ||| (k &&& 7)) ≤ (base ||| 7) := by
  rw [USize.le_iff_toNat_le, USize.toNat_or, USize.toNat_and, USize.toNat_or]
  exact nat_or_and_le (base.toNat + k.toNat + (7 : USize).toNat)
    base.toNat k.toNat (7 : USize).toNat (Nat.le_refl _)

@[inline] def foldNat {α : Type} (n : Nat) (f : α → Nat → α) (init : α) : α :=
  Fin.foldl n (fun acc k => f acc k.val) init

@[inline] def byteAtU (b : @& ByteArray) (i : USize) : UInt64 :=
  if h : i < b.usize then (b.uget i (usize_lt_imp_size_lt h)).toUInt64 else 0

@[inline] def readU64LEU (b : @& ByteArray) (idx : USize) : UInt64 :=
  let base := idx <<< 3
  if h : (base ||| 7) < b.usize then
    let b0 := (b.uget (base ||| ((0 : USize) &&& 7)) (usize_le_lt_imp (usize_or_and7_le base 0) h)).toUInt64
    let b1 := (b.uget (base ||| ((1 : USize) &&& 7)) (usize_le_lt_imp (usize_or_and7_le base 1) h)).toUInt64
    let b2 := (b.uget (base ||| ((2 : USize) &&& 7)) (usize_le_lt_imp (usize_or_and7_le base 2) h)).toUInt64
    let b3 := (b.uget (base ||| ((3 : USize) &&& 7)) (usize_le_lt_imp (usize_or_and7_le base 3) h)).toUInt64
    let b4 := (b.uget (base ||| ((4 : USize) &&& 7)) (usize_le_lt_imp (usize_or_and7_le base 4) h)).toUInt64
    let b5 := (b.uget (base ||| ((5 : USize) &&& 7)) (usize_le_lt_imp (usize_or_and7_le base 5) h)).toUInt64
    let b6 := (b.uget (base ||| ((6 : USize) &&& 7)) (usize_le_lt_imp (usize_or_and7_le base 6) h)).toUInt64
    let b7 := (b.uget (base ||| ((7 : USize) &&& 7)) (usize_le_lt_imp (usize_or_and7_le base 7) h)).toUInt64
    let lo := (b0 ||| (b1 <<< 8)) ||| ((b2 <<< 16) ||| (b3 <<< 24))
    let hi := (b4 ||| (b5 <<< 8)) ||| ((b6 <<< 16) ||| (b7 <<< 24))
    lo ||| (hi <<< 32)
  else
    0

@[inline] def readU64LE (b : @& ByteArray) (idx : Nat) : UInt64 :=
  readU64LEU b idx.toUSize

@[inline] def readU64LEOr (b : @& ByteArray) (idx : Nat) (d : UInt64) : UInt64 :=
  let u := idx.toUSize
  if ((u <<< 3) ||| 7) < b.usize then readU64LEU b u else d

@[inline] def pushU64LE (b : ByteArray) (w : UInt64) : ByteArray :=
  let b := b.push w.toUInt8
  let b := b.push (w >>> 8).toUInt8
  let b := b.push (w >>> 16).toUInt8
  let b := b.push (w >>> 24).toUInt8
  let b := b.push (w >>> 32).toUInt8
  let b := b.push (w >>> 40).toUInt8
  let b := b.push (w >>> 48).toUInt8
  b.push (w >>> 56).toUInt8

@[inline] def countU64 (b : @& ByteArray) : Nat :=
  b.size / 8

def packU64Array (xs : @& Array UInt64) : ByteArray :=
  foldNat xs.size
    (fun acc i => pushU64LE acc (xs[i]?.getD 0))
    (ByteArray.emptyWithCapacity (8 * xs.size))

def unpackU64Array (b : @& ByteArray) : Array UInt64 :=
  let n := countU64 b
  foldNat n
    (fun acc i => acc.push (readU64LE b i))
    (Array.emptyWithCapacity n)

structure SliceE where
  c0 : ByteArray
  c1 : ByteArray
  c2 : ByteArray
  deriving Inhabited

@[noinline] def emptyWordsByteArray (cap : Nat) : ByteArray :=
  ByteArray.emptyWithCapacity (8 * cap)

@[inline] def sliceEEmpty (cap : Nat) : SliceE :=
  ⟨emptyWordsByteArray cap, emptyWordsByteArray cap, emptyWordsByteArray cap⟩

@[inline] def sliceESize (s : @& SliceE) : Nat :=
  countU64 s.c0

@[inline] def sliceEPush (s : SliceE) (x : E) : SliceE :=
  ⟨pushU64LE s.c0 x.c0, pushU64LE s.c1 x.c1, pushU64LE s.c2 x.c2⟩

@[inline] def sliceEGet (s : @& SliceE) (idx : Nat) : E :=
  let u := idx.toUSize
  ⟨readU64LEU s.c0 u, readU64LEU s.c1 u, readU64LEU s.c2 u⟩

@[inline] def sliceEGetOr (s : @& SliceE) (idx : Nat) (d : E) : E :=
  let u := idx.toUSize
  if ((u <<< 3) ||| 7) < s.c0.usize then
    ⟨readU64LEU s.c0 u, readU64LEU s.c1 u, readU64LEU s.c2 u⟩
  else
    d

def concatByteArrays (parts : @& Array ByteArray) : ByteArray :=
  let total := foldNat parts.size
    (fun acc idx => acc + (parts[idx]?.getD ByteArray.empty).size)
    0
  let (out, _) := foldNat parts.size
    (fun (cur, off) idx =>
      let p := parts[idx]?.getD ByteArray.empty
      let n := p.size
      (p.copySlice 0 cur off n false, off + n))
    (ByteArray.emptyWithCapacity total, 0)
  out

def sliceEAppend (a : SliceE) (b : @& SliceE) : SliceE :=
  ⟨a.c0 ++ b.c0, a.c1 ++ b.c1, a.c2 ++ b.c2⟩

def sliceEConcat (parts : @& Array SliceE) : SliceE :=
  let c0s := foldNat parts.size
    (fun acc i => acc.push (parts[i]?.getD (sliceEEmpty 0)).c0)
    (Array.emptyWithCapacity parts.size)
  let c1s := foldNat parts.size
    (fun acc i => acc.push (parts[i]?.getD (sliceEEmpty 0)).c1)
    (Array.emptyWithCapacity parts.size)
  let c2s := foldNat parts.size
    (fun acc i => acc.push (parts[i]?.getD (sliceEEmpty 0)).c2)
    (Array.emptyWithCapacity parts.size)
  ⟨concatByteArrays c0s, concatByteArrays c1s, concatByteArrays c2s⟩

def packSliceE (xs : @& Array E) : SliceE :=
  foldNat xs.size
    (fun acc i => sliceEPush acc (xs[i]?.getD zero))
    (sliceEEmpty xs.size)

def unpackSliceE (s : @& SliceE) : Array E :=
  let n := sliceESize s
  foldNat n
    (fun acc i => acc.push (sliceEGet s i))
    (Array.emptyWithCapacity n)

def clmul64 (a b : UInt64) : UInt64 :=
  Fin.foldl 64 (fun acc i =>
    let iu := i.val.toUInt64
    let mask := (0 : UInt64) - ((b >>> iu) &&& 1)
    acc ^^^ ((a <<< iu) &&& mask)) 0

def clmul64Hi (a b : UInt64) : UInt64 :=
  Fin.foldl 63 (fun acc i =>
    let iu := (i.val + 1).toUInt64
    let mask := (0 : UInt64) - ((b >>> iu) &&& 1)
    acc ^^^ ((a >>> (64 - iu)) &&& mask)) 0

def gf2Dot8 (row x : UInt64) : UInt64 :=
  Fin.foldl 8 (fun s j =>
    let ju := j.val.toUInt64
    s ^^^ (((row >>> ju) &&& 1) &&& ((x >>> ju) &&& 1))) 0

def gf2Affine64 (x m : UInt64) (imm : UInt8) : UInt64 :=
  let immU := imm.toUInt64
  Fin.foldl 8 (fun out b =>
    let bu := b.val.toUInt64
    let xb := (x >>> (bu * 8)) &&& 0xff
    let yb := Fin.foldl 8 (fun acc i =>
      let iu := i.val.toUInt64
      acc ||| (gf2Dot8 ((m >>> (iu * 8)) &&& 0xff) xb <<< iu)) 0
    out ||| ((yb ^^^ immU) <<< (bu * 8))) 0

def ternaryLogic64 (a b c : UInt64) (imm : UInt8) : UInt64 :=
  let immU := imm.toUInt64
  Fin.foldl 64 (fun acc i =>
    let iu := i.val.toUInt64
    let idx := (((a >>> iu) &&& 1) <<< 2) ||| (((b >>> iu) &&& 1) <<< 1) ||| ((c >>> iu) &&& 1)
    let bit := (immU >>> idx) &&& 1
    acc ||| (bit <<< iu)) 0

def uget64LE (b : @& ByteArray) (wordIdx : USize) : UInt64 :=
  LeanVmXmss.Model.Prim.uget64LE b wordIdx

def uset64LE (b : ByteArray) (wordIdx : USize) (val : UInt64) : ByteArray :=
  LeanVmXmss.Model.Prim.uset64LE b wordIdx val

@[inline]
def rol64 (x : UInt64) (s : UInt64) : UInt64 :=
  (x <<< s) ||| (x >>> (64 - s))

@[inline]
def gf64Reduce1B (lo hi : UInt64) : UInt64 :=
  lo ^^^ clmul64 hi 0x1b ^^^ clmul64 (clmul64Hi hi 0x1b) 0x1b

end LeanVmXmss.Model.Prim.Slice64
