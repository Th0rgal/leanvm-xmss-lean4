import Spec.Field.Basic

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

end LeanVmXmss.Model.Prim.Slice64
