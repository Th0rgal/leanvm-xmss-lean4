import Model.Prim.Slice64
import Model.Field.NativeKernel
import Proofs.Field.NativeKernel
import Proofs.Field.Extension

namespace LeanVmXmss.Proofs.Prim

open LeanVmXmss.Model.Prim
open LeanVmXmss.Spec.Field (K E)

@[inline] def primBaseMul (a b : UInt64) : UInt64 :=
  LeanVmXmss.Model.Field.nativeReduce (clmul64 a b) (clmul64Hi a b)

@[inline] def primKaratsubaMul (a b : E) : E :=
  let p0 := primBaseMul a.c0 b.c0
  let p1 := primBaseMul a.c1 b.c1
  let p2 := primBaseMul a.c2 b.c2
  let e1 := primBaseMul (a.c0 ^^^ a.c1) (b.c0 ^^^ b.c1) ^^^ p0 ^^^ p1
  let e2 := primBaseMul (a.c0 ^^^ a.c2) (b.c0 ^^^ b.c2) ^^^ p0 ^^^ p2 ^^^ p1
  let e3 := primBaseMul (a.c1 ^^^ a.c2) (b.c1 ^^^ b.c2) ^^^ p1 ^^^ p2
  ⟨p0 ^^^ e3, e1 ^^^ e3 ^^^ p2, e2 ^^^ p2⟩

theorem usetByte_size (bs : ByteArray) (idx : USize) (b : UInt8) :
    (usetByte bs idx b).size = bs.size := by
  unfold usetByte
  cases h : decide (idx < bs.usize) with
  | true =>
    have hlt : idx < bs.usize := of_decide_eq_true h
    simp only [hlt, dite_true]
    cases bs with
    | mk data =>
      simp only [ByteArray.uset.eq_1, ByteArray.size.eq_1, Array.size_uset]
  | false =>
    have hge : ¬ idx < bs.usize := of_decide_eq_false h
    simp only [hge, dite_false]

theorem usetByte_usize (bs : ByteArray) (idx : USize) (b : UInt8) :
    (usetByte bs idx b).usize = bs.usize := by
  simp only [ByteArray.usize.eq_1, usetByte_size]

theorem byteArray_uget_uset_self (bs : ByteArray) (idx : USize) (b : UInt8)
    (h1 : idx.toNat < bs.size) (h2 : idx.toNat < (bs.uset idx b h1).size) :
    (bs.uset idx b h1).uget idx h2 = b := by
  cases bs with
  | mk data =>
    simp only [ByteArray.uset.eq_1, ByteArray.uget.eq_1, Array.uset.eq_1]
    exact Array.getElem_set_self h1

theorem byteArray_uget_uset_ne (bs : ByteArray) (i j : USize) (b : UInt8)
    (h1 : i.toNat < bs.size) (h2 : j.toNat < (bs.uset i b h1).size) (hj : j.toNat < bs.size)
    (hne : i.toNat ≠ j.toNat) :
    (bs.uset i b h1).uget j h2 = bs.uget j hj := by
  cases bs with
  | mk data =>
    simp only [ByteArray.uset.eq_1, ByteArray.uget.eq_1, Array.uset.eq_1]
    exact Array.getElem_set_ne h1 hj hne

theorem ugetByte_usetByte_self (bs : ByteArray) (idx : USize) (b : UInt8)
    (h : idx < bs.usize) :
    ugetByte (usetByte bs idx b) idx = b.toUInt64 := by
  have h2 : idx < (usetByte bs idx b).usize := by
    rw [usetByte_usize]
    exact h
  unfold ugetByte
  simp only [h2, dite_true]
  revert h2
  unfold usetByte
  simp only [h, dite_true]
  intro h2
  rw [byteArray_uget_uset_self]

theorem ugetByte_usetByte_ne (bs : ByteArray) (i j : USize) (b : UInt8)
    (hne : i ≠ j) :
    ugetByte (usetByte bs i b) j = ugetByte bs j := by
  cases hj : decide (j < bs.usize) with
  | false =>
    have hjge : ¬ j < bs.usize := of_decide_eq_false hj
    have hjge2 : ¬ j < (usetByte bs i b).usize := by
      rw [usetByte_usize]
      exact hjge
    unfold ugetByte
    simp only [hjge, hjge2, dite_false]
  | true =>
    have hjlt : j < bs.usize := of_decide_eq_true hj
    have hjlt2 : j < (usetByte bs i b).usize := by
      rw [usetByte_usize]
      exact hjlt
    unfold ugetByte
    simp only [hjlt, hjlt2, dite_true]
    revert hjlt2
    unfold usetByte
    cases hi : decide (i < bs.usize) with
    | false =>
      have hige : ¬ i < bs.usize := of_decide_eq_false hi
      simp only [hige, dite_false]
      intro _
      trivial
    | true =>
      have hilt : i < bs.usize := of_decide_eq_true hi
      simp only [hilt, dite_true]
      intro hjlt2
      have hne_nat : i.toNat ≠ j.toNat := by
        intro heq
        exact hne (USize.toNat_inj.mp heq)
      rw [byteArray_uget_uset_ne bs i j b (usize_lt_size hilt)
        (usize_lt_size hjlt2) (usize_lt_size hjlt) hne_nat]

theorem usize_ofNat_small (k : Nat) (hk : k < 2 ^ 32) :
    (OfNat.ofNat k : USize).toNat = k := by
  rw [USize.toNat_ofNat]
  rcases System.Platform.numBits_eq with hbits | hbits
  · rw [hbits]
    exact Nat.mod_eq_of_lt hk
  · rw [hbits]
    exact Nat.mod_eq_of_lt (by omega)

theorem usize_mul_eight_mod8 (w : USize) : (w * 8).toNat % 8 = 0 := by
  have h8 : (8 : USize).toNat = 8 := usize_ofNat_small 8 (by decide)
  rw [USize.toNat_mul, h8]
  rcases System.Platform.numBits_eq with hbits | hbits
  · rw [hbits]
    omega
  · rw [hbits]
    omega

theorem usize_add_seven_toNat (base : USize) (h : base ≤ base + 7) :
    (base + 7).toNat = base.toNat + 7 := by
  have hle : base.toNat ≤ (base + 7).toNat := USize.le_iff_toNat_le.mp h
  have h7 : (7 : USize).toNat = 7 := usize_ofNat_small 7 (by decide)
  rw [USize.toNat_add, h7] at hle ⊢
  have hlt := base.toNat_lt_two_pow_numBits
  rcases System.Platform.numBits_eq with hbits | hbits
  · rw [hbits] at hle hlt ⊢
    omega
  · rw [hbits] at hle hlt ⊢
    omega

theorem usize_add_offset_toNat (base : USize) (h : base ≤ base + 7)
    (k : Nat) (hk : k ≤ 7) :
    (base + OfNat.ofNat k).toNat = base.toNat + k := by
  have h7 := usize_add_seven_toNat base h
  have hk_lt : k < 2 ^ 32 := by omega
  have hk_val : (OfNat.ofNat k : USize).toNat = k := usize_ofNat_small k hk_lt
  rw [USize.toNat_add, hk_val]
  have hlt := (base + 7).toNat_lt_two_pow_numBits
  rw [h7] at hlt
  exact Nat.mod_eq_of_lt (by omega)

theorem usize_offset_lt (base n : USize) (h1 : base + 7 < n) (h2 : base ≤ base + 7)
    (k : Nat) (hk : k ≤ 7) :
    base + OfNat.ofNat k < n := by
  rw [USize.lt_iff_toNat_lt]
  have h1' : (base + 7).toNat < n.toNat := USize.lt_iff_toNat_lt.mp h1
  have h7 := usize_add_seven_toNat base h2
  have hk' := usize_add_offset_toNat base h2 k hk
  omega

theorem usize_base_lt (base n : USize) (h1 : base + 7 < n) (h2 : base ≤ base + 7) :
    base < n := by
  rw [USize.lt_iff_toNat_lt]
  have h1' : (base + 7).toNat < n.toNat := USize.lt_iff_toNat_lt.mp h1
  have h2' : base.toNat ≤ (base + 7).toNat := USize.le_iff_toNat_le.mp h2
  omega

theorem usize_offset_ne (base : USize) (h2 : base ≤ base + 7)
    (i j : Nat) (hi : i ≤ 7) (hj : j ≤ 7) (hne : i ≠ j) :
    base + OfNat.ofNat i ≠ base + OfNat.ofNat j := by
  intro heq
  have hnat := congrArg USize.toNat heq
  rw [usize_add_offset_toNat base h2 i hi, usize_add_offset_toNat base h2 j hj] at hnat
  omega

theorem usize_base_ne_offset (base : USize) (h2 : base ≤ base + 7)
    (j : Nat) (hj1 : 1 ≤ j) (hj7 : j ≤ 7) :
    base + OfNat.ofNat j ≠ base := by
  intro heq
  have hnat := congrArg USize.toNat heq
  rw [usize_add_offset_toNat base h2 j hj7] at hnat
  omega

theorem uset64LE_size (bs : ByteArray) (wordIdx : USize) (val : UInt64) :
    (uset64LE bs wordIdx val).size = bs.size := by
  unfold uset64LE
  dsimp only
  cases h1 : decide (wordIdx * 8 + 7 < bs.usize) with
  | false =>
    have h1' : ¬ (wordIdx * 8 + 7 < bs.usize) := of_decide_eq_false h1
    simp only [h1', ite_false]
  | true =>
    have h1' : wordIdx * 8 + 7 < bs.usize := of_decide_eq_true h1
    simp only [h1', ite_true]
    cases h2 : decide (wordIdx * 8 ≤ wordIdx * 8 + 7) with
    | false =>
      have h2' : ¬ (wordIdx * 8 ≤ wordIdx * 8 + 7) := of_decide_eq_false h2
      simp only [h2', ite_false]
    | true =>
      have h2' : wordIdx * 8 ≤ wordIdx * 8 + 7 := of_decide_eq_true h2
      simp only [h2', ite_true, usetByte_size]

theorem uset64LE_usize (bs : ByteArray) (wordIdx : USize) (val : UInt64) :
    (uset64LE bs wordIdx val).usize = bs.usize := by
  simp only [ByteArray.usize.eq_1, uset64LE_size]

theorem byteShift_getLsbD (val : UInt64) (s : UInt64)
    (hs : s.toNat + 8 ≤ 64) (hmod : (s.toBitVec % 64).toNat = s.toNat)
    (k : Nat) (hk : k < 64) :
    (((val >>> s).toUInt8.toUInt64) <<< s).toBitVec.getLsbD k =
      (decide (s.toNat ≤ k) && decide (k < s.toNat + 8) && val.toBitVec.getLsbD k) := by
  simp only [UInt64.toBitVec_shiftLeft, UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8,
    UInt64.toBitVec_shiftRight, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', hmod,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    hk, decide_true, Bool.true_and]
  cases hle : decide (s.toNat ≤ k) with
  | false =>
    have hlt : k < s.toNat := by
      have hnot := of_decide_eq_false hle
      omega
    simp only [hlt, decide_true, Bool.not_true, Bool.false_and]
  | true =>
    have hge : s.toNat ≤ k := of_decide_eq_true hle
    have hnlt : ¬ k < s.toNat := by omega
    have hksub64 : k - s.toNat < 64 := by omega
    simp only [hnlt, hksub64, decide_false, decide_true, Bool.not_false, Bool.true_and]
    cases hhi : decide (k < s.toNat + 8) with
    | false =>
      have hge8 : ¬ k - s.toNat < 8 := by
        have hnot := of_decide_eq_false hhi
        omega
      simp only [hge8, decide_false, Bool.false_and]
    | true =>
      have hlt8 : k - s.toNat < 8 := by
        have hyes := of_decide_eq_true hhi
        omega
      have hadd : s.toNat + (k - s.toNat) = k := by omega
      simp only [hlt8, hadd, decide_true, Bool.true_and]

theorem byteZero_getLsbD (val : UInt64) (k : Nat) (hk : k < 64) :
    val.toUInt8.toUInt64.toBitVec.getLsbD k =
      (decide (k < 8) && val.toBitVec.getLsbD k) := by
  simp only [UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8, BitVec.getLsbD_setWidth,
    hk, decide_true, Bool.true_and]

theorem wordLE_reconstruct (val : UInt64) :
    (val.toUInt8.toUInt64 |||
      ((val >>> 8).toUInt8.toUInt64 <<< 8) |||
      ((val >>> 16).toUInt8.toUInt64 <<< 16) |||
      ((val >>> 24).toUInt8.toUInt64 <<< 24) |||
      ((val >>> 32).toUInt8.toUInt64 <<< 32) |||
      ((val >>> 40).toUInt8.toUInt64 <<< 40) |||
      ((val >>> 48).toUInt8.toUInt64 <<< 48) |||
      ((val >>> 56).toUInt8.toUInt64 <<< 56)) = val := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [UInt64.toBitVec_or, BitVec.getLsbD_or]
  rw [byteZero_getLsbD val k hk,
    byteShift_getLsbD val 8 (by decide) (by decide) k hk,
    byteShift_getLsbD val 16 (by decide) (by decide) k hk,
    byteShift_getLsbD val 24 (by decide) (by decide) k hk,
    byteShift_getLsbD val 32 (by decide) (by decide) k hk,
    byteShift_getLsbD val 40 (by decide) (by decide) k hk,
    byteShift_getLsbD val 48 (by decide) (by decide) k hk,
    byteShift_getLsbD val 56 (by decide) (by decide) k hk]
  have hpart :
      (decide (k < 8) ||
        (decide ((8 : UInt64).toNat ≤ k) && decide (k < (8 : UInt64).toNat + 8)) ||
        (decide ((16 : UInt64).toNat ≤ k) && decide (k < (16 : UInt64).toNat + 8)) ||
        (decide ((24 : UInt64).toNat ≤ k) && decide (k < (24 : UInt64).toNat + 8)) ||
        (decide ((32 : UInt64).toNat ≤ k) && decide (k < (32 : UInt64).toNat + 8)) ||
        (decide ((40 : UInt64).toNat ≤ k) && decide (k < (40 : UInt64).toNat + 8)) ||
        (decide ((48 : UInt64).toNat ≤ k) && decide (k < (48 : UInt64).toNat + 8)) ||
        (decide ((56 : UInt64).toNat ≤ k) && decide (k < (56 : UInt64).toNat + 8))) = true := by
    have hfin : ∀ j : Fin 64,
        (decide (j.val < 8) ||
          (decide ((8 : UInt64).toNat ≤ j.val) && decide (j.val < (8 : UInt64).toNat + 8)) ||
          (decide ((16 : UInt64).toNat ≤ j.val) && decide (j.val < (16 : UInt64).toNat + 8)) ||
          (decide ((24 : UInt64).toNat ≤ j.val) && decide (j.val < (24 : UInt64).toNat + 8)) ||
          (decide ((32 : UInt64).toNat ≤ j.val) && decide (j.val < (32 : UInt64).toNat + 8)) ||
          (decide ((40 : UInt64).toNat ≤ j.val) && decide (j.val < (40 : UInt64).toNat + 8)) ||
          (decide ((48 : UInt64).toNat ≤ j.val) && decide (j.val < (48 : UInt64).toNat + 8)) ||
          (decide ((56 : UInt64).toNat ≤ j.val) && decide (j.val < (56 : UInt64).toNat + 8))) = true := by
      decide
    exact hfin ⟨k, hk⟩
  cases hb : val.toBitVec.getLsbD k
  · simp
  · simpa using hpart

theorem uget64LE_uset64LE_self (bs : ByteArray) (wordIdx : USize) (val : UInt64)
    (h1 : wordIdx * 8 + 7 < bs.usize) (h2 : wordIdx * 8 ≤ wordIdx * 8 + 7) :
    uget64LE (uset64LE bs wordIdx val) wordIdx = val := by
  have hus : (uset64LE bs wordIdx val).usize = bs.usize := uset64LE_usize bs wordIdx val
  unfold uget64LE
  dsimp only
  rw [hus]
  simp only [h1, h2, ite_true]
  unfold uset64LE
  dsimp only
  simp only [h1, h2, ite_true]
  let base := wordIdx * 8
  have hb0 : base < bs.usize := usize_base_lt base bs.usize h1 h2
  have hb1 : base + 1 < bs.usize := usize_offset_lt base bs.usize h1 h2 1 (by decide)
  have hb2 : base + 2 < bs.usize := usize_offset_lt base bs.usize h1 h2 2 (by decide)
  have hb3 : base + 3 < bs.usize := usize_offset_lt base bs.usize h1 h2 3 (by decide)
  have hb4 : base + 4 < bs.usize := usize_offset_lt base bs.usize h1 h2 4 (by decide)
  have hb5 : base + 5 < bs.usize := usize_offset_lt base bs.usize h1 h2 5 (by decide)
  have hb6 : base + 6 < bs.usize := usize_offset_lt base bs.usize h1 h2 6 (by decide)
  have hb7 : base + 7 < bs.usize := h1
  let s0 := usetByte bs base val.toUInt8
  let s1 := usetByte s0 (base + 1) (val >>> 8).toUInt8
  let s2 := usetByte s1 (base + 2) (val >>> 16).toUInt8
  let s3 := usetByte s2 (base + 3) (val >>> 24).toUInt8
  let s4 := usetByte s3 (base + 4) (val >>> 32).toUInt8
  let s5 := usetByte s4 (base + 5) (val >>> 40).toUInt8
  let s6 := usetByte s5 (base + 6) (val >>> 48).toUInt8
  let s7 := usetByte s6 (base + 7) (val >>> 56).toUInt8
  change (ugetByte s7 base |||
      (ugetByte s7 (base + 1) <<< 8) |||
      (ugetByte s7 (base + 2) <<< 16) |||
      (ugetByte s7 (base + 3) <<< 24) |||
      (ugetByte s7 (base + 4) <<< 32) |||
      (ugetByte s7 (base + 5) <<< 40) |||
      (ugetByte s7 (base + 6) <<< 48) |||
      (ugetByte s7 (base + 7) <<< 56)) = val
  have hs0 : s0.usize = bs.usize := usetByte_usize _ _ _
  have hs1 : s1.usize = bs.usize := (usetByte_usize _ _ _).trans hs0
  have hs2 : s2.usize = bs.usize := (usetByte_usize _ _ _).trans hs1
  have hs3 : s3.usize = bs.usize := (usetByte_usize _ _ _).trans hs2
  have hs4 : s4.usize = bs.usize := (usetByte_usize _ _ _).trans hs3
  have hs5 : s5.usize = bs.usize := (usetByte_usize _ _ _).trans hs4
  have hs6 : s6.usize = bs.usize := (usetByte_usize _ _ _).trans hs5
  have g7 : ugetByte s7 (base + 7) = (val >>> 56).toUInt8.toUInt64 :=
    ugetByte_usetByte_self s6 (base + 7) (val >>> 56).toUInt8 (hs6.symm ▸ hb7)
  have g6 : ugetByte s7 (base + 6) = (val >>> 48).toUInt8.toUInt64 := by
    rw [ugetByte_usetByte_ne s6 (base + 7) (base + 6) _
      (usize_offset_ne base h2 7 6 (by decide) (by decide) (by decide))]
    exact ugetByte_usetByte_self s5 (base + 6) (val >>> 48).toUInt8 (hs5.symm ▸ hb6)
  have g5 : ugetByte s7 (base + 5) = (val >>> 40).toUInt8.toUInt64 := by
    rw [ugetByte_usetByte_ne s6 (base + 7) (base + 5) _
      (usize_offset_ne base h2 7 5 (by decide) (by decide) (by decide))]
    rw [ugetByte_usetByte_ne s5 (base + 6) (base + 5) _
      (usize_offset_ne base h2 6 5 (by decide) (by decide) (by decide))]
    exact ugetByte_usetByte_self s4 (base + 5) (val >>> 40).toUInt8 (hs4.symm ▸ hb5)
  have g4 : ugetByte s7 (base + 4) = (val >>> 32).toUInt8.toUInt64 := by
    rw [ugetByte_usetByte_ne s6 (base + 7) (base + 4) _
      (usize_offset_ne base h2 7 4 (by decide) (by decide) (by decide))]
    rw [ugetByte_usetByte_ne s5 (base + 6) (base + 4) _
      (usize_offset_ne base h2 6 4 (by decide) (by decide) (by decide))]
    rw [ugetByte_usetByte_ne s4 (base + 5) (base + 4) _
      (usize_offset_ne base h2 5 4 (by decide) (by decide) (by decide))]
    exact ugetByte_usetByte_self s3 (base + 4) (val >>> 32).toUInt8 (hs3.symm ▸ hb4)
  have g3 : ugetByte s7 (base + 3) = (val >>> 24).toUInt8.toUInt64 := by
    rw [ugetByte_usetByte_ne s6 (base + 7) (base + 3) _
      (usize_offset_ne base h2 7 3 (by decide) (by decide) (by decide))]
    rw [ugetByte_usetByte_ne s5 (base + 6) (base + 3) _
      (usize_offset_ne base h2 6 3 (by decide) (by decide) (by decide))]
    rw [ugetByte_usetByte_ne s4 (base + 5) (base + 3) _
      (usize_offset_ne base h2 5 3 (by decide) (by decide) (by decide))]
    rw [ugetByte_usetByte_ne s3 (base + 4) (base + 3) _
      (usize_offset_ne base h2 4 3 (by decide) (by decide) (by decide))]
    exact ugetByte_usetByte_self s2 (base + 3) (val >>> 24).toUInt8 (hs2.symm ▸ hb3)
  have g2 : ugetByte s7 (base + 2) = (val >>> 16).toUInt8.toUInt64 := by
    rw [ugetByte_usetByte_ne s6 (base + 7) (base + 2) _
      (usize_offset_ne base h2 7 2 (by decide) (by decide) (by decide))]
    rw [ugetByte_usetByte_ne s5 (base + 6) (base + 2) _
      (usize_offset_ne base h2 6 2 (by decide) (by decide) (by decide))]
    rw [ugetByte_usetByte_ne s4 (base + 5) (base + 2) _
      (usize_offset_ne base h2 5 2 (by decide) (by decide) (by decide))]
    rw [ugetByte_usetByte_ne s3 (base + 4) (base + 2) _
      (usize_offset_ne base h2 4 2 (by decide) (by decide) (by decide))]
    rw [ugetByte_usetByte_ne s2 (base + 3) (base + 2) _
      (usize_offset_ne base h2 3 2 (by decide) (by decide) (by decide))]
    exact ugetByte_usetByte_self s1 (base + 2) (val >>> 16).toUInt8 (hs1.symm ▸ hb2)
  have g1 : ugetByte s7 (base + 1) = (val >>> 8).toUInt8.toUInt64 := by
    rw [ugetByte_usetByte_ne s6 (base + 7) (base + 1) _
      (usize_offset_ne base h2 7 1 (by decide) (by decide) (by decide))]
    rw [ugetByte_usetByte_ne s5 (base + 6) (base + 1) _
      (usize_offset_ne base h2 6 1 (by decide) (by decide) (by decide))]
    rw [ugetByte_usetByte_ne s4 (base + 5) (base + 1) _
      (usize_offset_ne base h2 5 1 (by decide) (by decide) (by decide))]
    rw [ugetByte_usetByte_ne s3 (base + 4) (base + 1) _
      (usize_offset_ne base h2 4 1 (by decide) (by decide) (by decide))]
    rw [ugetByte_usetByte_ne s2 (base + 3) (base + 1) _
      (usize_offset_ne base h2 3 1 (by decide) (by decide) (by decide))]
    rw [ugetByte_usetByte_ne s1 (base + 2) (base + 1) _
      (usize_offset_ne base h2 2 1 (by decide) (by decide) (by decide))]
    exact ugetByte_usetByte_self s0 (base + 1) (val >>> 8).toUInt8 (hs0.symm ▸ hb1)
  have g0 : ugetByte s7 base = val.toUInt8.toUInt64 := by
    rw [ugetByte_usetByte_ne s6 (base + 7) base _
      (usize_base_ne_offset base h2 7 (by decide) (by decide))]
    rw [ugetByte_usetByte_ne s5 (base + 6) base _
      (usize_base_ne_offset base h2 6 (by decide) (by decide))]
    rw [ugetByte_usetByte_ne s4 (base + 5) base _
      (usize_base_ne_offset base h2 5 (by decide) (by decide))]
    rw [ugetByte_usetByte_ne s3 (base + 4) base _
      (usize_base_ne_offset base h2 4 (by decide) (by decide))]
    rw [ugetByte_usetByte_ne s2 (base + 3) base _
      (usize_base_ne_offset base h2 3 (by decide) (by decide))]
    rw [ugetByte_usetByte_ne s1 (base + 2) base _
      (usize_base_ne_offset base h2 2 (by decide) (by decide))]
    rw [ugetByte_usetByte_ne s0 (base + 1) base _
      (usize_base_ne_offset base h2 1 (by decide) (by decide))]
    exact ugetByte_usetByte_self bs base val.toUInt8 hb0
  rw [g0, g1, g2, g3, g4, g5, g6, g7]
  exact wordLE_reconstruct val

theorem word_byte_disjoint (w1 w2 : USize)
    (hw1 : w1 * 8 ≤ w1 * 8 + 7) (hw2 : w2 * 8 ≤ w2 * 8 + 7)
    (hne : w1 * 8 ≠ w2 * 8)
    (i j : Nat) (hi : i ≤ 7) (hj : j ≤ 7) :
    w1 * 8 + OfNat.ofNat i ≠ w2 * 8 + OfNat.ofNat j := by
  intro heq
  have hnat := congrArg USize.toNat heq
  rw [usize_add_offset_toNat (w1 * 8) hw1 i hi,
      usize_add_offset_toNat (w2 * 8) hw2 j hj] at hnat
  have hm1 := usize_mul_eight_mod8 w1
  have hm2 := usize_mul_eight_mod8 w2
  have hbne : (w1 * 8).toNat ≠ (w2 * 8).toNat := by
    intro hbeq
    exact hne (USize.toNat_inj.mp hbeq)
  omega

theorem ugetByte_uset64LE_disjoint (bs : ByteArray) (w1 : USize) (val : UInt64)
    (hw2_idx : USize)
    (hdisj0 : w1 * 8 ≤ w1 * 8 + 7 → w1 * 8 ≠ hw2_idx)
    (hdisj1 : w1 * 8 ≤ w1 * 8 + 7 → w1 * 8 + 1 ≠ hw2_idx)
    (hdisj2 : w1 * 8 ≤ w1 * 8 + 7 → w1 * 8 + 2 ≠ hw2_idx)
    (hdisj3 : w1 * 8 ≤ w1 * 8 + 7 → w1 * 8 + 3 ≠ hw2_idx)
    (hdisj4 : w1 * 8 ≤ w1 * 8 + 7 → w1 * 8 + 4 ≠ hw2_idx)
    (hdisj5 : w1 * 8 ≤ w1 * 8 + 7 → w1 * 8 + 5 ≠ hw2_idx)
    (hdisj6 : w1 * 8 ≤ w1 * 8 + 7 → w1 * 8 + 6 ≠ hw2_idx)
    (hdisj7 : w1 * 8 ≤ w1 * 8 + 7 → w1 * 8 + 7 ≠ hw2_idx) :
    ugetByte (uset64LE bs w1 val) hw2_idx = ugetByte bs hw2_idx := by
  unfold uset64LE
  dsimp only
  cases h1 : decide (w1 * 8 + 7 < bs.usize) with
  | false =>
    have h1' : ¬ (w1 * 8 + 7 < bs.usize) := of_decide_eq_false h1
    simp only [h1', ite_false]
  | true =>
    have h1' : w1 * 8 + 7 < bs.usize := of_decide_eq_true h1
    simp only [h1', ite_true]
    cases h2 : decide (w1 * 8 ≤ w1 * 8 + 7) with
    | false =>
      have h2' : ¬ (w1 * 8 ≤ w1 * 8 + 7) := of_decide_eq_false h2
      simp only [h2', ite_false]
    | true =>
      have h2' : w1 * 8 ≤ w1 * 8 + 7 := of_decide_eq_true h2
      simp only [h2', ite_true]
      rw [ugetByte_usetByte_ne _ _ _ _ (hdisj7 h2')]
      rw [ugetByte_usetByte_ne _ _ _ _ (hdisj6 h2')]
      rw [ugetByte_usetByte_ne _ _ _ _ (hdisj5 h2')]
      rw [ugetByte_usetByte_ne _ _ _ _ (hdisj4 h2')]
      rw [ugetByte_usetByte_ne _ _ _ _ (hdisj3 h2')]
      rw [ugetByte_usetByte_ne _ _ _ _ (hdisj2 h2')]
      rw [ugetByte_usetByte_ne _ _ _ _ (hdisj1 h2')]
      rw [ugetByte_usetByte_ne _ _ _ _ (hdisj0 h2')]

theorem uget64LE_uset64LE_ne (bs : ByteArray) (w1 w2 : USize) (val : UInt64)
    (hne : w1 * 8 ≠ w2 * 8) :
    uget64LE (uset64LE bs w1 val) w2 = uget64LE bs w2 := by
  have hus : (uset64LE bs w1 val).usize = bs.usize := uset64LE_usize bs w1 val
  unfold uget64LE
  dsimp only
  rw [hus]
  cases hg1 : decide (w2 * 8 + 7 < bs.usize) with
  | false =>
    have hg1' : ¬ (w2 * 8 + 7 < bs.usize) := of_decide_eq_false hg1
    simp only [hg1', ite_false]
  | true =>
    have hg1' : w2 * 8 + 7 < bs.usize := of_decide_eq_true hg1
    simp only [hg1', ite_true]
    cases hg2 : decide (w2 * 8 ≤ w2 * 8 + 7) with
    | false =>
      have hg2' : ¬ (w2 * 8 ≤ w2 * 8 + 7) := of_decide_eq_false hg2
      simp only [hg2', ite_false]
    | true =>
      have hg2' : w2 * 8 ≤ w2 * 8 + 7 := of_decide_eq_true hg2
      simp only [hg2', ite_true]
      have hz0 : w2 * 8 + OfNat.ofNat 0 = w2 * 8 := by
        apply USize.toNat_inj.mp
        have h0 : (0 : USize).toNat = 0 := usize_ofNat_small 0 (by decide)
        rw [USize.toNat_add, h0, Nat.add_zero]
        exact Nat.mod_eq_of_lt (w2 * 8).toNat_lt_two_pow_numBits
      have hstep : ∀ (j : Nat) (hj : j ≤ 7),
          ugetByte (uset64LE bs w1 val) (w2 * 8 + OfNat.ofNat j) =
            ugetByte bs (w2 * 8 + OfNat.ofNat j) := by
        intro j hj
        apply ugetByte_uset64LE_disjoint
        · intro hw1
          have hd := word_byte_disjoint w1 w2 hw1 hg2' hne 0 j (by decide) hj
          have hz1 : w1 * 8 + OfNat.ofNat 0 = w1 * 8 := by
            apply USize.toNat_inj.mp
            have h0 : (0 : USize).toNat = 0 := usize_ofNat_small 0 (by decide)
            rw [USize.toNat_add, h0, Nat.add_zero]
            exact Nat.mod_eq_of_lt (w1 * 8).toNat_lt_two_pow_numBits
          rw [hz1] at hd
          exact hd
        · intro hw1
          exact word_byte_disjoint w1 w2 hw1 hg2' hne 1 j (by decide) hj
        · intro hw1
          exact word_byte_disjoint w1 w2 hw1 hg2' hne 2 j (by decide) hj
        · intro hw1
          exact word_byte_disjoint w1 w2 hw1 hg2' hne 3 j (by decide) hj
        · intro hw1
          exact word_byte_disjoint w1 w2 hw1 hg2' hne 4 j (by decide) hj
        · intro hw1
          exact word_byte_disjoint w1 w2 hw1 hg2' hne 5 j (by decide) hj
        · intro hw1
          exact word_byte_disjoint w1 w2 hw1 hg2' hne 6 j (by decide) hj
        · intro hw1
          exact word_byte_disjoint w1 w2 hw1 hg2' hne 7 j (by decide) hj
      have e0 : ugetByte (uset64LE bs w1 val) (w2 * 8) = ugetByte bs (w2 * 8) := by
        rw [← hz0]
        exact hstep 0 (by decide)
      rw [e0,
        hstep 1 (by decide),
        hstep 2 (by decide),
        hstep 3 (by decide),
        hstep 4 (by decide),
        hstep 5 (by decide),
        hstep 6 (by decide),
        hstep 7 (by decide)]

theorem wordIdx_mul8_ne (w1 w2 : USize)
    (hw1_bound : w1.toNat * 8 < 2 ^ System.Platform.numBits)
    (hw2_bound : w2.toNat * 8 < 2 ^ System.Platform.numBits)
    (hne : w1 ≠ w2) :
    w1 * 8 ≠ w2 * 8 := by
  intro heq
  have h8 : (8 : USize).toNat = 8 := usize_ofNat_small 8 (by decide)
  have hnat := congrArg USize.toNat heq
  rw [USize.toNat_mul, USize.toNat_mul, h8,
      Nat.mod_eq_of_lt hw1_bound, Nat.mod_eq_of_lt hw2_bound] at hnat
  have hwnat : w1.toNat = w2.toNat := by omega
  exact hne (USize.toNat_inj.mp hwnat)

theorem uget64LE_uset64LE_disjoint (bs : ByteArray) (w1 w2 : USize) (val : UInt64)
    (hw1_bound : w1.toNat * 8 < 2 ^ System.Platform.numBits)
    (hw2_bound : w2.toNat * 8 < 2 ^ System.Platform.numBits)
    (hne : w1 ≠ w2) :
    uget64LE (uset64LE bs w1 val) w2 = uget64LE bs w2 :=
  uget64LE_uset64LE_ne bs w1 w2 val (wordIdx_mul8_ne w1 w2 hw1_bound hw2_bound hne)

theorem storeLE_size (bs : ByteArray) (wordBase : USize) (v : U64x8) :
    (U64x8.storeLE bs wordBase v).size = bs.size := by
  simp only [U64x8.storeLE, uset64LE_size]

theorem setWord_size (bs : ByteArray) (r : PlanarSliceRange) (idx : USize) (val : UInt64) :
    (PlanarSliceRange.setWord bs r idx val).size = bs.size := by
  unfold PlanarSliceRange.setWord
  cases h : decide (idx < r.wordLen) with
  | false =>
    have h' : ¬ idx < r.wordLen := of_decide_eq_false h
    simp only [h', ite_false]
  | true =>
    have h' : idx < r.wordLen := of_decide_eq_true h
    simp only [h', ite_true, uset64LE_size]

theorem setVec8_size (bs : ByteArray) (r : PlanarSliceRange) (idx : USize) (v : U64x8) :
    (PlanarSliceRange.setVec8 bs r idx v).size = bs.size := by
  unfold PlanarSliceRange.setVec8
  cases h : (decide (idx + 8 ≤ r.wordLen) && decide (idx ≤ idx + 8)) with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
  | true =>
    simp only [ite_true, storeLE_size]

theorem getWord_setWord_self (bs : ByteArray) (r : PlanarSliceRange) (idx : USize) (val : UInt64)
    (hidx : idx < r.wordLen)
    (h1 : (r.wordOffset + idx) * 8 + 7 < bs.usize)
    (h2 : (r.wordOffset + idx) * 8 ≤ (r.wordOffset + idx) * 8 + 7) :
    PlanarSliceRange.getWord (PlanarSliceRange.setWord bs r idx val) r idx = val := by
  unfold PlanarSliceRange.getWord PlanarSliceRange.setWord
  simp only [hidx, ite_true]
  exact uget64LE_uset64LE_self bs (r.wordOffset + idx) val h1 h2

theorem getLsbD_not64 (x : BitVec 64) (k : Nat) (hk : k < 64) :
    (~~~x).getLsbD k = !x.getLsbD k := by
  change (BitVec.allOnes 64 ^^^ x).getLsbD k = !x.getLsbD k
  rw [BitVec.getLsbD_xor]
  have hones : ∀ j : Fin 64, (BitVec.allOnes 64).getLsbD j.val = true := by decide
  rw [hones ⟨k, hk⟩]
  cases x.getLsbD k
  · rfl
  · rfl

theorem bitMask64_toBitVec (a b i : UInt64) :
    (bitMask64 a b i).toBitVec =
      if b.toBitVec.getLsbD (i.toNat % 64) then a.toBitVec else 0 := by
  simp only [bitMask64, UInt64.toBitVec_and, UInt64.toBitVec_sub,
    UInt64.toBitVec_shiftRight, UInt64.toBitVec_ofNat]
  rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  cases h : b.toBitVec.getLsbD (i.toNat % 64)
  · simp [h]
  · simp [h]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [BitVec.getLsbD_and]
    change (a.toBitVec.getLsbD j && (BitVec.allOnes 64).getLsbD j) = _
    have bits : ∀ k : Fin 64, (BitVec.allOnes 64).getLsbD k.val = true := by decide
    rw [bits ⟨j, hj⟩]
    exact Bool.and_true _

theorem ternaryLogic64_0xD2_eq_chi (a b c : UInt64) :
    ternaryLogic64 a b c 0xD2 = (a ^^^ ((~~~b) &&& c)) := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [ternaryLogic64, UInt64.toBitVec_or, bitMask64_toBitVec]
  have hd0 : (0xD2 : UInt8).toUInt64.toBitVec.getLsbD ((0 : UInt64).toNat % 64) = false := by
    decide
  have hd1 : (0xD2 : UInt8).toUInt64.toBitVec.getLsbD ((1 : UInt64).toNat % 64) = true := by
    decide
  have hd2 : (0xD2 : UInt8).toUInt64.toBitVec.getLsbD ((2 : UInt64).toNat % 64) = false := by
    decide
  have hd3 : (0xD2 : UInt8).toUInt64.toBitVec.getLsbD ((3 : UInt64).toNat % 64) = false := by
    decide
  have hd4 : (0xD2 : UInt8).toUInt64.toBitVec.getLsbD ((4 : UInt64).toNat % 64) = true := by
    decide
  have hd5 : (0xD2 : UInt8).toUInt64.toBitVec.getLsbD ((5 : UInt64).toNat % 64) = false := by
    decide
  have hd6 : (0xD2 : UInt8).toUInt64.toBitVec.getLsbD ((6 : UInt64).toNat % 64) = true := by
    decide
  have hd7 : (0xD2 : UInt8).toUInt64.toBitVec.getLsbD ((7 : UInt64).toNat % 64) = true := by
    decide
  rw [hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7]
  have hz : (0 : BitVec 64).getLsbD k = false := BitVec.getLsbD_zero
  simp only [Bool.false_eq_true, ite_true, ite_false,
    UInt64.toBitVec_and, UInt64.toBitVec_not, UInt64.toBitVec_xor,
    BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor, hz]
  rw [getLsbD_not64 a.toBitVec k hk,
      getLsbD_not64 b.toBitVec k hk,
      getLsbD_not64 c.toBitVec k hk]
  cases a.toBitVec.getLsbD k
  · cases b.toBitVec.getLsbD k
    · cases c.toBitVec.getLsbD k
      · rfl
      · rfl
    · cases c.toBitVec.getLsbD k
      · rfl
      · rfl
  · cases b.toBitVec.getLsbD k
    · cases c.toBitVec.getLsbD k
      · rfl
      · rfl
    · cases c.toBitVec.getLsbD k
      · rfl
      · rfl

theorem bitMask64_eq_nativeSelect (a b i : UInt64) :
    bitMask64 a b i = LeanVmXmss.Model.Field.nativeSelect a b i := rfl

theorem clmul64_eq_nativeClmulLo (a b : UInt64) :
    clmul64 a b = LeanVmXmss.Model.Field.nativeClmulLo a b := rfl

theorem clmul64_refines_clmul (a b : K) :
    (clmul64 a b).toBitVec = (LeanVmXmss.Model.Field.clmul a b).setWidth 64 := by
  rw [clmul64_eq_nativeClmulLo]
  exact LeanVmXmss.Proofs.Field.nativeClmulLo_correct a b

theorem clmul64Hi_eq_nativeClmulHi (a b : UInt64) :
    clmul64Hi a b = LeanVmXmss.Model.Field.nativeClmulHi a b := by
  apply UInt64.eq_of_toBitVec_eq
  simp only [clmul64Hi, clmulHiOctet, bitMask64_eq_nativeSelect,
    LeanVmXmss.Model.Field.nativeClmulHi]
  change (LeanVmXmss.Model.Field.nativeSelect (a >>> 63) b 1 ^^^
      LeanVmXmss.Model.Field.nativeSelect (a >>> 62) b 2 ^^^
      LeanVmXmss.Model.Field.nativeSelect (a >>> 61) b 3 ^^^
      LeanVmXmss.Model.Field.nativeSelect (a >>> 60) b 4 ^^^
      LeanVmXmss.Model.Field.nativeSelect (a >>> 59) b 5 ^^^
      LeanVmXmss.Model.Field.nativeSelect (a >>> 58) b 6 ^^^
      LeanVmXmss.Model.Field.nativeSelect (a >>> 57) b 7 ^^^
      (LeanVmXmss.Model.Field.nativeSelect (a >>> 56) b 8 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 55) b 9 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 54) b 10 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 53) b 11 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 52) b 12 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 51) b 13 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 50) b 14 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 49) b 15) ^^^
      (LeanVmXmss.Model.Field.nativeSelect (a >>> 48) b 16 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 47) b 17 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 46) b 18 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 45) b 19 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 44) b 20 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 43) b 21 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 42) b 22 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 41) b 23) ^^^
      (LeanVmXmss.Model.Field.nativeSelect (a >>> 40) b 24 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 39) b 25 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 38) b 26 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 37) b 27 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 36) b 28 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 35) b 29 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 34) b 30 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 33) b 31) ^^^
      (LeanVmXmss.Model.Field.nativeSelect (a >>> 32) b 32 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 31) b 33 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 30) b 34 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 29) b 35 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 28) b 36 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 27) b 37 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 26) b 38 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 25) b 39) ^^^
      (LeanVmXmss.Model.Field.nativeSelect (a >>> 24) b 40 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 23) b 41 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 22) b 42 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 21) b 43 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 20) b 44 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 19) b 45 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 18) b 46 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 17) b 47) ^^^
      (LeanVmXmss.Model.Field.nativeSelect (a >>> 16) b 48 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 15) b 49 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 14) b 50 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 13) b 51 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 12) b 52 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 11) b 53 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 10) b 54 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 9) b 55) ^^^
      (LeanVmXmss.Model.Field.nativeSelect (a >>> 8) b 56 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 7) b 57 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 6) b 58 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 5) b 59 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 4) b 60 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 3) b 61 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 2) b 62 ^^^
       LeanVmXmss.Model.Field.nativeSelect (a >>> 1) b 63)).toBitVec = _
  simp only [UInt64.toBitVec_xor, BitVec.xor_assoc]

theorem clmul64Hi_refines_clmul (a b : K) :
    (clmul64Hi a b).toBitVec = ((LeanVmXmss.Model.Field.clmul a b >>> 64).setWidth 64) := by
  rw [clmul64Hi_eq_nativeClmulHi]
  exact LeanVmXmss.Proofs.Field.nativeClmulHi_correct a b

theorem primBaseMul_eq_mul (a b : UInt64) :
    primBaseMul a b = LeanVmXmss.Model.Field.mul a b := by
  rw [primBaseMul, clmul64_eq_nativeClmulLo, clmul64Hi_eq_nativeClmulHi]
  exact LeanVmXmss.Proofs.Field.nativeMul_correct a b

theorem primBaseMul_refines_spec (a b : K) :
    primBaseMul a b = LeanVmXmss.Spec.Field.mul a b :=
  (primBaseMul_eq_mul a b).trans (LeanVmXmss.Proofs.Field.mul_refines_spec a b)

theorem karatsuba6_eq_polynomial (f : UInt64 → UInt64 → UInt64)
    (hleft : ∀ x y z, f (x ^^^ y) z = f x z ^^^ f y z)
    (hright : ∀ x y z, f x (y ^^^ z) = f x y ^^^ f x z)
    (a b : E) :
    (let p0 := f a.c0 b.c0
     let p1 := f a.c1 b.c1
     let p2 := f a.c2 b.c2
     let e1 := f (a.c0 ^^^ a.c1) (b.c0 ^^^ b.c1) ^^^ p0 ^^^ p1
     let e2 := f (a.c0 ^^^ a.c2) (b.c0 ^^^ b.c2) ^^^ p0 ^^^ p2 ^^^ p1
     let e3 := f (a.c1 ^^^ a.c2) (b.c1 ^^^ b.c2) ^^^ p1 ^^^ p2
     (⟨p0 ^^^ e3, e1 ^^^ e3 ^^^ p2, e2 ^^^ p2⟩ : E)) =
    (let p0 := f a.c0 b.c0
     let p1 := f a.c0 b.c1 ^^^ f a.c1 b.c0
     let p2 := f a.c0 b.c2 ^^^ f a.c1 b.c1 ^^^ f a.c2 b.c0
     let p3 := f a.c1 b.c2 ^^^ f a.c2 b.c1
     let p4 := f a.c2 b.c2
     (⟨p0 ^^^ p3, p1 ^^^ p3 ^^^ p4, p2 ^^^ p4⟩ : E)) := by
  dsimp only
  simp only [hleft, hright]
  congr 1
  · apply UInt64.eq_of_toBitVec_eq
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [UInt64.toBitVec_xor, BitVec.getLsbD_xor]
    simp [Bool.xor_left_comm, Bool.xor_comm]
  · apply UInt64.eq_of_toBitVec_eq
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [UInt64.toBitVec_xor, BitVec.getLsbD_xor]
    simp [Bool.xor_left_comm, Bool.xor_comm]
  · apply UInt64.eq_of_toBitVec_eq
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [UInt64.toBitVec_xor, BitVec.getLsbD_xor]
    simp [Bool.xor_left_comm, Bool.xor_comm]

theorem primKaratsubaMul_eq_karatsubaMul (a b : E) :
    primKaratsubaMul a b = LeanVmXmss.Model.Field.karatsubaMul a b := by
  simp only [primKaratsubaMul, LeanVmXmss.Model.Field.karatsubaMul, primBaseMul_eq_mul]

theorem primKaratsubaMul_eq_polynomialMul (a b : E) :
    primKaratsubaMul a b = LeanVmXmss.Model.Field.polynomialMul a b :=
  (primKaratsubaMul_eq_karatsubaMul a b).trans
    (LeanVmXmss.Proofs.Field.karatsuba_refines_polynomial a b)

theorem primKaratsubaMul_refines_spec (a b : E) :
    primKaratsubaMul a b = LeanVmXmss.Spec.Field.emul a b :=
  (primKaratsubaMul_eq_karatsubaMul a b).trans
    (LeanVmXmss.Proofs.Field.karatsuba_refines_spec a b)

end LeanVmXmss.Proofs.Prim
