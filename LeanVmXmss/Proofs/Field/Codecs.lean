import Proofs.Field.ExtensionInverse

namespace LeanVmXmss.Proofs.Field

open Spec.Field (K E)
open Model.Field

set_option maxRecDepth 20000
set_option maxHeartbeats 200000

def bytesValue : List UInt8 → Nat :=
  List.foldr (fun b prev => b.toNat + 256 * prev) 0

@[simp] theorem bytesValue.nil : bytesValue [] = 0 := rfl

@[simp] theorem bytesValue.cons (b : UInt8) (bs : List UInt8) :
    bytesValue (b :: bs) = b.toNat + 256 * bytesValue bs := rfl

theorem bytesValue_bound (bs : List UInt8) : bytesValue bs < 256^bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    have hb := b.toNat_lt
    simp only [bytesValue.cons, List.length_cons, Nat.pow_succ]
    omega

theorem bytesValue_digit (bs : List UInt8) (i : Nat) (hi : i < bs.length) :
    bytesValue bs / 256^i % 256 = bs[i].toNat := by
  induction bs generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero =>
      have hb := b.toNat_lt
      simp only [bytesValue.cons, Nat.pow_zero, Nat.div_one, List.getElem_cons_zero]
      omega
    | succ i =>
      have hb := b.toNat_lt
      have hd : (b.toNat + 256 * bytesValue bs) / 256 = bytesValue bs := by omega
      rw [bytesValue.cons, Nat.pow_succ', ← Nat.div_div_eq_div_mul, hd]
      exact ih i (by simpa using hi)

theorem readLimb_value (bs : List UInt8) (h : bs.length = 8) :
    (readLimb ⟨bs.toArray⟩ 0).toNat = bytesValue bs := by
  have hb := bytesValue_bound bs
  have he : ∃ b0 b1 b2 b3 b4 b5 b6 b7, bs = [b0,b1,b2,b3,b4,b5,b6,b7] := by
    match bs with
    | [b0,b1,b2,b3,b4,b5,b6,b7] => exact ⟨b0,b1,b2,b3,b4,b5,b6,b7,rfl⟩
    | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] | [_,_,_,_,_,_] | [_,_,_,_,_,_,_] | _::_::_::_::_::_::_::_::_::_ => simp_all
  obtain ⟨b0,b1,b2,b3,b4,b5,b6,b7,rfl⟩ := he
  have heq : (readLimb ⟨[b0,b1,b2,b3,b4,b5,b6,b7].toArray⟩ 0).toNat =
      bytesValue [b0,b1,b2,b3,b4,b5,b6,b7] % 2^64 := by
    simp [readLimb, bytesValue, Nat.shiftLeft_eq, Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc, Nat.mul_comm]
  rw [heq, Nat.mod_eq_of_lt (by simpa using hb)]

theorem encode_value (bs : List UInt8) (h : bs.length = 8) :
    encodeBytesK (UInt64.ofNat (bytesValue bs)) = ⟨bs.toArray⟩ := by
  have hb : bytesValue bs < 2^64 := by simpa [h] using bytesValue_bound bs
  apply ByteArray.ext
  apply Array.ext
  · simp [encodeBytesK, h]
  · intro i hi hj
    have hil : i < bs.length := by simpa using hj
    have hd := bytesValue_digit bs i hil
    have hn : (UInt64.ofNat (bytesValue bs)).toNat = bytesValue bs := Nat.mod_eq_of_lt hb
    have hie : i < 8 := by omega
    simp only [encodeBytesK]
    apply UInt8.toNat_inj.mp
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [hn, Nat.shiftRight_eq_div_pow] using hd

theorem encodeBytesK_decodeBytesK (b : ByteArray) (a : K) (h : decodeBytesK? b = some a) : encodeBytesK a = b := by
  have hl : b.size = 8 := by
    by_cases hn : b.size = 8
    · exact hn
    · simp [decodeBytesK?, hn] at h
  have ha : a = readLimb b 0 := by simpa [decodeBytesK?, hl] using h.symm
  rw [ha]
  have hl' : b.data.toList.length = 8 := by simpa only [Array.length_toList, ByteArray.size] using hl
  have hv := readLimb_value b.data.toList hl'
  have he := encode_value b.data.toList hl'
  have hr : readLimb b 0 = UInt64.ofNat (bytesValue b.data.toList) := by
    apply UInt64.toNat_inj.mp
    have hb : bytesValue b.data.toList < 2^64 := by simpa only [hl'] using bytesValue_bound b.data.toList
    have hn : (UInt64.ofNat (bytesValue b.data.toList)).toNat = bytesValue b.data.toList := Nat.mod_eq_of_lt hb
    rw [hn]
    cases b
    simpa only [Array.toArray_toList] using hv
  rw [hr]
  simpa using he

def byteSlice (b : ByteArray) (offset count : Nat) : ByteArray :=
  ⟨((b.data.toList.drop offset).take count).toArray⟩

theorem readLimb_extract (b : ByteArray) (offset : Nat) :
    readLimb (byteSlice b offset 8) 0 = readLimb b offset := by
  simp only [readLimb, byteSlice, List.toList_toArray]
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_drop]

theorem encode_readLimb_extract (b : ByteArray) (offset : Nat) (h : offset + 8 ≤ b.size) :
    encodeBytesK (readLimb b offset) = byteSlice b offset 8 := by
  apply encodeBytesK_decodeBytesK
  have hb : b.data.size = b.size := rfl
  have hl : (byteSlice b offset 8).size = 8 := by
    simp only [byteSlice, ByteArray.size, List.size_toArray, List.length_take, List.length_drop, Array.length_toList]
    omega
  simp only [decodeBytesK?, hl, ↓reduceIte, readLimb_extract b offset]

theorem encodeBytesE_decodeBytesE (b : ByteArray) (a : E) (h : decodeBytesE? b = some a) : encodeBytesE a = b := by
  have hl : b.size = 24 := by
    by_cases hn : b.size = 24
    · exact hn
    · simp [decodeBytesE?, hn] at h
  have ha : a = ⟨readLimb b 0, readLimb b 8, readLimb b 16⟩ := by
    simpa [decodeBytesE?, hl] using h.symm
  rw [ha]
  simp only [encodeBytesE]
  rw [encode_readLimb_extract b 0 (by omega), encode_readLimb_extract b 8 (by omega),
    encode_readLimb_extract b 16 (by omega)]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp only [ByteArray.data_append, Array.toList_append, byteSlice, List.drop_zero]
  have hb : b.data.toList.length = 24 := hl
  have hlast : (b.data.toList.drop 16).take 8 = b.data.toList.drop 16 :=
    List.take_of_length_le (by simp only [List.length_drop, hb]; decide)
  rw [hlast, List.append_assoc]
  have hd : b.data.toList.drop 16 = (b.data.toList.drop 8).drop 8 := by simp only [List.drop_drop]
  rw [hd, List.take_append_drop, List.take_append_drop]

end LeanVmXmss.Proofs.Field
