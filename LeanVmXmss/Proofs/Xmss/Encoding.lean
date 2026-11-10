import Spec.Xmss.Encoding

namespace LeanVmXmss.Proofs.Xmss

open Spec.Xmss

theorem range_eight : Array.range 8 = #[0, 1, 2, 3, 4, 5, 6, 7] := by
  rfl

theorem byte_get_data (a : ByteArray) (i : Nat) : a[i]! = a.data[i]! := by
  by_cases h : i < a.size
  · rw [getElem!_pos a i h, getElem!_pos a.data i (by simpa using h)]
    rfl
  · rw [getElem!_neg a i h, getElem!_neg a.data i (by simpa using h)]

theorem low_byte_bits (v : BitVec 64) (i : Nat) :
    (BitVec.setWidth 64 (BitVec.setWidth 8 v)).getLsbD i = (decide (i < 8) && v.getLsbD i) := by
  change (v.toNat % 2^8).testBit i = _
  exact Nat.testBit_mod_two_pow _ _ _

theorem low_nat_byte (v i : Nat) :
    (v % (256#64).toNat).testBit i = (decide (i < 8) && v.testBit i) :=
  Nat.testBit_mod_two_pow v 8 i

theorem sub_byte_bound (i k : Nat) : i - k < 8 ↔ i < k + 8 := by
  constructor
  · intro h
    omega
  · intro h
    omega

theorem nat_byte_bit (v i : Nat) : (v % 256).testBit i = (decide (i < 8) && v.testBit i) :=
  Nat.testBit_mod_two_pow v 8 i

theorem nat_word_bit (v i : Nat) :
    (v % 18446744073709551616).testBit i = (decide (i < 64) && v.testBit i) :=
  Nat.testBit_mod_two_pow v 64 i

theorem byte_high_bit (v : UInt8) (i : Nat) (h : 8 ≤ i) : v.toNat.testBit i = false := by
  apply Nat.testBit_lt_two_pow
  exact Nat.lt_of_lt_of_le v.toNat_lt (Nat.pow_le_pow_right (by decide) h)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem pack_cell_bytes (x : Spec.Field.E) (canonical : x.c2 = 0) :
    packCell (cellBytes x) = x := by
  cases x with
  | mk a b c =>
    simp only at canonical
    subst c
    simp only [packCell, cellBytes, readLE, writeLE, range_eight]
    congr 1 <;> apply UInt64.toBitVec_inj.mp <;>
      apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp [List.range_succ, byte_get_data, ByteArray.data_append,
        UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
        BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
      <;> simp only [BitVec.getLsbD, BitVec.toNat_umod, BitVec.toNat_ushiftRight]
      <;> simp only [low_nat_byte, Nat.testBit_shiftRight]
      <;> (by_cases h8 : i < 8
        <;> by_cases h16 : i < 16
        <;> by_cases h24 : i < 24
        <;> by_cases h32 : i < 32
        <;> by_cases h40 : i < 40
        <;> by_cases h48 : i < 48
        <;> by_cases h56 : i < 56 <;>
        first | omega | (simp [sub_byte_bound, *] <;> (congr 1 <;> omega)))

theorem cell_bytes_size (x : Spec.Field.E) : (cellBytes x).size = 16 := by
  simp [cellBytes, writeLE, ByteArray.size]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem cell_bytes_pack (bytes : ByteArray) (length : bytes.size = 16) :
    cellBytes (packCell bytes) = bytes := by
  apply ByteArray.ext_getElem (by rw [cell_bytes_size, length])
  intro i hi hj
  have bound : i < 16 := by omega
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
      i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨
      i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply UInt8.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq
    intro j hjbit
    have bitCases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
    rcases bitCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [cellBytes, packCell, writeLE, readLE, range_eight]
      simp [List.range_succ,
        ByteArray.getElem_eq_getElem_data, ByteArray.data_append,
        BitVec.getLsbD]
      <;> simp (disch := omega) [nat_byte_bit, nat_word_bit, Nat.testBit_or,
        Nat.testBit_shiftRight, Nat.testBit_shiftLeft, byte_high_bit,
        getElem!_pos, ByteArray.getElem_eq_getElem_data, length]

end LeanVmXmss.Proofs.Xmss
