import Model.KeccakGkr.Flat
namespace LeanVmXmss.Proofs.KeccakGkr
open Model.KeccakGkr
theorem uget_eq_get (b : ByteArray) (i : USize) (h : i.toNat < b.size) :
    b.uget i h = b[i.toNat]'h := by
  cases b
  rfl


theorem readWordLE_refines_reference (bytes : ByteArray) (index : Nat) :
    readWordLE bytes index = readWordLEReference bytes index := by
  by_cases hb : 8 * index + 7 < bytes.size
  · by_cases hs : bytes.size < 2^32
    · have hsize : bytes.size < USize.size := Nat.lt_of_lt_of_le hs USize.le_size
      have byte_eq (k : Nat) (hk : k ≤ 7)
          (hi : (USize.ofNat (8 * index) + USize.ofNat k).toNat < bytes.size) :
          bytes.uget (USize.ofNat (8 * index) + USize.ofNat k) hi =
            bytes[8 * index + k]'(by omega) := by
        rw [uget_eq_get]
        simp only [wordOffsetNatEq (8 * index) k (by omega)]
      simp only [readWordLE, hb, hs, dite_true]
      simp only [readWordLEReference, hb, dite_true]
      simp only [byte_eq 0 (by decide), byte_eq 1 (by decide),
        byte_eq 2 (by decide), byte_eq 3 (by decide), byte_eq 4 (by decide),
        byte_eq 5 (by decide), byte_eq 6 (by decide), byte_eq 7 (by decide), Nat.add_zero]
    · simp only [readWordLE, hb, hs, dite_true, dite_false]
  · simp only [readWordLE, readWordLEReference, hb, dite_false]
end LeanVmXmss.Proofs.KeccakGkr
