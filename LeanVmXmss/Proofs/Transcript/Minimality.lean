import Spec.Transcript.Basic

namespace LeanVmXmss.Proofs.Transcript

open Spec.Transcript

def advance (count : Nat) : UInt64 → UInt64 :=
  Nat.rec (fun n => n) (fun _ previous n => previous (n + 1)) count

theorem search_first_success (s : Sponge) (bits fuel : Nat) (start nonce : UInt64)
    (h : searchNonce s bits fuel start = some nonce) :
    ∃ k, k < fuel ∧ nonce = advance k start ∧
      powBitsOk s ⟨nonce, 0, 0⟩ bits = true ∧
      ∀ j, j < k → powBitsOk s ⟨advance j start, 0, 0⟩ bits = false := by
  induction fuel generalizing start with
  | zero => simp [searchNonce] at h
  | succ fuel ih =>
    simp only [searchNonce] at h
    split at h
    next good =>
      cases h
      exact ⟨0, by omega, rfl, good, by intro j hj; omega⟩
    next bad =>
      obtain ⟨k, hk, hn, good, before⟩ := ih (start + 1) h
      refine ⟨k + 1, by omega, ?_, good, ?_⟩
      · simpa [advance] using hn
      · intro j hj
        cases j with
        | zero => exact Bool.eq_false_iff.mpr bad
        | succ j => exact before j (by omega)

theorem zero_bits_grinding_nonce (s : Sponge) (fuel : Nat) :
    (powGrinding s 0 fuel).map Prod.fst = some 0 := by
  rfl

end LeanVmXmss.Proofs.Transcript
