import Model.Transcript.Scalar
import Proofs.Merkle.Refinement

namespace LeanVmXmss.Proofs.Transcript

open Spec.Field (E)

theorem duplex_refines_spec (s : Spec.Transcript.Sponge) :
    Model.Transcript.duplex s = Spec.Transcript.duplex s := rfl

theorem absorb_refines_spec (s : Spec.Transcript.Sponge) (x : E) (tag : UInt64) :
    Model.Transcript.absorb s x tag = Spec.Transcript.absorb s x tag := rfl

theorem challenge_refines_spec (s : Spec.Transcript.Sponge) :
    Model.Transcript.challenge s = Spec.Transcript.challenge s := rfl

theorem pow_check_sound (s : Spec.Transcript.Sponge) (n : E) (bits : Nat)
    (nonzero : bits ≠ 0) (h : (Model.Transcript.verifyPow s n bits).1 = true) :
    Spec.Transcript.powBitsOk s n bits = true := by
  simpa [Model.Transcript.verifyPow, Spec.Transcript.verifyPow, Spec.Transcript.powBitsOk, nonzero] using h

theorem add_scalar_wire_order (s : Spec.Transcript.ProverState) (x : E) :
    (Model.Transcript.addScalar s x).stream = s.stream.push x := rfl

theorem add_scalar_binding (s : Spec.Transcript.ProverState) (x : E) :
    (Model.Transcript.addScalar s x).sponge = Spec.Transcript.observe s.sponge x := rfl

theorem search_nonce_sound (s : Spec.Transcript.Sponge) (bits fuel : Nat) (start nonce : UInt64)
    (h : Spec.Transcript.searchNonce s bits fuel start = some nonce) :
    Spec.Transcript.powBitsOk s ⟨nonce, 0, 0⟩ bits = true := by
  induction fuel generalizing start with
  | zero => simp [Spec.Transcript.searchNonce] at h
  | succ fuel ih =>
    simp only [Spec.Transcript.searchNonce] at h
    split at h
    next good =>
      cases h
      exact good
    next => exact ih _ h

theorem zero_bits_canonical (s : Spec.Transcript.Sponge) (n : E)
    (h : (Spec.Transcript.verifyPow s n 0).1 = true) :
    n.c0 = 0 ∧ n.c1 = 0 ∧ n.c2 = 0 := by
  exact of_decide_eq_true h

theorem root_wire_order (s : Spec.Transcript.ProverState) (d : ByteArray) :
    (Model.Transcript.addRoot s d).stream =
    (s.stream.push (Spec.Merkle.hashToScalars d).1).push (Spec.Merkle.hashToScalars d).2 := rfl

theorem hint_does_not_absorb (s : Spec.Transcript.ProverState) (b : ByteArray) :
    (Model.Transcript.hintMerkle s b).sponge = s.sponge := rfl

end LeanVmXmss.Proofs.Transcript
