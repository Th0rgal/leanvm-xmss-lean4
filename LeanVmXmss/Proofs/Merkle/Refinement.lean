import Model.Merkle.Scalar
import Proofs.Keccak.Refinement

namespace LeanVmXmss.Proofs.Merkle

theorem hashToScalars_refines_spec (b : ByteArray) :
    Model.Merkle.hashToScalars b = Spec.Merkle.hashToScalars b := rfl

theorem compress_refines_spec (l r : Spec.Merkle.Digest) :
    Model.Merkle.compress l r = Spec.Merkle.compress l r := rfl

theorem leaf_refines_spec (row : Array UInt64) (n : Nat) :
    Model.Merkle.hashRow row n = Spec.Merkle.hashRow row n := rfl

theorem path_sound (root leaf : Spec.Merkle.Digest) (index : Nat) (siblings : List Spec.Merkle.Digest)
    (h : Model.Merkle.verifyPath root leaf index siblings = true) :
    Spec.Merkle.pathRoot index leaf siblings = root := by
  have p : index < 2^siblings.length ∧ Spec.Merkle.pathRoot index leaf siblings = root := of_decide_eq_true h
  exact p.2

theorem path_step (i : Nat) (leaf sibling : Spec.Merkle.Digest) (rest : List Spec.Merkle.Digest) :
    Spec.Merkle.pathRoot i leaf (sibling :: rest) =
    Spec.Merkle.pathRoot (i / 2)
      (if i % 2 == 0 then Spec.Merkle.compress leaf sibling else Spec.Merkle.compress sibling leaf) rest := rfl

end LeanVmXmss.Proofs.Merkle
