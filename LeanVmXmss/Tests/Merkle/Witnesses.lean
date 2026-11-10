import Proofs.Merkle.Refinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LeanVmXmss.Tests.Merkle

def posWitness : Spec.Field.E × Spec.Field.E :=
  Model.Merkle.hashToScalars (Spec.Keccak.wordsBytes #[1, 2, 3, 4])

theorem scalar_encoding_witness : posWitness.1.c2 = 0 ∧ posWitness.2.c2 = 0 := by decide

def negWitness : ByteArray :=
  ByteArray.append (Spec.Merkle.digestBytes (Spec.Merkle.toDigest (Spec.Keccak.wordBytes 2)))
  (Spec.Merkle.digestBytes (Spec.Merkle.toDigest (Spec.Keccak.wordBytes 1)))

theorem swapped_children_preimage_witness :
    (#[2, 1] : Array UInt64)[0]! ≠ (#[1, 2] : Array UInt64)[0]! := by decide

theorem zero_prefix_witness (row : Array UInt64) (n : Nat) :
    Spec.Merkle.leafImage row n = Spec.Keccak.wordsBytes (Array.replicate (n - row.size) 0 ++ row) := rfl

end LeanVmXmss.Tests.Merkle
