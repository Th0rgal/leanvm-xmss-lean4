import Proofs.Merkle.Contracts
import Proofs.Transcript.Replay

namespace LeanVmXmss.Tests.Merkle.Pruned

def rows : Array (Array UInt64) := #[#[1, 0], #[2, 11], #[3, 22], #[4, 33]]
def queries : Array Nat := #[3, 0, 1, 0]
def batch : Spec.Merkle.PrunedMerklePaths :=
  (Spec.Merkle.openPruned 2 5 rows queries).getD default
def root : Spec.Merkle.Digest :=
  Spec.Merkle.treeRoot (Spec.Merkle.build (rows.map fun row => Spec.Merkle.hashRow row 5))

def run : IO Unit := do
  let check := fun (label : String) (ok : Bool) =>
    if ok then IO.println label else throw (IO.userError label)
  check "shared_siblings_count" (batch.siblings.size == 1)
  check "expanded_paths_order"
    (((Spec.Merkle.expandPruned batch 2 queries 2 5).map fun r => r.2.map (·.index)) == some queries)
  check "pruned_accepts" (Spec.Merkle.verifyPruned root batch 2 queries 2 5)
  check "extra_sibling_rejected"
    (Spec.Merkle.expandPruned {batch with siblings := batch.siblings.push root} 2 queries 2 5).isNone
  check "missing_sibling_rejected"
    (Spec.Merkle.expandPruned {batch with siblings := #[]} 2 queries 2 5).isNone
  check "invalid_query_rejected" (Spec.Merkle.expandPruned batch 2 #[4] 2 5).isNone
  check "narrow_leaf_rejected" (Spec.Merkle.expandPruned batch 2 queries 2 1).isNone
  let verifier := Spec.Transcript.verifierNew ⟨#[], #[batch]⟩ ByteArray.empty ByteArray.empty
  check "replay_merkle_finish"
    (((Spec.Transcript.merkle verifier root 2 queries 2 5).bind fun r =>
      (Spec.Transcript.finish r.2).map Array.size) == some 4)
  check "replay_unread_rejected" (Spec.Transcript.finish verifier).isNone

end LeanVmXmss.Tests.Merkle.Pruned

#eval LeanVmXmss.Tests.Merkle.Pruned.run
