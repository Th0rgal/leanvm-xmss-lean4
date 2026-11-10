import Model.Aggregate.Wire
import Proofs.Pcs.Whir
import Proofs.Layout.Basic
import Proofs.Transcript.Registers

namespace LeanVmXmss.Proofs.Aggregate.Wire

open Spec.Field (K E)

theorem toBytes_refines :
    Model.Aggregate.Wire.EthereumProof.toBytes = Spec.Aggregate.Wire.EthereumProof.toBytes := rfl

theorem toBytesWithoutPubkeys_refines :
    Model.Aggregate.Wire.EthereumProof.toBytesWithoutPubkeys =
      Spec.Aggregate.Wire.EthereumProof.toBytesWithoutPubkeys := rfl

theorem proofSize_refines :
    Model.Aggregate.Wire.EthereumProof.proofSize = Spec.Aggregate.Wire.EthereumProof.proofSize := rfl

theorem fromBytes_refines :
    Model.Aggregate.Wire.EthereumProof.fromBytes = Spec.Aggregate.Wire.EthereumProof.fromBytes := rfl

theorem fromBytesWithoutPubkeys_refines :
    Model.Aggregate.Wire.EthereumProof.fromBytesWithoutPubkeys =
      Spec.Aggregate.Wire.EthereumProof.fromBytesWithoutPubkeys := rfl

theorem listSplit_refines :
    Model.Aggregate.Wire.listSplit = Spec.Aggregate.Wire.listSplit := rfl

theorem claimCells_refines (p : Spec.Aggregate.Wire.SignaturePair) :
    Model.Aggregate.Wire.claimCells p = Spec.Aggregate.Wire.claimCells p := by
  simp only [Model.Aggregate.Wire.claimCells, Spec.Aggregate.Wire.claimCells,
    Proofs.Layout.readWordLE_eq_wordAt]

theorem claimCells_eq_spec :
    Model.Aggregate.Wire.claimCells = Spec.Aggregate.Wire.claimCells := by
  funext p
  exact claimCells_refines p

theorem claimListDigest_refines (claims : Array Spec.Aggregate.Wire.SignaturePair) :
    Model.Aggregate.Wire.claimListDigest claims = Spec.Aggregate.Wire.claimListDigest claims := by
  simp only [Model.Aggregate.Wire.claimListDigest, Spec.Aggregate.Wire.claimListDigest,
    claimCells_eq_spec, Proofs.Layout.wordsBytesFast_refines_spec,
    Proofs.Layout.keccak256Fast_refines_spec]

private theorem register_sample_init_fst (iv root : ByteArray) :
    (Model.Transcript.Registers.sample (Model.Transcript.Registers.init iv root)).1 =
      (Spec.Transcript.challenge (Spec.Transcript.init iv root)).1 := by
  have sample := congrArg Prod.fst
    (Proofs.Transcript.Registers.sample_refines (Model.Transcript.Registers.init iv root))
  rw [Proofs.Transcript.Registers.init_refines iv root] at sample
  exact sample

theorem daDigest_refines (root : Option ByteArray) :
    Model.Aggregate.Wire.daDigest root = Spec.Aggregate.Wire.daDigest root := by
  cases root with
  | none => rfl
  | some root =>
    simp only [Model.Aggregate.Wire.daDigest, Spec.Aggregate.Wire.daDigest,
      Proofs.Layout.keccak256Fast_refines_spec, register_sample_init_fst,
      Spec.Merkle.compress, Spec.Merkle.hashLeaf]

theorem statementDigest_refines (seed xmssDigest sphincsDigest : E × E) (da : ByteArray)
    (defer : Spec.Aggregate.Wire.DeferredClaim) :
    Model.Aggregate.Wire.statementDigest seed xmssDigest sphincsDigest da defer =
      Spec.Aggregate.Wire.statementDigest seed xmssDigest sphincsDigest da defer := by
  simp only [Model.Aggregate.Wire.statementDigest, Spec.Aggregate.Wire.statementDigest,
    Proofs.Layout.wordsBytesFast_refines_spec, Proofs.Layout.keccak256Fast_refines_spec]

theorem ethereumProof_statement_refines (seed : E × E)
    (proof : Spec.Aggregate.Wire.EthereumProof) :
    Model.Aggregate.Wire.EthereumProof.statement seed proof =
      Spec.Aggregate.Wire.EthereumProof.statement seed proof := by
  simp only [Model.Aggregate.Wire.EthereumProof.statement,
    Spec.Aggregate.Wire.EthereumProof.statement, claimListDigest_refines,
    daDigest_refines, statementDigest_refines]

theorem signerSetOk_of_fromBytes (bytes : ByteArray) (v : E)
    (proof : Spec.Aggregate.Wire.EthereumProof)
    (h : Spec.Aggregate.Wire.EthereumProof.fromBytes bytes v = some proof) :
    Spec.Aggregate.Wire.signerSetOk proof.claims = true := by
  dsimp only [Spec.Aggregate.Wire.EthereumProof.fromBytes, Bind.bind, Option.bind] at h
  cases hc : Spec.Aggregate.Wire.Cursor.claims ⟨bytes, 0⟩ with
  | none =>
    rw [hc] at h
    cases h
  | some p1 =>
    rw [hc] at h
    dsimp only at h
    cases hcore : p1.2.core with
    | none =>
      rw [hcore] at h
      cases h
    | some p2 =>
      rw [hcore] at h
      dsimp only at h
      cases hp : decide (p2.2.2.2.pos = bytes.size) with
      | false =>
        rw [hp] at h
        cases h
      | true =>
        rw [hp] at h
        dsimp only [ite_true, Spec.Aggregate.Wire.fromParts] at h
        cases hs : Spec.Aggregate.Wire.signerSetOk p1.1 with
        | false =>
          rw [hs] at h
          cases h
        | true =>
          rw [hs] at h
          injection h with hEq
          rw [← hEq]
          exact hs

theorem listSplit_reconstructs (n : Nat) (hn : 0 < n) :
    let parts := Spec.Aggregate.Wire.listSplit n
    parts.getD 0 0 * Spec.Aggregate.Wire.claimBig +
      parts.getD 1 0 * Spec.Aggregate.Wire.claimGroup +
      parts.getD 2 0 = n := by
  cases n with
  | zero => cases hn
  | succ m =>
    have hparts : Spec.Aggregate.Wire.listSplit (m + 1) =
        #[(m + 1) / (17 * 8), (m + 1) % (17 * 8) / 17, (m + 1) % (17 * 8) % 17] := rfl
    dsimp only [Spec.Aggregate.Wire.claimBig, Spec.Aggregate.Wire.bigGroups,
      Spec.Aggregate.Wire.claimGroup]
    rw [hparts]
    have h0 : #[(m + 1) / (17 * 8), (m + 1) % (17 * 8) / 17, (m + 1) % (17 * 8) % 17].getD 0 0 =
      (m + 1) / (17 * 8) := rfl
    have h1 : #[(m + 1) / (17 * 8), (m + 1) % (17 * 8) / 17, (m + 1) % (17 * 8) % 17].getD 1 0 =
      (m + 1) % (17 * 8) / 17 := rfl
    have h2 : #[(m + 1) / (17 * 8), (m + 1) % (17 * 8) / 17, (m + 1) % (17 * 8) % 17].getD 2 0 =
      (m + 1) % (17 * 8) % 17 := rfl
    rw [h0, h1, h2]
    omega

theorem signerSetOk_refines :
    Model.Aggregate.Wire.signerSetOk = Spec.Aggregate.Wire.signerSetOk := rfl

theorem deferredMatches_refines (table : Array K) (claim : Spec.Aggregate.Wire.DeferredClaim) :
    Model.Aggregate.Wire.deferredMatches table claim =
      Spec.Aggregate.Wire.deferredMatches table claim := by
  simp only [Model.Aggregate.Wire.deferredMatches, Spec.Aggregate.Wire.deferredMatches,
    Proofs.Pcs.Whir.multilinearEval_refines]

theorem proofSize_eq_bytes (proof : Spec.Aggregate.Wire.EthereumProof) :
    Spec.Aggregate.Wire.EthereumProof.proofSize proof =
      (Spec.Aggregate.Wire.putProof ByteArray.empty proof.proof).size := rfl

end LeanVmXmss.Proofs.Aggregate.Wire
