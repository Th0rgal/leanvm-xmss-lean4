import Spec.Transcript.Basic
import Spec.Merkle.Pruned

namespace LeanVmXmss.Spec.Transcript

open Spec.Field (E)

structure ReplayProof where
  scalars : Array E
  openings : Array Merkle.PrunedMerklePaths

structure VerifierState where
  proof : ReplayProof
  sponge : Sponge
  scalarOffset : Nat := 0
  openingOffset : Nat := 0
  paths : Array Merkle.MerklePath := #[]

def verifierNew (proof : ReplayProof) (iv publicInput : ByteArray) : VerifierState :=
  ⟨proof, init iv publicInput, 0, 0, #[]⟩

def nextRaw (s : VerifierState) : Option (E × VerifierState) := do
  let x ← s.proof.scalars[s.scalarOffset]?
  some (x, {s with scalarOffset := s.scalarOffset + 1})

def nextScalar (s : VerifierState) : Option (E × VerifierState) := do
  let (x, s) ← nextRaw s
  some (x, {s with sponge := observe s.sponge x})

def nextScalars (count : Nat) : VerifierState → Option (Array E × VerifierState) :=
  Nat.rec (fun s => some (#[], s)) (fun _ previous s => do
    let (x, s) ← nextScalar s
    let (xs, s) ← previous s
    some (#[x] ++ xs, s)) count

def verifierSample (s : VerifierState) : E × VerifierState :=
  let (x, sponge) := challenge s.sponge
  (x, {s with sponge})

def sumcheckRoundPoly (s : VerifierState) (degree : Nat) (claimedSum : E)
    (eqFactor : Option E := none) : Option (Array E × VerifierState) := do
  if degree < 1 then none else
    match eqFactor with
    | none =>
      let (c0, s) ← nextScalar s
      let (tail, s) ← nextScalars (degree - 1) s
      let c1 := Spec.Field.eadd claimedSum (tail.foldl Spec.Field.eadd Spec.Field.zero)
      some (#[c0, c1] ++ tail, s)
    | some r =>
      let (tail, s) ← nextScalars degree s
      let c0 := Spec.Field.eadd claimedSum
        (Spec.Field.emul r (tail.foldl Spec.Field.eadd Spec.Field.zero))
      some (#[c0] ++ tail, s)

def merkle (s : VerifierState) (root : Merkle.Digest) (depth : Nat)
    (queries : Array Nat) (rowWords leafWords : Nat) :
    Option (Array (Array UInt64) × VerifierState) := do
  let batch ← s.proof.openings[s.openingOffset]?
  let (computedRoot, paths) ← Merkle.expandPruned batch depth queries rowWords leafWords
  if computedRoot = root then
    let next := { s with openingOffset := s.openingOffset + 1, paths := s.paths ++ paths }
    some (paths.map (·.leaf), next)
  else none

def grindCheck (s : VerifierState) (bits : Nat) : Option VerifierState := do
  let (nonce, s) ← nextRaw s
  let (ok, sponge) := verifyPow s.sponge nonce bits
  if ok then some {s with sponge} else none

def finish (s : VerifierState) : Option (Array Merkle.MerklePath) :=
  if s.scalarOffset = s.proof.scalars.size ∧ s.openingOffset = s.proof.openings.size then
    some s.paths
  else none

def checkedAddRoundPoly (s : ProverState) (coeffs : Array E) (eq : Bool) : Option ProverState :=
  if coeffs.size ≥ 2 then some (addRoundPoly s coeffs eq) else none

end LeanVmXmss.Spec.Transcript
