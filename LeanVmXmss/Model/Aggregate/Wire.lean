import Spec.Aggregate.Wire
import Model.Pcs.Whir
import Model.Layout.Scalar
import Model.Transcript.Registers

namespace LeanVmXmss.Model.Aggregate.Wire

open Spec.Field (K E)

def maxKeys := Spec.Aggregate.Wire.maxKeys
def recursionLabel := Spec.Aggregate.Wire.recursionLabel
def claimGroup := Spec.Aggregate.Wire.claimGroup
def claimBig := Spec.Aggregate.Wire.claimBig
def strictlySorted := Spec.Aggregate.Wire.strictlySorted
def signerSetOk := Spec.Aggregate.Wire.signerSetOk

def putU64 := Spec.Aggregate.Wire.putU64
def putUsize := Spec.Aggregate.Wire.putUsize
def putE := Spec.Aggregate.Wire.putE
def putProof := Spec.Aggregate.Wire.putProof
def putClaims := Spec.Aggregate.Wire.putClaims

def EthereumProof.toBytes := Spec.Aggregate.Wire.EthereumProof.toBytes
def EthereumProof.toBytesWithoutPubkeys := Spec.Aggregate.Wire.EthereumProof.toBytesWithoutPubkeys
def EthereumProof.proofSize := Spec.Aggregate.Wire.EthereumProof.proofSize
def EthereumProof.fromBytes := Spec.Aggregate.Wire.EthereumProof.fromBytes
def EthereumProof.fromBytesWithoutPubkeys := Spec.Aggregate.Wire.EthereumProof.fromBytesWithoutPubkeys

def listSplit := Spec.Aggregate.Wire.listSplit

def claimCells (p : Spec.Aggregate.Wire.SignaturePair) : Array E :=
  #[⟨Model.Layout.readWordLE p.pubkey 0, Model.Layout.readWordLE p.pubkey 8, 0⟩,
    ⟨Model.Layout.readWordLE p.pubkey 16, Model.Layout.readWordLE p.pubkey 24, 0⟩,
    ⟨Model.Layout.readWordLE p.message 0, Model.Layout.readWordLE p.message 8, 0⟩,
    ⟨Model.Layout.readWordLE p.message 16, Model.Layout.readWordLE p.message 24, 0⟩]

def claimListDigest (claims : Array Spec.Aggregate.Wire.SignaturePair) : E × E :=
  let lanes := claims.foldl (fun acc p =>
    (claimCells p).foldl (fun acc x => acc ++ #[x.c0, x.c1]) acc) #[]
  Spec.Merkle.hashToScalars (Model.Layout.keccak256Fast (Model.Layout.wordsBytesFast lanes))

def daLabel := Spec.Aggregate.Wire.daLabel

def daDigest (root : Option ByteArray) : ByteArray :=
  match root with
  | none => (Array.range 32).foldl (fun b _ => b.push 0) ByteArray.empty
  | some root =>
    let z := (Model.Transcript.Registers.sample
      (Model.Transcript.Registers.init (Model.Layout.keccak256Fast Spec.Aggregate.Wire.daLabel) root)).1
    let left := Spec.Merkle.digestBytes (Spec.Merkle.toDigest root)
    let right := Spec.Merkle.digestBytes
      (Spec.Merkle.toDigest (Spec.Field.encodeBytesE ⟨z.c0, z.c1, z.c2⟩ ++ Spec.Field.encodeBytesK 0))
    Spec.Merkle.digestBytes (Spec.Merkle.toDigest (Model.Layout.keccak256Fast (left ++ right)))

def statementDigest (seed xmssDigest sphincsDigest : E × E) (da : ByteArray)
    (defer : Spec.Aggregate.Wire.DeferredClaim) : E × E :=
  let da := Spec.Merkle.hashToScalars da
  let header := #[seed.1, seed.2, xmssDigest.1, xmssDigest.2, sphincsDigest.1, sphincsDigest.2, da.1, da.2]
  let cells := defer.cells
  let cells := if cells.size % 2 = 1 then cells.push Spec.Field.zero else cells
  let lanes := header.foldl (fun acc x => acc ++ #[x.c0, x.c1]) #[] ++
    cells.foldl (fun acc x => acc ++ #[x.c0, x.c1, x.c2]) #[]
  Spec.Merkle.hashToScalars (Model.Layout.keccak256Fast (Model.Layout.wordsBytesFast lanes))

def EthereumProof.statement (seed : E × E) (proof : Spec.Aggregate.Wire.EthereumProof) : E × E :=
  statementDigest seed (claimListDigest proof.claims.xmss)
    (claimListDigest proof.claims.leanSphincs) (daDigest proof.daRoot) proof.defer

def deferredMatches (table : Array K) (claim : Spec.Aggregate.Wire.DeferredClaim) : Bool :=
  if decide (1 <<< claim.bytecodePoint.size = table.size) then
    Spec.Vm.wordBEq claim.bytecodeValue (Model.Pcs.Whir.multilinearEval table claim.bytecodePoint)
  else false

end LeanVmXmss.Model.Aggregate.Wire
