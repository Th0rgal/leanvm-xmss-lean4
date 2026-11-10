import Spec.Pcs.Whir

namespace LeanVmXmss.Spec.Aggregate.Wire

open Spec.Field (K E zero)

def maxKeys : Nat := 1 <<< 16
def recursionLabel : ByteArray := String.toUTF8 "leanvm/recursion-aggregation/v1"
def daLabel : ByteArray := String.toUTF8 "leanDA/rs-membership/v1"

def claimGroup : Nat := 17
def bigGroups : Nat := 8
def claimBig : Nat := claimGroup * bigGroups
def statementHeader : Nat := 8

structure SignaturePair where
  pubkey : ByteArray
  message : ByteArray
  deriving Inhabited, DecidableEq

def SignaturePair.bytes (p : SignaturePair) : ByteArray := p.pubkey ++ p.message

structure SignatureClaims where
  xmss : Array SignaturePair
  leanSphincs : Array SignaturePair
  deriving Inhabited

def pairLt (a b : SignaturePair) : Bool :=
  decide (a.pubkey.toList < b.pubkey.toList) ||
    (decide (a.pubkey.toList = b.pubkey.toList) && decide (a.message.toList < b.message.toList))

def strictlySorted (xs : Array SignaturePair) : Bool :=
  (Array.range xs.size).all fun i =>
    match xs[i]? with
    | none => false
    | some a =>
      (Array.range (xs.size - (i + 1))).all fun d =>
        match xs[i + 1 + d]? with
        | none => false
        | some b => pairLt a b

def signerSetOk (claims : SignatureClaims) : Bool :=
  decide (claims.xmss.size + claims.leanSphincs.size < maxKeys) &&
    strictlySorted claims.xmss && strictlySorted claims.leanSphincs

structure VmProof where
  stream : Array E
  merkle : Array Spec.Merkle.PrunedMerklePaths
  deriving Inhabited

structure DeferredClaim where
  bytecodePoint : Array E
  bytecodeValue : E
  deriving DecidableEq

def DeferredClaim.cells (d : DeferredClaim) : Array E := d.bytecodePoint.push d.bytecodeValue

structure EthereumProof where
  claims : SignatureClaims
  daRoot : Option ByteArray
  defer : DeferredClaim
  proof : VmProof

def putU64 (b : ByteArray) (w : UInt64) : ByteArray := b ++ Spec.Field.encodeBytesK w

def putUsize (b : ByteArray) (n : Nat) : ByteArray := putU64 b (UInt64.ofNat n)

def putBytes (b : ByteArray) (raw : ByteArray) : ByteArray :=
  putUsize b raw.size ++ raw

def putOption32 (b : ByteArray) (value : Option ByteArray) : ByteArray :=
  match value with
  | none => b.push 0
  | some raw =>
    if decide (raw.size = 32) then (b.push 1) ++ raw else b.push 0

def putE (b : ByteArray) (x : E) : ByteArray :=
  putU64 (putU64 (putU64 b x.c0) x.c1) x.c2

def putRow (b : ByteArray) (row : Array UInt64) : ByteArray :=
  row.foldl putU64 (putUsize b row.size)

def putDigest (b : ByteArray) (d : Spec.Merkle.Digest) : ByteArray :=
  (Array.range 32).foldl (fun b i => b.push (d[i]?.getD 0)) b

def putPhase (b : ByteArray) (phase : Spec.Merkle.PrunedMerklePaths) : ByteArray :=
  let b := phase.rows.foldl putRow (putUsize b phase.rows.size)
  phase.siblings.foldl putDigest (putUsize b phase.siblings.size)

def putProof (b : ByteArray) (proof : VmProof) : ByteArray :=
  let b := proof.stream.foldl putE (putUsize b proof.stream.size)
  proof.merkle.foldl putPhase (putUsize b proof.merkle.size)

def putPair (b : ByteArray) (p : SignaturePair) : ByteArray :=
  b ++ p.pubkey ++ p.message

def putClaims (b : ByteArray) (claims : SignatureClaims) : ByteArray :=
  let b := claims.xmss.foldl putPair (putUsize b claims.xmss.size)
  claims.leanSphincs.foldl putPair (putUsize b claims.leanSphincs.size)

def EthereumProof.coreBytes (proof : EthereumProof) : ByteArray :=
  let b := putOption32 ByteArray.empty proof.daRoot
  let b := proof.defer.bytecodePoint.foldl putE (putUsize b proof.defer.bytecodePoint.size)
  putProof b proof.proof

def EthereumProof.toBytes (proof : EthereumProof) : ByteArray :=
  putClaims ByteArray.empty proof.claims ++ proof.coreBytes

def EthereumProof.toBytesWithoutPubkeys (proof : EthereumProof) : ByteArray :=
  proof.coreBytes

def EthereumProof.proofSize (proof : EthereumProof) : Nat :=
  (putProof ByteArray.empty proof.proof).size

structure Cursor where
  bytes : ByteArray
  pos : Nat
  deriving Inhabited

def Cursor.rest (c : Cursor) : Nat := c.bytes.size - c.pos

def Cursor.take (c : Cursor) (n : Nat) : Option (ByteArray × Cursor) :=
  if decide (c.pos + n ≤ c.bytes.size) then
    some (c.bytes.extract c.pos (c.pos + n), { c with pos := c.pos + n })
  else none

def Cursor.u64 (c : Cursor) : Option (UInt64 × Cursor) := do
  let (raw, c) ← c.take 8
  some (Spec.Field.readLimb raw 0, c)

def Cursor.usize (c : Cursor) : Option (Nat × Cursor) := do
  let (w, c) ← c.u64
  some (w.toNat, c)

def Cursor.bytesOf (c : Cursor) : Option (ByteArray × Cursor) := do
  let (n, c) ← c.usize
  c.take n

def Cursor.option32 (c : Cursor) : Option (Option ByteArray × Cursor) := do
  let (tag, c) ← c.take 1
  match tag[0]?.getD 0 with
  | 0 => some (none, c)
  | 1 => do
    let (raw, c) ← c.take 32
    some (some raw, c)
  | _ => none

def Cursor.elem (c : Cursor) : Option (E × Cursor) := do
  let (c0, c) ← c.u64
  let (c1, c) ← c.u64
  let (c2, c) ← c.u64
  some (⟨c0, c1, c2⟩, c)

def Cursor.repeat {α : Type} (n : Nat) (step : Cursor → Option (α × Cursor))
    (c : Cursor) : Option (Array α × Cursor) :=
  (Array.range n).foldlM (fun (acc, c) _ => do
    let (x, c) ← step c
    some (acc.push x, c)) (#[], c)

def Cursor.row (c : Cursor) : Option (Array UInt64 × Cursor) := do
  let (n, c) ← c.usize
  c.repeat n Cursor.u64

def Cursor.digest (c : Cursor) : Option (Spec.Merkle.Digest × Cursor) := do
  let (raw, c) ← c.take 32
  Spec.Merkle.checkedDigest raw |>.map fun d => (d, c)

def Cursor.phase (c : Cursor) : Option (Spec.Merkle.PrunedMerklePaths × Cursor) := do
  let (n, c) ← c.usize
  let (rows, c) ← c.repeat n Cursor.row
  let (m, c) ← c.usize
  let (siblings, c) ← c.repeat m Cursor.digest
  some (⟨rows, siblings⟩, c)

def Cursor.proof (c : Cursor) : Option (VmProof × Cursor) := do
  let (n, c) ← c.usize
  let (stream, c) ← c.repeat n Cursor.elem
  let (m, c) ← c.usize
  let (merkle, c) ← c.repeat m Cursor.phase
  some (⟨stream, merkle⟩, c)

def Cursor.pair (c : Cursor) : Option (SignaturePair × Cursor) := do
  let (pubkey, c) ← c.take 32
  let (message, c) ← c.take 32
  some (⟨pubkey, message⟩, c)

def Cursor.list (c : Cursor) : Option (Array SignaturePair × Cursor) := do
  let (n, c) ← c.usize
  c.repeat n Cursor.pair

def Cursor.claims (c : Cursor) : Option (SignatureClaims × Cursor) := do
  let (xmss, c) ← c.list
  let (leanSphincs, c) ← c.list
  some (⟨xmss, leanSphincs⟩, c)

def Cursor.core (c : Cursor) : Option (Option ByteArray × Array E × VmProof × Cursor) := do
  let (daRoot, c) ← c.option32
  let (n, c) ← c.usize
  let (bytecodePoint, c) ← c.repeat n Cursor.elem
  let (proof, c) ← c.proof
  some (daRoot, bytecodePoint, proof, c)

def fromParts (claims : SignatureClaims) (daRoot : Option ByteArray)
    (bytecodePoint : Array E) (bytecodeValue : E) (proof : VmProof) : Option EthereumProof :=
  if signerSetOk claims then
    some ⟨claims, daRoot, ⟨bytecodePoint, bytecodeValue⟩, proof⟩
  else none

def EthereumProof.fromBytes (bytes : ByteArray) (bytecodeValue : E) : Option EthereumProof := do
  let (claims, c) ← Cursor.claims ⟨bytes, 0⟩
  let (daRoot, point, proof, c) ← c.core
  if decide (c.pos = bytes.size) then fromParts claims daRoot point bytecodeValue proof else none

def EthereumProof.fromBytesWithoutPubkeys (bytes : ByteArray) (claims : SignatureClaims)
    (bytecodeValue : E) : Option EthereumProof := do
  let (daRoot, point, proof, c) ← Cursor.core ⟨bytes, 0⟩
  if decide (c.pos = bytes.size) then fromParts claims daRoot point bytecodeValue proof else none

def listSplit (n : Nat) : Array Nat :=
  if n = 0 then #[] else
    let rest := n % claimBig
    #[n / claimBig, rest / claimGroup, rest % claimGroup]

def claimCells (p : SignaturePair) : Array E :=
  #[⟨Spec.Keccak.wordAt p.pubkey 0, Spec.Keccak.wordAt p.pubkey 8, 0⟩,
    ⟨Spec.Keccak.wordAt p.pubkey 16, Spec.Keccak.wordAt p.pubkey 24, 0⟩,
    ⟨Spec.Keccak.wordAt p.message 0, Spec.Keccak.wordAt p.message 8, 0⟩,
    ⟨Spec.Keccak.wordAt p.message 16, Spec.Keccak.wordAt p.message 24, 0⟩]

def claimListDigest (claims : Array SignaturePair) : E × E :=
  let lanes := claims.foldl (fun acc p =>
    (claimCells p).foldl (fun acc x => acc ++ #[x.c0, x.c1]) acc) #[]
  Spec.Merkle.hashToScalars (Spec.Keccak.keccak256 (Spec.Keccak.wordsBytes lanes))

def daDigest (root : Option ByteArray) : ByteArray :=
  match root with
  | none => (Array.range 32).foldl (fun b _ => b.push 0) ByteArray.empty
  | some root =>
    let z := (Spec.Transcript.challenge
      (Spec.Transcript.init (Spec.Keccak.keccak256 daLabel) root)).1
    Spec.Merkle.digestBytes (Spec.Merkle.compress (Spec.Merkle.toDigest root)
      (Spec.Merkle.toDigest (Spec.Field.encodeBytesE ⟨z.c0, z.c1, z.c2⟩ ++ Spec.Field.encodeBytesK 0)))

def statementDigest (seed xmssDigest sphincsDigest : E × E) (da : ByteArray)
    (defer : DeferredClaim) : E × E :=
  let da := Spec.Merkle.hashToScalars da
  let header := #[seed.1, seed.2, xmssDigest.1, xmssDigest.2, sphincsDigest.1, sphincsDigest.2, da.1, da.2]
  let cells := defer.cells
  let cells := if cells.size % 2 = 1 then cells.push zero else cells
  let lanes := header.foldl (fun acc x => acc ++ #[x.c0, x.c1]) #[] ++
    cells.foldl (fun acc x => acc ++ #[x.c0, x.c1, x.c2]) #[]
  Spec.Merkle.hashToScalars (Spec.Keccak.keccak256 (Spec.Keccak.wordsBytes lanes))

def EthereumProof.statement (seed : E × E) (proof : EthereumProof) : E × E :=
  statementDigest seed (claimListDigest proof.claims.xmss)
    (claimListDigest proof.claims.leanSphincs) (daDigest proof.daRoot) proof.defer

def deferredMatches (table : Array K) (claim : DeferredClaim) : Bool :=
  if decide (1 <<< claim.bytecodePoint.size = table.size) then
    Spec.Vm.wordBEq claim.bytecodeValue (Spec.Pcs.Whir.multilinearEval table claim.bytecodePoint)
  else false

end LeanVmXmss.Spec.Aggregate.Wire
