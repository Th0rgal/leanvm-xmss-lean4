import Spec.Merkle.Basic

namespace LeanVmXmss.Spec.Merkle

structure PrunedMerklePaths where
  rows : Array (Array UInt64)
  siblings : Array Digest
  deriving Inhabited

structure MerklePath where
  index : Nat
  leaf : Array UInt64
  siblings : Array Digest
  deriving Inhabited

def sortedUnique (queries : Array Nat) : Array Nat :=
  (queries.toList.mergeSort (· ≤ ·)).eraseDups.toArray

def validIndices (depth : Nat) (indices : Array Nat) : Bool :=
  !indices.isEmpty && indices.all (· < 2^depth) && sortedUnique indices == indices

def checkedLeafImage (row : Array UInt64) (leafWords : Nat) : Option ByteArray :=
  if row.size ≤ leafWords then some (leafImage row leafWords) else none

def checkedDigest (b : ByteArray) : Option Digest :=
  if b.size = 32 then some (toDigest b) else none

def fromHalves (low high : Spec.Field.E) : Option Digest :=
  if low.c2 = 0 ∧ high.c2 = 0 then
    checkedDigest (Keccak.wordsBytes #[low.c0, low.c1, high.c0, high.c1])
  else none

def pruneLevel (nodes : Array Digest) (active : List Nat) : List Nat × Array Digest :=
  active.zipIdx.foldr (fun (p, i) previous skip =>
    let rest := active.drop (i + 1)
    if skip then previous false else
      if rest.head? = some (p ^^^ 1) then
        let tail := previous true
        (p / 2 :: tail.1, tail.2)
      else
        let tail := previous false
        (p / 2 :: tail.1, #[nodes[p ^^^ 1]!] ++ tail.2)) (fun _ => ([], #[])) false

def pruneLevels (depth : Nat) : Nat → Array (Array Digest) → List Nat → Array Digest :=
  Nat.rec (fun _ _ _ => #[]) (fun _ previous level tree active =>
    let next := pruneLevel tree[level]! active
    next.2 ++ previous (level + 1) tree next.1) depth

def openPruned (depth leafWords : Nat) (rows : Array (Array UInt64))
    (queries : Array Nat) : Option PrunedMerklePaths := do
  let indices := sortedUnique queries
  if rows.size != 2^depth || !rows.all (fun row => row.size ≤ leafWords) ||
      !validIndices depth indices then none else
    let tree := build (rows.map fun row => hashRow row leafWords)
    some ⟨indices.map (fun i => rows[i]!), pruneLevels depth 0 tree indices.toList⟩

structure ActiveNode where
  index : Nat
  digest : Digest
  members : Array Nat
  deriving Inhabited

def expandLevel (cursor : Nat) (nodes : List ActiveNode) (siblings : Array Digest)
    (paths : Array MerklePath) : Option (List ActiveNode × Nat × Array MerklePath) :=
  nodes.zipIdx.foldr
    (fun (node, i) previous skip cursor paths => do
    let rest := nodes.drop (i + 1)
    if skip then previous false cursor paths else
    if node.index % 2 = 0 && rest.head?.any (fun r => r.index = node.index + 1) then
      let right := rest.head!
      let paths := node.members.foldl (fun paths i =>
        paths.modify i fun p => {p with siblings := p.siblings.push right.digest}) paths
      let paths := right.members.foldl (fun paths i =>
        paths.modify i fun p => {p with siblings := p.siblings.push node.digest}) paths
      let (tail, cursor, paths) ← previous true cursor paths
      some (⟨node.index / 2, compress node.digest right.digest, node.members ++ right.members⟩ :: tail,
        cursor, paths)
    else
      let sibling ← siblings[cursor]?
      let paths := node.members.foldl (fun paths i =>
        paths.modify i fun p => {p with siblings := p.siblings.push sibling}) paths
      let parent := if node.index % 2 = 0 then compress node.digest sibling else compress sibling node.digest
      let (tail, cursor, paths) ← previous false (cursor + 1) paths
      some (⟨node.index / 2, parent, node.members⟩ :: tail, cursor, paths))
        (fun _ cursor paths => some ([], cursor, paths)) false cursor paths

def expandLevels (depth : Nat) : List ActiveNode → Nat → Array Digest → Array MerklePath →
    Option (List ActiveNode × Nat × Array MerklePath) :=
  Nat.rec (fun nodes cursor _ paths => some (nodes, cursor, paths))
    (fun _ previous nodes cursor siblings paths => do
    let (nodes, cursor, paths) ← expandLevel cursor nodes siblings paths
    previous nodes cursor siblings paths) depth

theorem expandLevels_zero (nodes : List ActiveNode) (cursor : Nat) (siblings : Array Digest)
    (paths : Array MerklePath) : expandLevels 0 nodes cursor siblings paths = some (nodes, cursor, paths) := rfl

theorem expandLevels_succ (depth : Nat) (nodes : List ActiveNode) (cursor : Nat)
    (siblings : Array Digest) (paths : Array MerklePath) :
    expandLevels (depth + 1) nodes cursor siblings paths =
      (expandLevel cursor nodes siblings paths).bind (fun result =>
        expandLevels depth result.1 result.2.1 siblings result.2.2) := rfl

def expandPruned (proof : PrunedMerklePaths) (depth : Nat) (queries : Array Nat)
    (rowWords leafWords : Nat) : Option (Digest × Array MerklePath) := do
  let indices := sortedUnique queries
  if !validIndices depth indices || indices.size != proof.rows.size || rowWords > leafWords ||
      !proof.rows.all (fun row => row.size == rowWords) then none else
    let paths := indices.mapIdx fun i index =>
      MerklePath.mk index (Array.replicate (leafWords - rowWords) 0 ++ proof.rows[i]!) #[]
    let nodes := paths.mapIdx fun i path =>
      ActiveNode.mk path.index (hashLeaf (Keccak.wordsBytes path.leaf)) #[i]
    let (nodes, consumed, paths) ← expandLevels depth nodes.toList 0 proof.siblings paths
    if consumed != proof.siblings.size then none else
      let node ← nodes.head?
      if nodes.length != 1 || node.index != 0 then none else
        some (node.digest, queries.map fun query =>
          paths[(indices.toList.idxOf query)]!)

def verifyPruned (root : Digest) (proof : PrunedMerklePaths) (depth : Nat)
    (queries : Array Nat) (rowWords leafWords : Nat) : Bool :=
  (expandPruned proof depth queries rowWords leafWords).any fun result =>
    (Array.range 32).all fun i => result.1[i]!.toNat == root[i]!.toNat

end LeanVmXmss.Spec.Merkle
