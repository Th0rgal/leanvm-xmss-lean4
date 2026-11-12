import Model.Merkle.Heap
import Model.Keccak.Registers
import Model.Layout.Scalar

namespace LeanVmXmss.Model.Merkle

open Model.Layout (zeroState25)

@[noinline] def Digest32.hashPairFlat (left right : Digest32) : Digest32 :=
  let st := Model.Keccak.keccakF1600
    { zeroState25 with
      a00 := left.lo0
      a01 := left.lo1
      a02 := left.hi0
      a03 := left.hi1
      a04 := right.lo0
      a05 := right.lo1
      a06 := right.hi0
      a07 := right.hi1
      a08 := 1
      a16 := 0x8000000000000000 }
  ⟨st.a00, st.a01, st.a02, st.a03⟩

structure FlatTree where
  depth : Nat
  nodes : Array Digest32
  deriving Inhabited

@[inline] def readWordLE (bytes : @& ByteArray) (off : Nat) : UInt64 :=
  (bytes.get! off).toUInt64 |||
    ((bytes.get! (off + 1)).toUInt64 <<< 8) |||
    ((bytes.get! (off + 2)).toUInt64 <<< 16) |||
    ((bytes.get! (off + 3)).toUInt64 <<< 24) |||
    ((bytes.get! (off + 4)).toUInt64 <<< 32) |||
    ((bytes.get! (off + 5)).toUInt64 <<< 40) |||
    ((bytes.get! (off + 6)).toUInt64 <<< 48) |||
    ((bytes.get! (off + 7)).toUInt64 <<< 56)

def Digest32.fromBytesFast (bytes : @& ByteArray) : Option Digest32 :=
  if decide (bytes.size = 32) then
    some ⟨readWordLE bytes 0, readWordLE bytes 8, readWordLE bytes 16, readWordLE bytes 24⟩
  else none

def Digest32.toBytesFast (d : Digest32) : ByteArray :=
  Model.Layout.wordsBytesFast #[d.lo0, d.lo1, d.hi0, d.hi1]

def Digest32.toSpecDigest (d : Digest32) : Spec.Merkle.Digest :=
  Spec.Merkle.toDigest d.toBytesFast

def flatParent (nodes : Array Digest32) (base i : Nat) : Digest32 :=
  let idx := base + 2 * i
  Digest32.hashPairFlat (nodes.getD idx default) (nodes.getD (idx + 1) default)

def buildFlat (depth : Nat) (leaves : Array Digest32) : Option FlatTree :=
  if decide (leaves.size ≠ 1 <<< depth) then none else
    let total := (2 <<< depth) - 1
    let init := Fin.foldl leaves.size
      (fun acc k => acc.push (leaves.getD k.val default))
      (Array.emptyWithCapacity total)
    let built := Fin.foldl depth
      (fun (nodes, base, len) _ =>
        let half := len / 2
        let next := Fin.foldl half (fun ns i => ns.push (flatParent ns base i.val)) nodes
        (next, base + len, half))
      (init, 0, 1 <<< depth)
    some ⟨depth, built.1⟩

def flatRoot (tree : FlatTree) : Digest32 :=
  tree.nodes.getD (tree.nodes.size - 1) default

def pruneFlatLayer (nodes : @& Array Digest32) (base : Nat) (active : List Nat)
    (initSibs : Array Digest32) : List Nat × Array Digest32 :=
  let (pend?, parentsRev, sibs) := active.foldl
    (fun (pend?, pRev, sibs) q =>
      match pend? with
      | none => (some q, pRev, sibs)
      | some p =>
        if decide (q = (p ^^^ 1)) then
          (none, (p / 2) :: pRev, sibs)
        else
          (some q, (p / 2) :: pRev, sibs.push (nodes.getD (base + (p ^^^ 1)) default)))
    ((none : Option Nat), ([] : List Nat), initSibs)
  match pend? with
  | none => (parentsRev.reverse, sibs)
  | some p => (((p / 2) :: parentsRev).reverse, sibs.push (nodes.getD (base + (p ^^^ 1)) default))

def flatLevelsSiblings (tree : FlatTree) (indices : List Nat) :
    List Nat × Array (Array Digest32) :=
  let res := Fin.foldl tree.depth
    (fun (levels, active, base, len) _ =>
      let step := pruneFlatLayer tree.nodes base active #[]
      (levels.push step.2, step.1, base + len, len / 2))
    (#[], indices, 0, 1 <<< tree.depth)
  (res.2.1, res.1)

def flatSiblings (tree : FlatTree) (indices : List Nat) : Array Digest32 :=
  let res := Fin.foldl tree.depth
    (fun (sibs, active, base, len) _ =>
      let step := pruneFlatLayer tree.nodes base active sibs
      (step.2, step.1, base + len, len / 2))
    (#[], indices, 0, 1 <<< tree.depth)
  res.1

def openTreeFlat (tree : FlatTree) (queries : Array Nat)
    (rowAt : Nat → Array UInt64) : Option Spec.Merkle.PrunedMerklePaths :=
  let indices := Spec.Merkle.sortedUnique queries
  if !Spec.Merkle.validIndices tree.depth indices then none else
    let rows := indices.map rowAt
    let sibs := (flatSiblings tree indices.toList).map Digest32.toSpecDigest
    some ⟨rows, sibs⟩

end LeanVmXmss.Model.Merkle
