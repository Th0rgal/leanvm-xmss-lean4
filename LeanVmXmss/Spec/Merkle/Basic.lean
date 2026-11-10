import Spec.Keccak.Basic
import Spec.Field.Basic

namespace LeanVmXmss.Spec.Merkle

open Spec.Field (E)

abbrev Digest := Vector UInt8 32

def digestBytes (d : Digest) : ByteArray := ⟨d.toArray⟩

def toDigest (b : ByteArray) : Digest := Vector.ofFn fun i => b[i.val]!

def hashLeaf (b : ByteArray) : Digest := toDigest (Keccak.keccak256 b)

def compress (left right : Digest) : Digest := hashLeaf (digestBytes left ++ digestBytes right)

def leafImage (row : Array UInt64) (leafWords : Nat) : ByteArray :=
  Keccak.wordsBytes (Array.replicate (leafWords - row.size) 0 ++ row)

def hashRow (row : Array UInt64) (leafWords : Nat) : Digest := hashLeaf (leafImage row leafWords)

def hashToScalars (d : ByteArray) : E × E :=
  (⟨Keccak.wordAt d 0, Keccak.wordAt d 8, 0⟩, ⟨Keccak.wordAt d 16, Keccak.wordAt d 24, 0⟩)

def parentLevel (nodes : Array Digest) : Array Digest :=
  (Array.range (nodes.size / 2)).map fun i => compress nodes[2 * i]! nodes[2 * i + 1]!

def levels (count : Nat) : Array Digest → Array (Array Digest) :=
  Nat.rec (fun nodes => #[nodes]) (fun _ previous nodes =>
    if nodes.size ≤ 1 then #[nodes] else #[nodes] ++ previous (parentLevel nodes)) count

theorem levels_zero (nodes : Array Digest) : levels 0 nodes = #[nodes] := rfl

theorem levels_succ (n : Nat) (nodes : Array Digest) :
    levels (n + 1) nodes =
      if nodes.size ≤ 1 then #[nodes] else #[nodes] ++ levels n (parentLevel nodes) := rfl

def build (leaves : Array Digest) : Array (Array Digest) := levels leaves.size leaves

def treeRoot (tree : Array (Array Digest)) : Digest := tree.back![0]!

def inclusionPath (tree : Array (Array Digest)) (index : Nat) : Array Digest :=
  (Array.range (tree.size - 1)).map fun level => tree[level]![(index / 2^level) ^^^ 1]!

def pathRoot (index : Nat) (node : Digest) (siblings : List Digest) : Digest :=
  (siblings.foldl (fun (state : Nat × Digest) sibling =>
    (state.1 / 2, if state.1 % 2 == 0 then compress state.2 sibling else compress sibling state.2))
      (index, node)).2

theorem pathRoot_nil (index : Nat) (node : Digest) : pathRoot index node [] = node := rfl

theorem pathRoot_cons (index : Nat) (node sibling : Digest) (rest : List Digest) :
    pathRoot index node (sibling :: rest) =
      pathRoot (index / 2) (if index % 2 == 0 then compress node sibling else compress sibling node) rest := rfl

def verifyPath (root leaf : Digest) (index : Nat) (siblings : List Digest) : Bool :=
  decide (index < 2^siblings.length ∧ pathRoot index leaf siblings = root)

end LeanVmXmss.Spec.Merkle
