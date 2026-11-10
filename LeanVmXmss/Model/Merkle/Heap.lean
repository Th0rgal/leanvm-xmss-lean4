import Spec.Merkle.Pruned

namespace LeanVmXmss.Model.Merkle

structure Digest32 where
  lo0 : UInt64
  lo1 : UInt64
  hi0 : UInt64
  hi1 : UInt64
  deriving Inhabited, DecidableEq, Repr

instance : BEq Digest32 where
  beq a b := a.lo0.toNat == b.lo0.toNat && a.lo1.toNat == b.lo1.toNat &&
    a.hi0.toNat == b.hi0.toNat && a.hi1.toNat == b.hi1.toNat

def Digest32.toBytes (d : Digest32) : ByteArray :=
  Spec.Keccak.wordsBytes #[d.lo0, d.lo1, d.hi0, d.hi1]

def Digest32.fromBytes (b : ByteArray) : Option Digest32 :=
  if b.size = 32 then some ⟨Spec.Keccak.wordAt b 0, Spec.Keccak.wordAt b 8,
    Spec.Keccak.wordAt b 16, Spec.Keccak.wordAt b 24⟩ else none

def Digest32.hashPair (left right : Digest32) : Digest32 :=
  let b := Spec.Keccak.keccak256 (left.toBytes ++ right.toBytes)
  ⟨Spec.Keccak.wordAt b 0, Spec.Keccak.wordAt b 8,
    Spec.Keccak.wordAt b 16, Spec.Keccak.wordAt b 24⟩

structure HeapTree where
  depth : Nat
  nodes : Array Digest32
  deriving Inhabited

def climb (count : Nat) : Array Digest32 → Array Digest32 :=
  Nat.rec (fun nodes => nodes) (fun k previous nodes =>
    previous (nodes.set! (k + 1) (Digest32.hashPair nodes[2 * (k + 1)]! nodes[2 * (k + 1) + 1]!))) count

theorem climb_zero (nodes : Array Digest32) : climb 0 nodes = nodes := rfl

theorem climb_succ (k : Nat) (nodes : Array Digest32) :
    climb (k + 1) nodes = climb k (nodes.set! (k + 1)
      (Digest32.hashPair nodes[2 * (k + 1)]! nodes[2 * (k + 1) + 1]!)) := rfl

def buildHeap (depth : Nat) (leaves : Array Digest32) : Option HeapTree :=
  if leaves.size = 2^depth then
    let nodes := Array.replicate leaves.size default ++ leaves
    some ⟨depth, climb (leaves.size - 1) nodes⟩
  else none

def heapRoot (tree : HeapTree) : Option Digest32 := tree.nodes[1]?

def heapPath (tree : HeapTree) (index : Nat) : Option (Array Digest32) :=
  if index < 2^tree.depth ∧ tree.nodes.size = 2 * 2^tree.depth then
    some ((Array.range tree.depth).map fun level =>
      tree.nodes[((2^tree.depth + index) / 2^level) ^^^ 1]!)
  else none

end LeanVmXmss.Model.Merkle
