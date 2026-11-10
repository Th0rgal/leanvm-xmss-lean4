import Spec.Merkle.Basic
import Model.Keccak.Scalar

namespace LeanVmXmss.Model.Merkle

open Spec.Field (E)
abbrev Digest := Spec.Merkle.Digest

def hashLeaf (b : ByteArray) : Digest := Spec.Merkle.toDigest (Keccak.keccak256 b)

def compress (left right : Digest) : Digest :=
  hashLeaf (Spec.Merkle.digestBytes left ++ Spec.Merkle.digestBytes right)

def hashToScalars (d : ByteArray) : E × E :=
  (⟨Spec.Keccak.wordAt d 0, Spec.Keccak.wordAt d 8, 0⟩,
   ⟨Spec.Keccak.wordAt d 16, Spec.Keccak.wordAt d 24, 0⟩)

def hashRow (row : Array UInt64) (leafWords : Nat) : Digest :=
  hashLeaf (Spec.Merkle.leafImage row leafWords)

def build := Spec.Merkle.build
def inclusionPath := Spec.Merkle.inclusionPath
def pathRoot := Spec.Merkle.pathRoot
def verifyPath := Spec.Merkle.verifyPath

end LeanVmXmss.Model.Merkle
