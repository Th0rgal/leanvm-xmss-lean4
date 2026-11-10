import Spec.Pcs.Ntt
import Spec.Merkle.Basic

namespace LeanVmXmss.Spec.Pcs.Commit

open Spec.Field (K)

def logBatch : Nat := 6
def leafWords : Nat := 64

def rowWords (lanes : Nat) : Nat := min leafWords ((lanes + 7) / 8 * 8)

def transpose (message : Array K) (lanes width logRows : Nat) : Array K :=
  let rows := 1 <<< logRows
  (Array.range lanes).foldl (fun out lane =>
    let destination := width - 1 - lane
    (Array.range rows).foldl (fun out rowIndex =>
      out.setIfInBounds (rowIndex * width + destination)
        (message.getD (lane * rows + rowIndex) 0)) out)
    (Array.replicate (width * rows) 0)

def replicate (block : Array K) (rate : Nat) : Array K :=
  (Array.range rate).foldl (fun acc _ => acc ++ block) #[]

def encodeMessage (message : Array K) (lanes logRows logInvRate : Nat) : Array K :=
  let width := rowWords lanes
  let first := transpose message lanes width logRows
  Ntt.encode (replicate first (1 <<< logInvRate)) width logInvRate

def leaves (codeword : Array K) (width : Nat) : Array Spec.Merkle.Digest :=
  (Array.range (codeword.size / width)).map fun pos =>
    Spec.Merkle.hashRow (codeword.extract (pos * width) ((pos + 1) * width)) leafWords

def root (message : Array K) (lanes logRows logInvRate : Nat) : ByteArray :=
  Spec.Merkle.digestBytes (Spec.Merkle.treeRoot (Spec.Merkle.build
    (leaves (encodeMessage message lanes logRows logInvRate) (rowWords lanes))))

end LeanVmXmss.Spec.Pcs.Commit
