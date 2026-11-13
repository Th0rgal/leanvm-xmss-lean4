import Model.Pcs.Commit
import Model.Merkle.Flat
import Native.Kernels.Keccak8x

namespace LeanVmXmss.Model.Pcs.MerkleBatch

open Model.Pcs.Ntt (Vec8 foldRange)
open Model.Merkle (Digest32)

/-- Pack only the requested subtree, preserving the model's default-zero reads. -/
def packVec8Rows (encoded : @& Array Vec8) (nVecs base rows : Nat) : ByteArray :=
  foldRange (rows * nVecs) (fun out i =>
    let v := encoded.getD (base * nVecs + i) default
    let out := Native.Kernels.Ntt.pushU64LE out v.w0
    let out := Native.Kernels.Ntt.pushU64LE out v.w1
    let out := Native.Kernels.Ntt.pushU64LE out v.w2
    let out := Native.Kernels.Ntt.pushU64LE out v.w3
    let out := Native.Kernels.Ntt.pushU64LE out v.w4
    let out := Native.Kernels.Ntt.pushU64LE out v.w5
    let out := Native.Kernels.Ntt.pushU64LE out v.w6
    Native.Kernels.Ntt.pushU64LE out v.w7)
    (ByteArray.emptyWithCapacity (rows * nVecs * 64))

/-- Batch the 64-word padded L0 leaf format in a bounded subtree scratch buffer.
The native kernel always hashes 64 words; it must not be used for extension leaves.
Trees outside the 8–1024-leaf batch range and widths outside the model's eight-vector format keep the scalar path. -/
def subtreeRootBuf (st1 st2 st3 : Model.Keccak.State25)
    (encoded : @& Array Vec8) (nVecs k base : Nat) : Digest32 :=
  if decide (1 ≤ nVecs ∧ nVecs ≤ 8 ∧ 3 ≤ k ∧ k ≤ 10) then
    let rows := 1 <<< k
    let packed := packVec8Rows encoded nVecs base rows
    let root := Native.Kernels.Keccak8x.lean_xmss_merkle_subtree_root_chunk
      packed 0 rows (8 * nVecs) 64
    match Digest32.fromBytesFast root with
    | some digest => digest
    | none => Model.Pcs.Commit.subtreeRootBuf st1 st2 st3 encoded nVecs k base
  else
    Model.Pcs.Commit.subtreeRootBuf st1 st2 st3 encoded nVecs k base

end LeanVmXmss.Model.Pcs.MerkleBatch
