import Model.KeccakGkr.Flat
import Proofs.Pcs.Refinement

namespace LeanVmXmss.Proofs.KeccakGkr

open Model.KeccakGkr
open Spec.Field (E zero)
open Model.Pcs.Ntt (foldRange foldRangeLoop)

/-- All lengths, offsets, bit shifts and malformed/truncated buffers preserve the
existing total fold semantics. No alignment or field-arithmetic assumption. -/
theorem productBucketLoop_refines_fold (weights : PlanarE) (polys : ByteArray)
    (bit : UInt64) (remaining idx : Nat) (acc : E) :
    productBucketLoop weights polys bit remaining idx acc.c0 acc.c1 acc.c2 =
      foldRangeLoop
        (fun a pos => maskedAddE a (planarEGet weights pos) (readWordLE polys pos) bit)
        remaining idx acc := by
  cases acc
  rfl

/-- Exact replacement of the pre-optimization inner product-bit loop. -/
theorem productBucket_refines (weights : PlanarE) (polys : ByteArray) (bit : UInt64) :
    productBucketLoop weights polys bit Spec.KeccakGkr.bitCount 0 0 0 0 =
      foldRange Spec.KeccakGkr.bitCount
        (fun a pos => maskedAddE a (planarEGet weights pos) (readWordLE polys pos) bit)
        zero := by
  exact productBucketLoop_refines_fold weights polys bit Spec.KeccakGkr.bitCount 0 zero

end LeanVmXmss.Proofs.KeccakGkr
