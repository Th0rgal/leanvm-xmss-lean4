import Lean
import Proofs.KeccakGkr.FlatBuckets

open Lean Elab Command

run_cmd do
  let env ← getEnv
  for name in #[`LeanVmXmss.Model.KeccakGkr.productBucketLoop,
                `LeanVmXmss.Proofs.KeccakGkr.productBucketLoop_refines_fold,
                `LeanVmXmss.Proofs.KeccakGkr.productBucket_refines] do
    let some info := env.find? name | throwError "Missing candidate declaration {name}"
    if info.isUnsafe || Lean.isExtern env name then
      throwError "Non-pure candidate declaration {name}"
    for dependency in (← Lean.collectAxioms name) do
      unless #[`propext, `Quot.sound].contains dependency do
        throwError "Forbidden dependency {dependency} in {name}"
  logInfo "FLAT_BUCKET_STRICT_AUDIT_PASS"

namespace LeanVmXmss.Tests.KeccakGkr.FlatBucketCheck

open Model.KeccakGkr
open Model.Pcs.Ntt (foldRange foldRangeLoop)
open Spec.Field (E)

def words (seed : UInt64) (count : Nat) : ByteArray :=
  foldRange count
    (fun bytes i =>
      let x := UInt64.ofNat i + seed
      pushWordLE bytes ((x * (0x9e3779b97f4a7c15 : UInt64)) ^^^ (x <<< 31) ^^^ (x >>> 7)))
    (ByteArray.emptyWithCapacity (count * 8))

def check : Bool := Id.run do
  let normal : PlanarE := ⟨words 0x1234 1619, words 0xfedcba98 1619,
    words 0x8000000000000000 1619⟩
  let short : PlanarE := ⟨normal.c0.extract 0 13, ByteArray.empty,
    normal.c2.extract 0 (normal.c2.size - 3)⟩
  let polys := words 0x9abcdef0 1619
  let mut ok := true
  for weights in #[normal, short, planarEEmpty 0] do
    for input in #[polys, polys.extract 0 11] do
      for count in #[0, 1, 2, 63, 64, 65, 1599, 1600, 1601] do
        for start in #[0, 1, 17] do
          for bit in #[(0 : UInt64), 1, 23, 46, 63, 64] do
            let acc : E := ⟨0x8000000000000001, 0x1122334455667788, 0xfedcba9876543210⟩
            let expected := foldRangeLoop
              (fun a pos => maskedAddE a (planarEGet weights pos) (readWordLE input pos) bit)
              count start acc
            let got := productBucketLoop weights input bit count start acc.c0 acc.c1 acc.c2
            ok := ok && decide (got = expected)
  return ok

end LeanVmXmss.Tests.KeccakGkr.FlatBucketCheck

def main : IO Unit := do
  unless LeanVmXmss.Tests.KeccakGkr.FlatBucketCheck.check do
    throw (IO.userError "Flat product bucket differential failed")
  IO.println "PASS: scalar product bucket vs original fold (972 cases, full/short/empty buffers, tails, shifts, nonzero accumulators)"
