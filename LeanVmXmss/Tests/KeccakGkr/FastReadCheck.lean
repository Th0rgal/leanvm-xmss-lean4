import Lean
import Proofs.KeccakGkr.FastRead
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for name in #[`LeanVmXmss.Model.KeccakGkr.readWordLE,
                `LeanVmXmss.Model.KeccakGkr.readWordLEReference,
                `LeanVmXmss.Proofs.KeccakGkr.readWordLE_refines_reference] do
    let some info := env.find? name | throwError "Missing read declaration {name}"
    if info.isUnsafe || Lean.isExtern env name then throwError "Non-pure read {name}"
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Quot.sound].contains ax do throwError "Forbidden axiom {ax}"
  logInfo "FAST_READ_STRICT_AUDIT_PASS"
namespace LeanVmXmss.Tests.KeccakGkr.FastReadCheck
open Model.KeccakGkr
open Model.Pcs.Ntt (foldRange)
def bytes (seed len : Nat) : ByteArray :=
  foldRange len (fun b i => b.push (UInt8.ofNat (i * 73 + seed)))
    (ByteArray.emptyWithCapacity len)
def check : Bool := Id.run do
  let mut ok := true
  for seed in #[0,1,251] do
    for len in #[0,1,7,8,9,15,16,17,23,24,31,32,33,255,256,257] do
      let b := bytes seed len
      for index in #[(0 : Nat),1,2,3,4,31,32,33,1599,1600,
        2^32-1,2^32,2^32+1,2^60,2^61-1,2^61,2^61+1,2^64-1,2^64,2^64+1] do
        ok := ok && (readWordLE b index == readWordLEReference b index)
  return ok
end LeanVmXmss.Tests.KeccakGkr.FastReadCheck
def main : IO Unit := do
  unless LeanVmXmss.Tests.KeccakGkr.FastReadCheck.check do
    throw (IO.userError "Packed word read differential failed")
  IO.println "PASS: packed word read vs original (960 cases: empty/truncated buffers, endian patterns, huge/wrapping offsets)"
