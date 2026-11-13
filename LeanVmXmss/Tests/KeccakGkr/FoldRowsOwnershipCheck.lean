import Lean
import Proofs.KeccakGkr.FoldRows
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for name in #[`LeanVmXmss.Model.KeccakGkr.foldRowsFlat,
                `LeanVmXmss.Proofs.KeccakGkr.foldRowsFlat_refines_reference] do
    let some info := env.find? name | throwError "Missing fold declaration {name}"
    if info.isUnsafe || Lean.isExtern env name then throwError "Non-pure fold {name}"
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Quot.sound].contains ax do throwError "Forbidden axiom {ax}"
  logInfo "FOLD_ROWS_OWNERSHIP_STRICT_AUDIT_PASS"
namespace LeanVmXmss.Tests.KeccakGkr.FoldRowsOwnershipCheck
open Model.KeccakGkr
open Model.Pcs.Ntt (foldRange)
open Spec.Field (E zero one)
open Spec.KeccakGkr (bitCount)
@[noinline] def makeTape (kind : Nat) : RoundETape :=
  let count := bitCount * 16
  let cur := foldRange count
    (fun p i =>
      let x := UInt64.ofNat i
      planarEPush p ⟨x * (0x9e3779b97f4a7c15 : UInt64), x ^^^ (0xfedcba9876543210 : UInt64), x + (0x8000000000000000 : UInt64)⟩)
    (planarEEmpty count)
  if kind == 0 then ⟨cur, planarEAlloc count⟩
  else if kind == 1 then ⟨cur, cur⟩
  else ⟨⟨cur.c0.extract 0 13, ByteArray.empty, cur.c2⟩,
        ⟨cur.c0.extract 0 17, cur.c1.extract 0 1, ByteArray.empty⟩⟩
@[noinline] def oldResult (kind rows : Nat) (challenge : E) : RoundETape :=
  Proofs.KeccakGkr.foldRowsReference (makeTape kind) rows challenge
@[noinline] def newResult (kind rows : Nat) (challenge : E) : RoundETape :=
  foldRowsFlat (makeTape kind) rows challenge
def same (a b : RoundETape) : Bool :=
  a.cur.c0 == b.cur.c0 && a.cur.c1 == b.cur.c1 && a.cur.c2 == b.cur.c2 &&
  a.nxt.c0 == b.nxt.c0 && a.nxt.c1 == b.nxt.c1 && a.nxt.c2 == b.nxt.c2
def check : Bool := Id.run do
  let mut ok := true
  for kind in #[0,1,2] do
    for rows in #[0,1,2,3,4,7,8,17] do
      for challenge in #[(zero : E), one, ⟨0x8000000000000001,0x1122334455667788,0xfedcba9876543210⟩] do
        ok := ok && same (oldResult kind rows challenge) (newResult kind rows challenge)
  return ok
end LeanVmXmss.Tests.KeccakGkr.FoldRowsOwnershipCheck
def main : IO Unit := do
  unless LeanVmXmss.Tests.KeccakGkr.FoldRowsOwnershipCheck.check do
    throw (IO.userError "Row-fold ownership differential failed")
  IO.println "PASS: row fold vs original (72 cases: unique, aliased, truncated tapes; zero/odd/tail rows; F192 challenges)"
