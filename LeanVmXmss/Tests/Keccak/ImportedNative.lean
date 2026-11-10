import Lean
import Model.Keccak.Registers

open Lean Elab Command

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

run_cmd do
  for i in List.range 25 do
    let suffix := if i < 10 then "0" ++ toString i else toString i
    let original := (`LeanVmXmss.Model.Keccak).str ("lane" ++ suffix)
    let target := (`LeanVmXmss.Tests.Keccak.ImportedNative).str ("lane" ++ suffix)
    let some (.defnInfo info) := (← getEnv).find? original
      | throwError "Missing scalar lane {original}"
    liftCoreM <| addAndCompile (.defnDecl { info with name := target })
    let command := "attribute [export shard_b_imported_lane_" ++ suffix ++ "] " ++ target.toString
    let .ok stx := Parser.runParserCategory (← getEnv) `command command
      | throwError "Invalid scalar export"
    elabCommand stx
    let proof := "theorem " ++ target.toString ++ "_refines : " ++ target.toString ++
      " = " ++ original.toString ++ " := rfl"
    let .ok proofStx := Parser.runParserCategory (← getEnv) `command proof
      | throwError "Invalid scalar refinement"
    elabCommand proofStx

run_cmd do
  let mut source := "@[export shard_b_imported_permutation]\ndef LeanVmXmss.Tests.Keccak.ImportedNative.permutation (x y : UInt64) : UInt64 :=\n"
  let mut state := #["x", "y"] ++ Array.replicate 23 "0"
  for round in List.range 24 do
    let constant := mkApp (mkConst `LeanVmXmss.Model.Keccak.roundConstant) (mkNatLit round)
    let value ← liftTermElabM <| Meta.evalExpr UInt64 (mkConst ``UInt64) constant
    let args := String.intercalate " " state.toList ++ " " ++ toString value.toNat
    let mut next := #[]
    for i in List.range 25 do
      let suffix := if i < 10 then "0" ++ toString i else toString i
      let localName := "r" ++ toString round ++ "_" ++ suffix
      source := source ++ "  let " ++ localName ++ " := LeanVmXmss.Tests.Keccak.ImportedNative.lane" ++ suffix ++ " " ++ args ++ "\n"
      next := next.push localName
    state := next
  source := source ++ "  " ++ state[0]!
  let .ok stx := Parser.runParserCategory (← getEnv) `command source
    | throwError "Invalid scalar permutation"
  elabCommand stx
