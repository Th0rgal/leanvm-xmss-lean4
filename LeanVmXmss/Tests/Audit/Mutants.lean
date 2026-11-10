/-
W5 Maxwell (Wave 1) · Category 4 · Negative mutants for the Lean VM model
==========================================================================
This suite drives `LeanVmXmss.Model.Vm.run` (the faithful interpreter) against
an honest baseline program and four corrupted variants. Every mutant must be
rejected — by a fault, by a divergent result, or by a non-empty
`Memory.unconstrainedReads` (the model-level analog of the prover's
`ProveError::UnconstrainedReads`). If any mutant passes as honest, this module
fails the build.

  baseline        #[set 2 5, xor 0 2 3, set 4 9]   PI [7, 2]    -> mem[3] = 7^5 = 2
  c4a-semantic    xor 0 2 3 :=> mul 0 2 3           PI [7, 2]    -> mem[3] = 7*5 = 35 ≠ 2
  c4a-fault       set :=> keccak of arity 3         PI [7, 2]    -> Fault.badProgram
  c4b             reads an unwritten frame cell     PI [7, 2]    -> unconstrainedReads = [4]
  c4c-badpc       jumps to pc 6 with program size 3 PI [1, 2^6]  -> Fault.badProgram
  c4c-steplimit   self-loop jump, fuel 10           PI [1, 1]    -> Fault.stepLimit
-/
import Spec.Vm.Basic
import Model.Vm.Interpreter

namespace LeanVmXmss.Tests.Audit.Mutants

open LeanVmXmss.Spec.Vm
open LeanVmXmss.Model.Vm

abbrev E := Spec.Field.E

def v (x : UInt64) : E := ⟨x, 0, 0⟩
def k (n : Nat) : E := ⟨(2^n : UInt64), 0, 0⟩

def runProgram (fuel : Nat) (program : Array Op) (pi : Array E) : Except Fault State :=
  match initial 2 pi program.size with
  | .error f => .error f
  | .ok s => run fuel program s

def jsonEscape (s : String) : String := s.replace "\\" "\\\\" |>.replace "\"" "\\\""

structure Mutant where
  name : String
  rejected : Bool
  detail : String

def mutantJson (_m : Mutant) : String :=
  "{\"name\":\"" ++ jsonEscape _m.name ++ "\",\"rejected\":" ++
    (if _m.rejected then "true" else "false") ++
    ",\"detail\":\"" ++ jsonEscape _m.detail ++ "\"}"

def run : IO Unit := do
  -- honest baseline
  let baseProgram : Array Op := #[.set 2 (v 5), .xor 0 2 3, .set 4 (v 9)]
  match runProgram 16 baseProgram #[v 7, v 2] with
  | .error f => throw (IO.userError s!"w5-4 baseline faulted: {repr f}")
  | .ok baseState =>
    let baseWord := baseState.memory.get 3 |>.word
    if baseWord.c0 != 2 then
      throw (IO.userError s!"w5-4 baseline mem[3].c0 = {baseWord.c0} (expected 2)")
    let mut out : Array String := #[]
    let mut failures : Nat := 0

    -- c4a semantic: XOR :=> MUL changes the computed word
    let semProgram : Array Op := #[.set 2 (v 5), .mul 0 2 3, .set 4 (v 9)]
    match runProgram 16 semProgram #[v 7, v 2] with
    | .error f =>
      out := out.push (mutantJson ⟨"c4a_opcode_mul_replaces_xor", false, s!"unexpected fault {repr f}"⟩)
      failures := failures + 1
    | .ok s =>
      let w := s.memory.get 3 |>.word
      if w.c0 != baseWord.c0 then
        out := out.push (mutantJson ⟨"c4a_opcode_mul_replaces_xor", true, s!"honest={baseWord.c0} mutated={w.c0}"⟩)
      else
        out := out.push (mutantJson ⟨"c4a_opcode_mul_replaces_xor", false, "result unchanged"⟩)
        failures := failures + 1

    -- c4a fault: KECCAK with the wrong message arity
    let arityProgram : Array Op := #[.keccak #[0, 1, 2] 13 26 39 52 false false, .set 2 (v 5)]
    match runProgram 16 arityProgram #[v 7, v 2] with
    | .error f =>
      if f == Fault.badProgram then
        out := out.push (mutantJson ⟨"c4a_keccak_arity_bad_program", true, "fault badProgram"⟩)
      else
        out := out.push (mutantJson ⟨"c4a_keccak_arity_bad_program", false, s!"wrong fault {repr f}"⟩)
        failures := failures + 1
    | .ok _ =>
      out := out.push (mutantJson ⟨"c4a_keccak_arity_bad_program", false, "ran to completion"⟩)
      failures := failures + 1

    -- c4b: an op reads a frame cell that was never written
    let freeProgram : Array Op := #[.set 2 (v 5), .xor 4 4 3, .set 5 (v 9)]
    match runProgram 16 freeProgram #[v 7, v 2] with
    | .error f =>
      out := out.push (mutantJson ⟨"c4b_unconstrained_read", false, s!"unexpected fault {repr f}"⟩)
      failures := failures + 1
    | .ok s =>
      let reads := s.memory.unconstrainedReads
      if reads.size == 1 && reads[0]? == some 4 then
        out := out.push (mutantJson ⟨"c4b_unconstrained_read", true, s!"unconstrainedReads=[4] size={reads.size}"⟩)
      else
        out := out.push (mutantJson ⟨"c4b_unconstrained_read", false, s!"unconstrainedReads size={reads.size}"⟩)
        failures := failures + 1

    -- c4c: a jump lands past the end of the program
    let badPcProgram : Array Op := #[.set 2 (v 5), .jump 1 1 0, .xor 0 2 3]
    match runProgram 16 badPcProgram #[v 1, k 6] with
    | .error f =>
      if f == Fault.badProgram then
        out := out.push (mutantJson ⟨"c4c_jump_out_of_range", true, "fault badProgram"⟩)
      else
        out := out.push (mutantJson ⟨"c4c_jump_out_of_range", false, s!"wrong fault {repr f}"⟩)
        failures := failures + 1
    | .ok _ =>
      out := out.push (mutantJson ⟨"c4c_jump_out_of_range", false, "ran to completion"⟩)
      failures := failures + 1

    -- c4c: a self-looping jump exhausts the fuel
    let loopProgram : Array Op := #[.jump 0 1 0, .set 9 (v 0)]
    match runProgram 10 loopProgram #[v 1, v 1] with
    | .error f =>
      if f == Fault.stepLimit then
        out := out.push (mutantJson ⟨"c4c_jump_loop_step_limit", true, "fault stepLimit"⟩)
      else
        out := out.push (mutantJson ⟨"c4c_jump_loop_step_limit", false, s!"wrong fault {repr f}"⟩)
        failures := failures + 1
    | .ok _ =>
      out := out.push (mutantJson ⟨"c4c_jump_loop_step_limit", false, "ran to completion"⟩)
      failures := failures + 1

    if failures != 0 then throw (IO.userError s!"w5-4: {failures} category-4 mutant(s) accepted")
    let envOut ← IO.getEnv "W5_AUDIT_OUT"
    let envTmp ← IO.getEnv "TMPDIR"
    let dir := envOut.getD (envTmp.getD "/tmp/w5-audit")
    IO.FS.createDirAll (System.FilePath.mk dir)
    let json := "{\"shard\":\"W5\",\"category\":4,\"baseline\":{\"program\":\"set-xor-set\",\"mem3\":2},\"mutant_count\":" ++
      toString out.size ++ ",\"accepted_count\":0,\"all_rejected\":true,\"mutants\":[" ++
      String.intercalate "," out.toList ++ "]}\n"
    IO.FS.writeFile (System.FilePath.mk (dir ++ "/mutants-lean.json")) json
    IO.println s!"W5_LEAN_MUTANTS_DONE path={dir}/mutants-lean.json"

end LeanVmXmss.Tests.Audit.Mutants

#eval LeanVmXmss.Tests.Audit.Mutants.run
