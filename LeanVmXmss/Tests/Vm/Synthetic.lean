import Model.Vm.Scheduled

namespace LeanVmXmss.Tests.Vm.Synthetic

open Spec.Vm

def k (n : UInt64) : Spec.Field.E := ⟨n, 0, 0⟩
def set (o : Nat) (n : UInt64) : Op := .set o (k n)

def cases : Array (String × Array Op) := #[
  ("xor", #[set 2 5, set 3 9, .xor 2 3 4]),
  ("mul", #[set 2 5, set 3 9, .mul 2 3 4]),
  ("backsolve", #[set 2 5, set 4 45, .mul 2 3 4]),
  ("zero-backsolve", #[set 2 0, set 4 1, .mul 2 3 4]),
  ("conflict", #[set 2 5, set 2 9]),
  ("deref-link", #[set 2 8, .deref 2 1 5 .cell, set 4 11]),
  ("wild-pointer", #[set 2 0, .deref 2 0 5 .cell]),
  ("deref-pc", #[set 2 8, .deref 2 1 5 .pc]),
  ("deref-fp", #[set 2 8, .deref 2 1 5 .fp]),
  ("unwritten-read", #[.xor 2 3 4])]

def faultName : Fault → String
  | .conflict .. => "conflict"
  | .backSolveThroughZero => "backSolveThroughZero"
  | .wildPointer .. => "wildPointer"
  | fault => reprStr fault

def report (name : String) (result : Except Fault Runtime) : String :=
  match result with
  | .error fault => s!"{name}|error|{faultName fault}"
  | .ok runtime =>
    let s := runtime.state
    let words := (Array.range 16).map fun i =>
      let x := (s.memory.get i).word
      s!"{x.c0}:{x.c1}:{x.c2}"
    s!"{name}|ok|{s.cycles}|{s.opcodeCounts.toList}|{s.memory.unconstrainedReads.toList}|{String.intercalate "," words.toList}"

def run : IO Unit := do
  for (name, ops) in cases do
    let program := ops ++ Array.replicate (8-ops.size) (set 15 0)
    let result := do
      let state ← Model.Vm.initial 16 #[k 0, k 0] program.size
      Model.Vm.scheduledRun 32 program #[] ⟨state, #[]⟩
    IO.println (report name result)

end LeanVmXmss.Tests.Vm.Synthetic

def main : IO Unit := LeanVmXmss.Tests.Vm.Synthetic.run
