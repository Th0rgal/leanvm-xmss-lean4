import Spec.Vm.Basic

namespace LeanVmXmss.Model.Vm

open Spec.Vm

def setStep (offset : Nat) (value : Spec.Field.E) (s : State) : Except Fault State := do
  let ⟨memory, pc, fp, nextFree, g, cycles, counts⟩ := s
  let memory ← memory.put (fp+offset) value
  let memory ← memory.bump (fp+offset)
  return ⟨memory, pc+1, fp, nextFree, g.grow (max (pc+2) fp), cycles+1,
    counts.modify 2 (·+1)⟩

def step (op : Op) (s : State) : Except Fault State :=
  match op with
  | .set offset value => setStep offset value s
  | other => Spec.Vm.step other s

def run (fuel : Nat) (program : Array Op) (s : State) : Except Fault State :=
  Nat.rec (motive := fun _ => State → Except Fault State) (fun _ => .error .stepLimit)
    (fun _ previous s =>
    if s.pc+1 == program.size && s.fp == 0 then .ok s
    else match program[s.pc]? with
      | none => .error .badProgram
      | some op => match step op s with
        | .error fault => .error fault
        | .ok next => previous next) fuel s

def initialMemory (mainFrame : Nat) (publicInput : Array Spec.Field.E) : Except Fault Memory := do
  if publicInput.size != 2 then throw .badProgram
  let m ← Spec.Vm.Memory.put {} 0 (publicInput[0]?.getD Spec.Field.zero)
  let m ← m.put 1 (publicInput[1]?.getD Spec.Field.zero)
  let m ← m.ensure (max mainFrame 2 - 1)
  return m

def initialWithPowers (mainFrame : Nat) (publicInput : Array Spec.Field.E) (g : GPow) : Except Fault State := do
  let m ← initialMemory mainFrame publicInput
  return {memory := m, nextFree := mainFrame, g}

def initial (mainFrame : Nat) (publicInput : Array Spec.Field.E) (programSize : Nat) : Except Fault State :=
  initialWithPowers mainFrame publicInput
    (({} : GPow).grow (max (programSize+2) (max mainFrame 65536)))

end LeanVmXmss.Model.Vm
