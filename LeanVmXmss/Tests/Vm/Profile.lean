import Model.Vm.Scheduled

namespace LeanVmXmss.Tests.Vm.Profile

open Spec.Vm Spec.Xmss

def liftError [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

def writes (n : Nat) (m : Memory) : Except Fault Memory := do
  let mut m := m
  for i in [:n] do
    m ← m.put i Spec.Field.one
  return m

def sharedWrites (n : Nat) (m : Memory) : Except Fault (Memory × UInt64) := do
  let mut m := m
  let mut checksum : UInt64 := 0
  for i in [:n] do
    let before := m
    m ← m.put i Spec.Field.one
    checksum := checksum ^^^ (before.get i).word.c0
  return (m, checksum)

def linkedWrites (n : Nat) (m : Memory) : Except Fault Memory := do
  let mut m := m
  for i in [:n] do
    m ← m.link (2*i) (2*i+1)
  for i in [:n] do
    m ← m.put (2*i) Spec.Field.one
  return m

def powerLookups (n : Nat) (g : GPow) : Except Fault UInt64 := do
  let mut checksum : UInt64 := 0
  for i in [:n] do
    let value ← g.power (i % g.powers.size)
    checksum := checksum ^^^ value.c0
  return checksum

def countLookups (n : Nat) : UInt64 := Id.run do
  let mut checksum : UInt64 := 0
  for i in [:n] do
    checksum := checksum ^^^ (count (i % 1024)).c0
  return checksum

@[noinline] def report (label : String) (action : Unit → IO UInt64) : IO Unit := do
  let start ← IO.monoNanosNow
  let value ← action ()
  let finish ← IO.monoNanosNow
  IO.println s!"MICRO label={label} elapsed_ns={finish-start} checksum={value}"

def run (name : String) (n : Nat) : IO Unit := do
  match name with
  | "owned" => report name fun _ => do
    let m ← liftError (({} : Memory).ensure 262143)
    let m ← liftError (writes n m)
    return (m.get (n-1)).word.c0
  | "shared" => report name fun _ => do
    let m ← liftError (({} : Memory).ensure 262143)
    let (m, checksum) ← liftError (sharedWrites n m)
    return checksum ^^^ (m.get (n-1)).word.c0
  | "links" => report name fun _ => do
    let m ← liftError (linkedWrites n {})
    return (m.get (2*n-1)).word.c0
  | "count" => report name (fun _ => pure (countLookups n))
  | "powers" => report name fun _ => do
    let start ← IO.monoNanosNow
    let g := ({} : GPow).grow n
    let size := g.powers.size
    let boundary ← liftError (g.power 8668972)
    let stop ← IO.monoNanosNow
    IO.println s!"POWERS_GROW elapsed_ns={stop-start} size={size} boundary={boundary.c0}"
    liftError (powerLookups 100000 g)
  | _ => throw (IO.userError "expected owned/shared/links/count/powers")

end LeanVmXmss.Tests.Vm.Profile

def main (args : List String) : IO Unit := do
  match args with
  | [name, n] =>
    let some n := n.toNat? | throw (IO.userError "invalid benchmark size")
    LeanVmXmss.Tests.Vm.Profile.run name n
  | _ => throw (IO.userError "expected benchmark name")
