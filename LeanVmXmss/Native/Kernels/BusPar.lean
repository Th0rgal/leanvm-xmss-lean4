import Native.Kernels.Bus

namespace LeanVmXmss.Native.Kernels

open Spec.Field (K E zero one)
open LeanVmXmss.Model.Prim.Slice64
open LeanVmXmss.Model.Bus (GroupedForm)

def parTasks : Nat := 16

def foldNatM {m : Type → Type} [Monad m] {α : Type} (n : Nat) (f : α → Nat → m α) (init : α) : m α :=
  Fin.foldlM n (fun acc k => f acc k.val) init

def chunkBounds (total workers idx : Nat) : Nat × Nat :=
  if workers = 0 then (0, 0)
  else
    let chunk := (total + workers - 1) / workers
    let start := idx * chunk
    let rem := if start < total then total - start else 0
    let count := if rem < chunk then rem else chunk
    (start, count)

def runRangeTasks {α : Type} (total : Nat) (workers : Nat) (f : Nat → Nat → α) : BaseIO (Array α) := do
  let w := if workers = 0 then 1 else workers
  let tasks ← foldNatM w
    (fun acc idx => do
      let (start, count) := chunkBounds total w idx
      let t := Task.spawn (fun _ => f start count)
      pure (acc.push t))
    (Array.emptyWithCapacity w)
  foldNatM tasks.size
    (fun out idx => do
      match tasks[idx]? with
      | some t =>
        let v ← IO.wait t
        pure (out.push v)
      | none => pure out)
    (Array.emptyWithCapacity tasks.size)

def busTreeRoundMessagePar (values eqWeights : SliceE) (workers : Nat := parTasks) :
    BaseIO (E × E × E × E) := do
  let storedRows := sliceESize values / 4
  let fullPairs := storedRows / 2
  let parts ← runRangeTasks fullPairs workers (fun s c =>
    busTreeRoundMessageRangeSlice values eqWeights s c)
  let msg := foldNat parts.size
    (fun acc idx => busAddMsg4 acc (parts[idx]?.getD (zero, zero, zero, zero)))
    (zero, zero, zero, zero)
  if storedRows % 2 = 1 then
    let lo := 8 * fullPairs
    let g0 := sliceEGetOr values lo one
    let g1 := sliceEGetOr values (lo + 1) one
    let g2 := sliceEGetOr values (lo + 2) one
    let g3 := sliceEGetOr values (lo + 3) one
    let w := sliceEGetOr eqWeights fullPairs zero
    return busAddMsg4 msg (busQuarticSummand g0 (busEadd g0 one) g1 (busEadd g1 one)
      g2 (busEadd g2 one) g3 (busEadd g3 one) w)
  else
    return msg

def busFoldTreePar (values : SliceE) (challenge : E) (workers : Nat := parTasks) :
    BaseIO SliceE := do
  let storedRows := sliceESize values / 4
  let fullRows := storedRows / 2
  let parts ← runRangeTasks fullRows workers (fun s c =>
    busFoldTreeRangeSlice values challenge s c)
  let parts := if storedRows % 2 = 1 then
    let lo := 8 * fullRows
    let v0 := sliceEGetOr values lo one
    let v1 := sliceEGetOr values (lo + 1) one
    let v2 := sliceEGetOr values (lo + 2) one
    let v3 := sliceEGetOr values (lo + 3) one
    let tail := sliceEPush (sliceEEmpty 4) (busInterp v0 one challenge)
    let tail := sliceEPush tail (busInterp v1 one challenge)
    let tail := sliceEPush tail (busInterp v2 one challenge)
    let tail := sliceEPush tail (busInterp v3 one challenge)
    parts.push tail
  else
    parts
  return sliceEConcat parts

def busNextLevelPar (current : SliceE) (workers : Nat := parTasks) : BaseIO SliceE := do
  let n := sliceESize current
  let fullRows := n / 4
  let parts ← runRangeTasks fullRows workers (fun s c =>
    busNextLevelRangeSlice current s c)
  let parts := if 4 * fullRows < n then
    let c0 := sliceEGetOr current (4 * fullRows) one
    let c1 := sliceEGetOr current (4 * fullRows + 1) one
    let c2 := sliceEGetOr current (4 * fullRows + 2) one
    let c3 := sliceEGetOr current (4 * fullRows + 3) one
    parts.push (sliceEPush (sliceEEmpty 1) (busEmul (busEmul c0 c1) (busEmul c2 c3)))
  else
    parts
  return sliceEConcat parts

def busFoldTableStatePar (state : Array SliceE) (r : E) (half : Nat)
    (workers : Nat := parTasks) : BaseIO (Array SliceE) := do
  let w := if workers = 0 then 1 else workers
  let allTasks ← foldNatM state.size
    (fun acc c => do
      let col := state[c]?.getD (sliceEEmpty 0)
      let colTasks ← foldNatM w
        (fun tAcc idx => do
          let (start, count) := chunkBounds half w idx
          let t := Task.spawn (fun _ => busFoldColumnRangeSlice col r half start count)
          pure (tAcc.push t))
        (Array.emptyWithCapacity w)
      pure (acc.push colTasks))
    (Array.emptyWithCapacity state.size)
  foldNatM allTasks.size
    (fun out c => do
      let colTasks := allTasks[c]?.getD #[]
      let parts ← foldNatM colTasks.size
        (fun pAcc idx => do
          match colTasks[idx]? with
          | some t =>
            let v ← IO.wait t
            pure (pAcc.push v)
          | none => pure pAcc)
        (Array.emptyWithCapacity colTasks.size)
      pure (out.push (sliceEConcat parts)))
    (Array.emptyWithCapacity allTasks.size)

def busJoinLinColPar (terms : Array (Nat × E)) (cols : Array ByteArray)
    (base : Nat) (r : E) (half : Nat) (workers : Nat := parTasks) : BaseIO SliceE := do
  let parts ← runRangeTasks half workers (fun s cnt =>
    busJoinLinColRangeSlice terms cols base r half s cnt)
  return sliceEConcat parts

def busJoinLeftColPar (kc : ByteArray) (r : E) (half : Nat)
    (workers : Nat := parTasks) : BaseIO SliceE := do
  let parts ← runRangeTasks half workers (fun s cnt =>
    busJoinLeftColRangeSlice kc r half s cnt)
  return sliceEConcat parts

def busJoinTableStatePar (gf : GroupedForm) (cols : Array ByteArray)
    (base : Nat) (r : E) (half : Nat) (workers : Nat := parTasks) : BaseIO (Array SliceE) := do
  let lin0 ← busJoinLinColPar gf.lin cols base r half workers
  foldNatM gf.groups.size
    (fun stateCols g => do
      match gf.groups[g]? with
      | none => pure stateCols
      | some (left, right) =>
        let kc := cols[base + left]?.getD ByteArray.empty
        let leftCol ← busJoinLeftColPar kc r half workers
        let rightCol ← busJoinLinColPar right cols base r half workers
        pure ((stateCols.push leftCol).push rightCol))
    #[lin0]

def busTableMessageEPar (constant : E) (state : Array SliceE) (eqr : SliceE)
    (half : Nat) (atOne : Bool) (workers : Nat := parTasks) : BaseIO (E × E) := do
  let parts ← runRangeTasks half workers (fun s cnt =>
    busTableMessageERangeSlice state eqr half atOne s cnt)
  let (eSum, sSum) := foldNat parts.size
    (fun (ea, sa) idx =>
      let (ep, sp) := parts[idx]?.getD (zero, zero)
      (busEadd ea ep, busEadd sa sp))
    (zero, zero)
  return (busEadd constant eSum, sSum)

def busTableMessageKPar (gf : GroupedForm) (cols : Array ByteArray)
    (base : Nat) (eqr : SliceE) (half : Nat) (atOne : Bool)
    (workers : Nat := parTasks) : BaseIO (E × E) := do
  let parts ← runRangeTasks half workers (fun s cnt =>
    busTableMessageKRangeSlice gf cols base eqr half atOne s cnt)
  let (eSum, sSum) := foldNat parts.size
    (fun (ea, sa) idx =>
      let (ep, sp) := parts[idx]?.getD (zero, zero)
      (busEadd ea ep, busEadd sa sp))
    (zero, zero)
  return (busEadd eSum gf.constant, sSum)

def busMleEvalPar (table : ByteArray) (eqs : SliceE) (workers : Nat := parTasks) : BaseIO E := do
  let total := sliceESize eqs
  let parts ← runRangeTasks total workers (fun s cnt =>
    busMleEvalRangeSlice table eqs s cnt)
  return foldNat parts.size
    (fun acc idx => busEadd acc (parts[idx]?.getD zero))
    zero

end LeanVmXmss.Native.Kernels
