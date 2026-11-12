import Spec.Witness.Basic
import Model.Vm.Flat

namespace LeanVmXmss.Model.Witness

open Spec.Field (K E)
open Spec.Layout
open Spec.Vm
open Model.Pcs.Ntt (Vec8 foldRange foldRangeLoop)
open Model.Vm.Flat

def logInvRateDefault := Spec.Witness.logInvRateDefault
def StepTrace := Spec.Witness.StepTrace
def ExecutionTrace := Spec.Witness.ExecutionTrace
def emptyTrace := Spec.Witness.emptyTrace
def rowsOf := Spec.Witness.rowsOf
def SizedRun := Spec.Witness.SizedRun
def sizeRun := Spec.Witness.sizeRun
def WitnessBundle := Spec.Witness.WitnessBundle
def executeTrace := Spec.Witness.executeTrace
def bundleOf := Spec.Witness.bundleOf
def proveBundle := Spec.Witness.proveBundle
def announceDigest := Spec.Witness.announceDigest
def l0Root := Spec.Witness.l0Root
def challengePair := Spec.Witness.challengePair

def bumpRec (m : Memory) (a : Nat) (ex : Array Nat) : Except Fault (Memory × Array Nat) := do
  let ⟨cells, links, ur, used⟩ ← Model.Vm.ensureLinear m a
  let old := Model.Vm.cellAt cells a
  let m1 : Memory := ⟨cells.set! a { old with accesses := old.accesses + 1 }, links, ur, used⟩
  return (m1, ex.push old.accesses)

def stepTraceF (op : @& Op) (m : Memory) (oldPc oldFp : Nat) (counts : Array Nat) (g : @& GPow)
    (rc jIdx : Nat) : Except Fault (Memory × Nat × Nat × Array Nat × Nat × StepTrace) := do
  let (m1, pc, fp', counts', addrs) ← stepBodyFast op m oldPc oldFp counts g
  let (tIdx, pre, suf) := match op with
    | .xor a b c => (0, #[a, b, c], #[])
    | .mul a b c => (1, #[a, b, c], #[])
    | .set .. => (2, #[], #[])
    | .deref .. => (3, #[], #[])
    | .jump oc od of => (4, #[], #[oc, od, of, jIdx])
    | .keccak .. => (5, #[], #[])
  let (m2, bmp) ← foldRange addrs.size (fun r i => do
    let (mc, ex) ← r
    bumpRec mc (addrs[i]?.getD 0) ex) (.ok (m1, pre))
  return (m2, pc, fp', counts', tIdx, ⟨oldPc, oldFp, rc, bmp ++ suf⟩)

def runTraceLoop (fuel : Nat) (prog : @& Array Op) (hints : @& Array (Array RHint))
    (s : FlatState) (st : Array Stream) (tbls : Array (Array StepTrace)) (bc : Array Nat) :
    Except Fault (FlatState × Array (Array StepTrace) × Array Nat) := do
  let mut cur := s
  let mut streams := st
  let mut tb := tbls
  let mut bcc := bc
  for _ in [:fuel] do
    if cur.pc + 1 == prog.size && cur.fp == 0 then
      return (cur, tb, bcc)
    let some op := prog[cur.pc]? | throw .badProgram
    let (rdy, st') ← (hints[cur.pc]?.getD #[]).foldlM (fun acc h => applyHintFlat h acc) (cur, streams)
    let ⟨m0, pc0, fp0, nf, g0, cyc, cnt0⟩ := rdy
    let g := Model.Vm.growLinear g0 (max (pc0 + 2) fp0)
    let rc := bcc[pc0]?.getD 0
    let jIdx := (tb[4]?.getD #[]).size
    let (m1, pc1, fp1, cnt1, tIdx, row) ← stepTraceF op m0 pc0 fp0 cnt0 g rc jIdx
    cur := ⟨m1, pc1, fp1, nf, g, cyc + 1, cnt1⟩
    streams := st'
    tb := tb.modify tIdx (·.push row)
    bcc := bcc.set! pc0 (rc + 1)
  throw .stepLimit

def writeTableCols (h base off w : Nat) (rows : @& Array Spec.Witness.StepTrace) (pad : @& Array K)
    (proj : Nat → Spec.Witness.StepTrace → K) (out : Array (Array K)) : Array (Array K) :=
  foldRange w (fun out l =>
    let pv := pad[off + l]?.getD 0
    let col := foldRange rows.size (fun c r =>
      c.setIfInBounds r (proj l (rows[r]?.getD default))) (Array.replicate h pv)
    out.setIfInBounds (base + off + l) col) out

def bProjCell (mem : @& Memory) (g : @& GPow) (l : Nat) (r : Spec.Witness.StepTrace) : K :=
  let a := r.extras[0]?.getD 0
  let b := r.extras[1]?.getD 0
  let c := r.extras[2]?.getD 0
  let va := Spec.Witness.cellWord mem (r.fp + a)
  let vb := Spec.Witness.cellWord mem (r.fp + b)
  if l == 0 then Spec.Witness.gAt g r.pc
  else if l == 1 then Spec.Witness.gAt g r.fp
  else if l == 2 then Spec.Witness.gAt g a
  else if l == 3 then Spec.Witness.gAt g b
  else if l == 4 then Spec.Witness.gAt g c
  else if l == 5 then va.c0
  else if l == 6 then va.c1
  else if l == 7 then va.c2
  else if l == 8 then vb.c0
  else if l == 9 then vb.c1
  else if l == 10 then vb.c2
  else if l < 14 then Spec.Witness.gAt g (r.extras[l - 8]?.getD 0)
  else Spec.Witness.gAt g r.bytecodeRead

def setProjCell (prog : @& Array Op) (g : @& GPow) (l : Nat) (r : Spec.Witness.StepTrace) : K :=
  match prog[r.pc]? with
  | some (.set o v) =>
    if l == 0 then Spec.Witness.gAt g r.pc
    else if l == 1 then Spec.Witness.gAt g r.fp
    else if l == 2 then Spec.Witness.gAt g o
    else if l == 3 then v.c0
    else if l == 4 then v.c1
    else if l == 5 then v.c2
    else if l == 6 then Spec.Witness.gAt g (r.extras[0]?.getD 0)
    else Spec.Witness.gAt g r.bytecodeRead
  | _ => 0

def derefProjCell (prog : @& Array Op) (mem : @& Memory) (g : @& GPow)
    (l : Nat) (r : Spec.Witness.StepTrace) : K :=
  match prog[r.pc]? with
  | some (.deref o1 o2 o3 m) =>
    let w := Spec.Witness.cellWord mem (r.fp + o3)
    if l == 0 then Spec.Witness.gAt g r.pc
    else if l == 1 then Spec.Witness.gAt g r.fp
    else if l == 2 then Spec.Witness.gAt g o1
    else if l == 3 then Spec.Witness.gAt g o2
    else if l == 4 then Spec.Witness.gAt g o3
    else if l == 5 then derefFlagPc m
    else if l == 6 then derefFlagFp m
    else if l == 7 then (Spec.Witness.cellWord mem (r.fp + o1)).c0
    else if l == 8 then w.c0
    else if l == 9 then w.c1
    else if l == 10 then w.c2
    else if l < 14 then Spec.Witness.gAt g (r.extras[l - 11]?.getD 0)
    else Spec.Witness.gAt g r.bytecodeRead
  | _ => 0

def keccakInProjCell (prog : @& Array Op) (mem : @& Memory) (g : @& GPow)
    (l : Nat) (r : Spec.Witness.StepTrace) : K :=
  match prog[r.pc]? with
  | some op@(.keccak _ _ _ _ _ inO outO) =>
    let offs := Spec.Witness.keccakOffsets op
    if l == 0 then Spec.Witness.gAt g r.pc
    else if l == 1 then Spec.Witness.gAt g r.fp
    else if l < 10 then Spec.Witness.gAt g (offs[l - 2]?.getD 0)
    else if l == 10 then (if inO then 1 else 0)
    else if l == 11 then (if outO then 1 else 0)
    else
      let wd := Spec.Witness.cellWord mem (Spec.Witness.keccakAddress r.fp offs (if inO then 0 else 8))
      if inO then wd.c0 else wd.c1
  | _ => 0

def fillKeccakFast (prog : @& Array Op) (mem : @& Memory) (g : @& GPow)
    (kh : Nat) (kr : @& Array Spec.Witness.StepTrace) (out : Array (Array K)) : Array (Array K) :=
  let kb := tableBase ⟨5, by decide⟩
  let pad := Spec.Witness.keccakPaddingValue
  let w5a := writeTableCols kh kb 0 keccakIn kr pad (keccakInProjCell prog mem g) out
  let w5b := writeTableCols kh kb keccakCnt (2 * keccakCells) kr pad
    (fun l r => Spec.Witness.gAt g (r.extras[l]?.getD 0)) w5a
  writeTableCols kh kb keccakCntBc 1 kr pad (fun _ r => Spec.Witness.gAt g r.bytecodeRead) w5b

def fillTablesGroup (grp : Nat) (prog : @& Array Op) (sized : @& Spec.Witness.SizedRun)
    (g : @& GPow) : Array (Array K) :=
  let mem := sized.trace.memory
  let hs := sized.layout.taus.map Spec.Witness.pow2
  let used := min sized.cells mem.used
  let z := Array.replicate nColumns #[]
  if grp == 0 then
    let c0 := foldRange used (fun c i =>
      c.setIfInBounds i (Model.Vm.cellAt mem.cells i).word.c0) (Array.replicate sized.cells 0)
    z.set! 0 c0
  else if grp == 1 then
    let c1 := foldRange used (fun c i =>
      c.setIfInBounds i (Model.Vm.cellAt mem.cells i).word.c1) (Array.replicate sized.cells 0)
    z.set! 1 c1
  else if grp == 2 then
    let c2 := foldRange used (fun c i =>
      c.setIfInBounds i (Model.Vm.cellAt mem.cells i).word.c2) (Array.replicate sized.cells 0)
    z.set! 2 c2
  else if grp == 3 then
    let c3 := foldRange sized.cells (fun c i =>
      let acc := if i < mem.used then (Model.Vm.cellAt mem.cells i).accesses else 0
      c.setIfInBounds i (Spec.Witness.gAt g acc)) (Array.replicate sized.cells 0)
    let bcLen := Spec.Witness.pow2 sized.logBytecode
    let cBc := foldRange bcLen (fun c i =>
      c.setIfInBounds i (Spec.Witness.gAt g (sized.trace.bytecodeCount[i]?.getD 0)))
      (Array.replicate bcLen 0)
    (z.set! 3 c3).set! bytecodeFinal cBc
  else if grp == 4 then
    let w0 := writeTableCols (hs[0]?.getD 1) (tableBase ⟨0, by decide⟩) 0 arithWidth
      (sized.trace.tables[0]?.getD #[]) Spec.Witness.arithPadding (bProjCell mem g) z
    writeTableCols (hs[1]?.getD 1) (tableBase ⟨1, by decide⟩) 0 arithWidth
      (sized.trace.tables[1]?.getD #[]) Spec.Witness.arithPadding (bProjCell mem g) w0
  else if grp == 5 then
    let w2 := writeTableCols (hs[2]?.getD 1) (tableBase ⟨2, by decide⟩) 0 setWidth
      (sized.trace.tables[2]?.getD #[]) Spec.Witness.setPadding (setProjCell prog g) z
    let w3 := writeTableCols (hs[3]?.getD 1) (tableBase ⟨3, by decide⟩) 0 derefWidth
      (sized.trace.tables[3]?.getD #[]) Spec.Witness.derefPadding (derefProjCell prog mem g) w2
    Spec.Witness.fillJump mem g (hs[4]?.getD 1) (sized.trace.tables[4]?.getD #[]) w3
  else
    fillKeccakFast prog mem g (hs[5]?.getD 1) (sized.trace.tables[5]?.getD #[]) z

def fillTablesFast (prog : @& Array Op) (sized : @& Spec.Witness.SizedRun)
    (g : @& GPow) : Array (Array K) :=
  let mem := sized.trace.memory
  let hs := sized.layout.taus.map Spec.Witness.pow2
  let sh := Spec.Witness.fillShared sized g
  let w0 := writeTableCols (hs[0]?.getD 1) (tableBase ⟨0, by decide⟩) 0 arithWidth
    (sized.trace.tables[0]?.getD #[]) Spec.Witness.arithPadding (bProjCell mem g) sh
  let w1 := writeTableCols (hs[1]?.getD 1) (tableBase ⟨1, by decide⟩) 0 arithWidth
    (sized.trace.tables[1]?.getD #[]) Spec.Witness.arithPadding (bProjCell mem g) w0
  let w2 := Spec.Witness.fillSet prog g (hs[2]?.getD 1) (sized.trace.tables[2]?.getD #[]) w1
  let w3 := Spec.Witness.fillDeref prog mem g (hs[3]?.getD 1) (sized.trace.tables[3]?.getD #[]) w2
  let w4 := Spec.Witness.fillJump mem g (hs[4]?.getD 1) (sized.trace.tables[4]?.getD #[]) w3
  fillKeccakFast prog mem g (hs[5]?.getD 1) (sized.trace.tables[5]?.getD #[]) w4

def fillQKeccakChunk (prog : @& Array Op) (rows : @& Array Spec.Witness.StepTrace) (mem : @& Memory)
    (lo hi : Nat) : Array Model.Keccak.State25 × Array Model.Keccak.State25 :=
  foldRange (hi - lo) (fun (ins, mids) j =>
    let st := Spec.Witness.inputState25 prog mem (rows[lo + j]?.getD default)
    (ins.push st, mids.push (Model.Keccak.rounds25 keccakDepth 0 st)))
    (Array.emptyWithCapacity (hi - lo), Array.emptyWithCapacity (hi - lo))

def assembleQKeccak (nRows h : Nat)
    (chunks : @& Array (Array Model.Keccak.State25 × Array Model.Keccak.State25)) : Array K :=
  let zm := (Model.Keccak.rounds25 keccakDepth 0 Model.Layout.zeroState25).toSpec
  let base := foldRange stateLanes (fun col lane =>
    let pv := zm[lane]?.getD 0
    if pv.toNat == 0 then col
    else
      foldRange (h - nRows) (fun c o =>
        c.set! ((stateLanes + lane) * h + nRows + o) pv) col)
    (Array.replicate (qKeccakSlots * h) 0)
  (chunks.foldl (fun (col, pos) (ins, mids) =>
    let col' := foldRange ins.size (fun c j =>
      let step := pos + j
      let is := (ins[j]?.getD Model.Layout.zeroState25).toSpec
      let ms := (mids[j]?.getD Model.Layout.zeroState25).toSpec
      let c1 := foldRange stateLanes (fun c0 l => c0.set! (l * h + step) (is[l]?.getD 0)) c
      foldRange stateLanes (fun c0 l =>
        c0.set! ((stateLanes + l) * h + step) (ms[l]?.getD 0)) c1) col
    (col', pos + ins.size)) (base, 0)).1

end LeanVmXmss.Model.Witness
