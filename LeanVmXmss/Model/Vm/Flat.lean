import Model.Vm.Linear
import Model.Pcs.Ntt
import Model.Keccak.Registers

namespace LeanVmXmss.Model.Vm.Flat

open Spec.Vm
open Spec.Field (E)
open Model.Pcs.Ntt (foldRange)

structure FlatState where
  m : Memory := {}
  pc : Nat := 0
  fp : Nat := 0
  nextFree : Nat := 0
  g : GPow := {}
  cycles : Nat := 0
  counts : Array Nat := Array.replicate 6 0

def flatOf (m : @& Memory) : Memory := m

def toMemory (m : @& Memory) : Memory := m

def putValsF (m : Memory) (b : Nat) (vs : @& Array E) : Except Fault Memory :=
  foldRange vs.size (fun r i => do
    putLinear (← r) (b + i) (vs[i]?.getD Spec.Field.zero)) (.ok m)

def reserveFlat (m : Memory) (pc fp nf : Nat) (g : GPow) (cyc : Nat) (cnt : Array Nat)
    (ptr sz : Nat) : Except Fault FlatState := do
  if (cellAt m.cells (fp + ptr)).written then
    return ⟨m, pc, fp, nf, g, cyc, cnt⟩
  let e := nf + sz
  if e >= maxCells then
    throw .outOfMemory
  let g := growLinear g e
  let m1 ← ensureLinear m e
  let m2 ← putLinear m1 (fp + ptr) (← powerLinear g nf)
  return ⟨m2, pc, fp, e, g, cyc, cnt⟩

def popWit (m : Memory) (pc fp nf : Nat) (g : GPow) (cyc : Nat) (cnt : Array Nat)
    (st : Array Stream) (nm : String) (b n : Nat) : Except Fault (FlatState × Array Stream) := do
  let some i := st.findIdx? (·.name == nm) | throw (.witness nm)
  let some sr := st[i]? | throw (.witness nm)
  let some vs := sr.entries[sr.next]? | throw (.witness nm)
  if vs.size != n then
    throw (.witness nm)
  let m1 ← putValsF m b vs
  return (⟨m1, pc, fp, nf, g, cyc, cnt⟩, st.set! i { sr with next := sr.next + 1 })

def applyHintFlat (h : @& RHint) (p : FlatState × Array Stream) :
    Except Fault (FlatState × Array Stream) := do
  let (⟨m, pc, fp, nf, g, cyc, cnt⟩, st) := p
  match h with
  | .frameAddress o =>
    return (⟨m, pc, fp, nf, growLinear g (fp + o), cyc, cnt⟩, st)
  | .alloc p sz =>
    return (← reserveFlat m pc fp nf g cyc cnt p sz, st)
  | .allocDyn p sz =>
    let c ← countOfLinear g (cellAt m.cells (fp + sz)).word 28
    return (← reserveFlat m pc fp nf g cyc cnt p c, st)
  | .allocFrames p sz eo si tl =>
    let prod := Model.Field.nativeMul (← inK (cellAt m.cells (fp + eo)).word) si
    let c ← countOfLinear g ⟨prod, 0, 0⟩ 28
    return (← reserveFlat m pc fp nf g cyc cnt p (sz * c + tl), st)
  | .witnessStack nm b n =>
    popWit m pc fp nf g cyc cnt st nm (fp + b) n
  | .witnessHeap nm p lo n =>
    let hb ← logLinear g (cellAt m.cells (fp + p)).word
    popWit m pc fp nf g cyc cnt st nm (hb + lo) n
  | .log2Ceil bs d nb fl =>
    let b ← bitsBaseLinear m.cells fp g bs
    let v := foldRange nb (fun v i =>
      if !wordBEq (cellAt m.cells (b + i)).word Spec.Field.zero then v ||| (1 <<< i) else v) 0
    let w := Spec.Xmss.count (max (if v <= 1 then 0 else (v - 1).log2 + 1) fl)
    return (⟨← putLinear m (fp + d) w, pc, fp, nf, g, cyc, cnt⟩, st)
  | .bitDecompose v bs nb st0 =>
    if st0 + nb > 192 then
      throw .badProgram
    let n := limbsInteger (cellAt m.cells (fp + v)).word
    let b ← bitsBaseLinear m.cells fp g bs
    let vs := (Array.range nb).map fun i => Spec.Field.embed (if n.testBit (st0 + i) then 1 else 0)
    return (⟨← putValsF m b vs, pc, fp, nf, g, cyc, cnt⟩, st)
  | .bitDecomposeExp v bs nb =>
    let n ← countOfLinear g (cellAt m.cells (fp + v)).word nb
    let b ← bitsBaseLinear m.cells fp g bs
    let vs := (Array.range nb).map fun i => Spec.Field.embed (if n.testBit i then 1 else 0)
    return (⟨← putValsF m b vs, pc, fp, nf, g, cyc, cnt⟩, st)
  | .digitDecomposeExp v d nb nd db st0 sc =>
    let n ← countOfLinear g (cellAt m.cells (fp + v)).word nb
    let s0 ← (match sc with
      | none => pure st0
      | some o => countOfLinear g (cellAt m.cells (fp + o)).word 7)
    let b ← bitsBaseLinear m.cells fp g d
    let vs := (Array.range nd).map fun i => Spec.Xmss.count ((n >>> (s0 + db * i)) % 2 ^ db)
    return (⟨← putValsF m b vs, pc, fp, nf, g, cyc, cnt⟩, st)
  | .windowsExp v d o st0 w c =>
    if st0 + w * c > 192 then
      throw .badProgram
    let n := limbsInteger (cellAt m.cells (fp + v)).word
    let b ← bitsBaseLinear m.cells fp g d
    let vs := (Array.range c).map fun i => Spec.Xmss.count ((n >>> (st0 + w * i)) % 2 ^ w)
    return (⟨← putValsF m (b + o) vs, pc, fp, nf, g, cyc, cnt⟩, st)
  | .fieldLimbs v b n =>
    if n < 1 || n > 3 then
      throw .badProgram
    let x := (cellAt m.cells (fp + v)).word
    let vs := (#[x.c0, x.c1, x.c2].extract 0 n).map Spec.Field.embed
    return (⟨← putValsF m (fp + b) vs, pc, fp, nf, g, cyc, cnt⟩, st)
  | .inverse v d =>
    let inv := inverseLinear (cellAt m.cells (fp + v)).word
    return (⟨← putLinear m (fp + d) inv, pc, fp, nf, g, cyc, cnt⟩, st)
  | .print .. =>
    return (⟨m, pc, fp, nf, g, cyc, cnt⟩, st)

def stepBodyFast (op : @& Op) (m : Memory) (oldPc oldFp : Nat) (counts : Array Nat)
    (g : @& GPow) : Except Fault (Memory × Nat × Nat × Array Nat × Array Nat) := do
  let fp := oldFp
  let (m, pc, fp', addrs) ← (match op with
    | .set o v => do
      pure (← putLinear m (fp + o) v, oldPc + 1, fp, #[fp + o])
    | .xor a b c | .mul a b c => do
      let isM := match op with
        | .mul .. => true
        | _ => false
      let aa := fp + a
      let ab := fp + b
      let ac := fp + c
      let ha := (cellAt m.cells aa).written
      let hb := (cellAt m.cells ab).written
      let m ←
        if isM && (cellAt m.cells ac).written && (ha != hb) then
          let k := (cellAt m.cells (if ha then aa else ab)).word
          if wordBEq k Spec.Field.zero then
            Except.error .backSolveThroughZero
          else
            let q := Model.Field.nativeKaratsuba (cellAt m.cells ac).word (inverseLinear k)
            putLinear m (if ha then ab else aa) q
        else
          pure m
      let (va, m1) ← readLinear m aa
      let (vb, m2) ← readLinear m1 ab
      let vc :=
        if isM then Model.Field.nativeKaratsuba va vb
        else ⟨va.c0 ^^^ vb.c0, va.c1 ^^^ vb.c1, va.c2 ^^^ vb.c2⟩
      pure (← putLinear m2 ac vc, oldPc + 1, fp, #[aa, ab, ac])
    | .deref o1 o2 o3 mode => do
      let (p, m1) ← readLinear m (fp + o1)
      let a2 := (← logLinear g p) + o2
      let a3 := fp + o3
      let m2 ← (match mode with
        | .cell =>
          if (cellAt m1.cells a2).written then
            let w := (cellAt m1.cells a2).word
            putLinear m1 a3 w
          else if (cellAt m1.cells a3).written then
            let w := (cellAt m1.cells a3).word
            putLinear m1 a2 w
          else
            linkLinear m1 a2 a3
        | .pc => do
          putLinear m1 a2 (← powerLinear g (oldPc + 2))
        | .fp => do
          putLinear m1 a2 (← powerLinear g fp))
      pure (m2, oldPc + 1, fp, #[fp + o1, a2, a3])
    | .jump oc od of => do
      let (c, m1) ← readLinear m (fp + oc)
      let (d, m2) ← readLinear m1 (fp + od)
      let (f, m3) ← readLinear m2 (fp + of)
      for v in #[c, d, f] do
        if v.c1.toNat != 0 || v.c2.toNat != 0 then
          throw (.notInK v)
      let (pc, fp') ←
        if c.c0.toNat != 0 then do
          pure (← logLinear g d, ← logLinear g f)
        else
          pure (oldPc + 1, fp)
      pure (m3, pc, fp', #[fp + oc, fp + od, fp + of])
    | .keccak msg tl b8 cp out inO outO => do
      if msg.size != 4 then
        throw .badProgram
      let ins := (msg ++ (Array.range 4).map (tl + ·) |>.push b8) ++ (Array.range 4).map (cp + ·)
      let (m1, cs) ← foldRange ins.size (fun r i => do
        let (mc, cs) ← r
        let (v, mn) ← readLinear mc (fp + (ins[i]?.getD 0))
        if v.c2.toNat != 0 then
          throw (.notCanonical v)
        else
          pure (mn, cs.push v)) (.ok (m, #[]))
      let stIn := Model.Keccak.State25.fromSpec (KeccakInternal.stateOfCells inO cs)
      let res := KeccakInternal.cellsOfState outO (Model.Keccak.keccakF1600 stIn).toSpec
      let addrs := ins.map (fp + ·) ++ (Array.range 13).map (fp + out + ·)
      pure (← putValsF m1 (fp + out) res, oldPc + 1, fp, addrs))
  return (m, pc, fp', counts.modify (opcode op) (· + 1), addrs)

def stepFlat (op : @& Op) (s : FlatState) : Except Fault FlatState := do
  let ⟨m0, oldPc, oldFp, nextFree, g0, cycles, counts0⟩ := s
  let g := growLinear g0 (max (oldPc + 2) oldFp)
  let (m1, pc, fp, counts, addrs) ← stepBodyFast op m0 oldPc oldFp counts0 g
  let m2 ← foldRange addrs.size (fun r i => do
    bumpLinear (← r) (addrs[i]?.getD 0)) (.ok m1)
  return ⟨m2, pc, fp, nextFree, g, cycles + 1, counts⟩

def scheduledRunFlat (fuel : Nat) (program : @& Array Op) (hints : @& Array (Array RHint))
    (s : FlatState) (st : Array Stream) : Except Fault (FlatState × Array Stream) := do
  let mut cur := s
  let mut streams := st
  for _ in [:fuel] do
    if cur.pc + 1 == program.size && cur.fp == 0 then
      return (cur, streams)
    let some op := program[cur.pc]? | throw .badProgram
    let (rdy, st') ← (hints[cur.pc]?.getD #[]).foldlM (fun acc h => applyHintFlat h acc) (cur, streams)
    cur ← stepFlat op rdy
    streams := st'
  throw .stepLimit

end LeanVmXmss.Model.Vm.Flat
