import Model.Field.NativeKernel
import Model.Vm.Scheduled

namespace LeanVmXmss.Model.Vm

open Spec.Vm
open Spec.Field (E)

@[inline] def cellAt (cells : @& Array Cell) (address : Nat) : Cell :=
  if h : address < cells.size then cells[address] else {}

def ensureLinear (m : Memory) (address : Nat) : Except Fault Memory :=
  if address >= maxCells then .error .outOfMemory
  else
    let ⟨cells, links, ur, used⟩ := m
    let used' := max used (address + 1)
    if address < cells.size then
      .ok ⟨cells, links, ur, used'⟩
    else
      let target := max (address + 1) (max 65536 (2 * cells.size))
      let delta := target - cells.size
      .ok ⟨cells ++ Array.replicate delta {}, links, ur, used'⟩

def storeLinear (m : Memory) (address : Nat) (value : E) : Except Fault Memory :=
  match ensureLinear m address with
  | .error fault => .error fault
  | .ok ⟨cells, links, ur, used⟩ =>
    let old := cellAt cells address
    if old.written && !wordBEq old.word value then
      .error (.conflict address old.word value)
    else
      .ok ⟨cells.set! address { word := value, written := true, accesses := old.accesses }, links, ur, used⟩

def spreadLinear (fuel : Nat) (todo : List Nat) (initial : Memory) (value : E) : Except Fault Memory := do
  let mut m := initial
  let mut pending := todo
  for _ in [:fuel] do
    match pending with
    | [] => return m
    | a :: rest =>
      pending := rest
      let ⟨cells, links, ur, used⟩ := m
      let neighbors := links.toList.filterMap fun (x, y) => if x == a then some y else none
      m := ⟨cells, links.filter (fun (x, _) => x != a), ur, used⟩
      for b in neighbors do
        if !(cellAt m.cells b).written then pending := b :: pending
        m ← storeLinear m b value
  if pending.isEmpty then return m else throw .badProgram

def putLinear (m : Memory) (address : Nat) (value : E) : Except Fault Memory := do
  let linksSize := m.links.size
  let next ← storeLinear m address value
  if linksSize == 0 then return next
  else spreadLinear (linksSize + 1) [address] next value

def readLinear (m : Memory) (address : Nat) : Except Fault (E × Memory) := do
  let ⟨cells, links, ur, used⟩ ← ensureLinear m address
  let old := cellAt cells address
  if old.written then
    return (old.word, ⟨cells, links, ur, used⟩)
  else
    return (old.word, ⟨cells.set! address { old with written := true }, links, ur.push address, used⟩)

def bumpLinear (m : Memory) (address : Nat) : Except Fault Memory := do
  let ⟨cells, links, ur, used⟩ ← ensureLinear m address
  let old := cellAt cells address
  return ⟨cells.set! address { old with accesses := old.accesses + 1 }, links, ur, used⟩

def linkLinear (m : Memory) (a b : Nat) : Except Fault Memory := do
  let m ← ensureLinear m a
  let ⟨cells, links, ur, used⟩ ← ensureLinear m b
  return ⟨cells, links.push (a, b) |>.push (b, a), ur, used⟩

def inverseLinear (a : @& E) : E := Id.run do
  let mut x := Spec.Field.one
  for i in [:192] do
    x := Model.Field.nativeKaratsuba x x
    if i < 191 then x := Model.Field.nativeKaratsuba x a
  return x

def extendLinear (g : GPow) : GPow :=
  let ⟨powers, coarse⟩ := g
  let x := powers.back?.getD 1
  let value := Model.Vm.scalarGeneratorStep x
  let index := powers.size
  let coarse := if index % 64 == 0 then
    coarse.modify (value.toNat % 65536) (fun xs => (value.toNat, index) :: xs)
    else coarse
  ⟨powers.push value, coarse⟩

def extendManyLinear (k : Nat) (g : GPow) : GPow :=
  Nat.rec (motive := fun _ => GPow → GPow)
    (fun acc => acc)
    (fun _ rec acc => rec (extendLinear acc))
    k g

def growLinear (g : GPow) (n : Nat) : GPow :=
  if n < g.powers.size then g
  else extendManyLinear (n + 1 - g.powers.size) g

@[inline] def powerLinear (g : @& GPow) (n : Nat) : Except Fault E :=
  match g.powers[n]? with
  | some value => .ok ⟨value, 0, 0⟩
  | none => .error .badProgram

def logLinear (g : @& GPow) (value : E) : Except Fault Nat := do
  if value.c1.toNat != 0 || value.c2.toNat != 0 then throw (.notInK value)
  let mut y := value.c0
  for j in [:64] do
    if let some (_, index) := (g.coarse[y.toNat % 65536]?.getD []).find?
        (fun pair => pair.1 == y.toNat) then
      if index + j < g.powers.size then return index + j
    y := if y.toNat % 2 == 1 then ((y ^^^ 0x1b) >>> 1) ||| ((1 : UInt64) <<< 63) else y >>> 1
  throw (.wildPointer value)

def heapBaseLinear (cells : @& Array Cell) (fp : Nat) (g : @& GPow) (ptr : Nat) : Except Fault Nat :=
  logLinear g (cellAt cells (fp + ptr)).word

def bitsBaseLinear (cells : @& Array Cell) (fp : Nat) (g : @& GPow) (d : BitsDest) : Except Fault Nat :=
  match d with
  | .stack base => .ok (fp + base)
  | .heap ptr => heapBaseLinear cells fp g ptr

def countOfLinear (g : @& GPow) (value : E) (nbits : Nat) : Except Fault Nat := do
  let index ← logLinear g value
  if index < 2 ^ nbits then return index else throw (.wildPointer value)

def putValuesLinear (m : Memory) (base : Nat) (values : @& Array E) : Except Fault Memory := do
  let mut m := m
  for i in [:values.size] do m ← putLinear m (base + i) (values[i]?.getD Spec.Field.zero)
  return m

def reserveLinear (s : State) (ptr size : Nat) : Except Fault State := do
  let ⟨m, pc, fp, nextFree, g, cycles, counts⟩ := s
  if (cellAt m.cells (fp + ptr)).written then return ⟨m, pc, fp, nextFree, g, cycles, counts⟩
  let endOffset := nextFree + size
  if endOffset >= maxCells then throw .outOfMemory
  let g := growLinear g endOffset
  let m ← ensureLinear m endOffset
  let pval ← powerLinear g nextFree
  let m ← putLinear m (fp + ptr) pval
  return ⟨m, pc, fp, endOffset, g, cycles, counts⟩

def popWitnessLinear (r : Runtime) (name : String) (base len : Nat) : Except Fault Runtime := do
  let ⟨⟨m, pc, fp, nextFree, g, cycles, counts⟩, streams⟩ := r
  let some index := streams.findIdx? (fun stream => stream.name == name) | throw (.witness name)
  let some stream := streams[index]? | throw (.witness name)
  let some values := stream.entries[stream.next]? | throw (.witness name)
  if values.size != len then throw (.witness name)
  let m ← putValuesLinear m base values
  return ⟨⟨m, pc, fp, nextFree, g, cycles, counts⟩, streams.set! index { stream with next := stream.next + 1 }⟩

def applyHintLinear (h : @& RHint) (r : Runtime) : Except Fault Runtime := do
  let ⟨⟨m, pc, fp, nextFree, g, cycles, counts⟩, streams⟩ := r
  match h with
  | .frameAddress offset =>
    let g := growLinear g (fp + offset)
    return ⟨⟨m, pc, fp, nextFree, g, cycles, counts⟩, streams⟩
  | .alloc ptr size =>
    let s ← reserveLinear ⟨m, pc, fp, nextFree, g, cycles, counts⟩ ptr size
    return ⟨s, streams⟩
  | .allocDyn ptr size =>
    let szVal := (cellAt m.cells (fp + size)).word
    let cnt ← countOfLinear g szVal 28
    let s ← reserveLinear ⟨m, pc, fp, nextFree, g, cycles, counts⟩ ptr cnt
    return ⟨s, streams⟩
  | .allocFrames ptr size endOffset startInverse tail =>
    let span ← inK (cellAt m.cells (fp + endOffset)).word
    let cnt ← countOfLinear g ⟨Model.Field.nativeMul span startInverse, 0, 0⟩ 28
    let s ← reserveLinear ⟨m, pc, fp, nextFree, g, cycles, counts⟩ ptr (size * cnt + tail)
    return ⟨s, streams⟩
  | .witnessStack name base len =>
    popWitnessLinear ⟨⟨m, pc, fp, nextFree, g, cycles, counts⟩, streams⟩ name (fp + base) len
  | .witnessHeap name ptr lo len =>
    let hb ← heapBaseLinear m.cells fp g ptr
    popWitnessLinear ⟨⟨m, pc, fp, nextFree, g, cycles, counts⟩, streams⟩ name (hb + lo) len
  | .log2Ceil bits dst nbits floor =>
    let base ← bitsBaseLinear m.cells fp g bits
    let mut value := 0
    for i in [:nbits] do
      if !wordBEq (cellAt m.cells (base + i)).word Spec.Field.zero then
        value := value ||| (1 <<< i)
    let log := if value <= 1 then 0 else (value - 1).log2 + 1
    let m ← putValuesLinear m (fp + dst) #[Spec.Xmss.count (max log floor)]
    return ⟨⟨m, pc, fp, nextFree, g, cycles, counts⟩, streams⟩
  | .bitDecompose value bits nbits start =>
    if start + nbits > 192 then throw .badProgram
    let base ← bitsBaseLinear m.cells fp g bits
    let integer := limbsInteger (cellAt m.cells (fp + value)).word
    let m ← putValuesLinear m base
      ((Array.range nbits).map fun i => Spec.Field.embed (if integer.testBit (start + i) then 1 else 0))
    return ⟨⟨m, pc, fp, nextFree, g, cycles, counts⟩, streams⟩
  | .bitDecomposeExp value bits nbits =>
    let integer ← countOfLinear g (cellAt m.cells (fp + value)).word nbits
    let base ← bitsBaseLinear m.cells fp g bits
    let m ← putValuesLinear m base
      ((Array.range nbits).map fun i => Spec.Field.embed (if integer.testBit i then 1 else 0))
    return ⟨⟨m, pc, fp, nextFree, g, cycles, counts⟩, streams⟩
  | .digitDecomposeExp value dst nbits ndigits digitBits start startCell =>
    let integer ← countOfLinear g (cellAt m.cells (fp + value)).word nbits
    let start ← match startCell with
      | none => pure start
      | some offset => countOfLinear g (cellAt m.cells (fp + offset)).word 7
    let base ← bitsBaseLinear m.cells fp g dst
    let m ← putValuesLinear m base
      ((Array.range ndigits).map fun i => Spec.Xmss.count ((integer >>> (start + digitBits * i)) % 2 ^ digitBits))
    return ⟨⟨m, pc, fp, nextFree, g, cycles, counts⟩, streams⟩
  | .windowsExp value dest offset start width count =>
    if start + width * count > 192 then throw .badProgram
    let base ← bitsBaseLinear m.cells fp g dest
    let integer := limbsInteger (cellAt m.cells (fp + value)).word
    let m ← putValuesLinear m (base + offset)
      ((Array.range count).map fun i => Spec.Xmss.count ((integer >>> (start + width * i)) % 2 ^ width))
    return ⟨⟨m, pc, fp, nextFree, g, cycles, counts⟩, streams⟩
  | .fieldLimbs value base len =>
    if len < 1 || len > 3 then throw .badProgram
    let v := (cellAt m.cells (fp + value)).word
    let m ← putValuesLinear m (fp + base)
      ((#[v.c0, v.c1, v.c2].extract 0 len).map Spec.Field.embed)
    return ⟨⟨m, pc, fp, nextFree, g, cycles, counts⟩, streams⟩
  | .inverse value dst =>
    let v := (cellAt m.cells (fp + value)).word
    let m ← putValuesLinear m (fp + dst) #[inverseLinear v]
    return ⟨⟨m, pc, fp, nextFree, g, cycles, counts⟩, streams⟩
  | .print .. =>
    return ⟨⟨m, pc, fp, nextFree, g, cycles, counts⟩, streams⟩

def applyHintsLinear (hints : @& Array RHint) (r : Runtime) : Except Fault Runtime :=
  hints.foldlM (fun r hint => applyHintLinear hint r) r

def stepBodyLinear (op : @& Op) (m : Memory) (oldPc oldFp : Nat) (opcodeCounts : Array Nat)
    (g : @& GPow) : Except Fault (Memory × Nat × Nat × Array Nat) := do
  let mut m := m
  let mut pc := oldPc + 1
  let mut fp := oldFp
  let mut addresses := #[]
  match op with
  | .set offset value =>
    m ← putLinear m (fp + offset) value
    addresses := #[fp + offset]
  | .xor a b c | .mul a b c =>
    let isMul := match op with | .mul .. => true | _ => false
    let aa := fp + a
    let ab := fp + b
    let ac := fp + c
    if isMul && (cellAt m.cells ac).written then
      let ha := (cellAt m.cells aa).written
      let hb := (cellAt m.cells ab).written
      if ha != hb then
        let known := (cellAt m.cells (if ha then aa else ab)).word
        if wordBEq known Spec.Field.zero then throw .backSolveThroughZero
        let prod := Model.Field.nativeKaratsuba (cellAt m.cells ac).word (inverseLinear known)
        m ← putLinear m (if ha then ab else aa) prod
    let (va, next) ← readLinear m aa
    m := next
    let (vb, next) ← readLinear m ab
    m := next
    m ← putLinear m ac (if isMul then Model.Field.nativeKaratsuba va vb else
      ⟨Model.Vm.xorKernel va.c0 vb.c0, Model.Vm.xorKernel va.c1 vb.c1,
        Model.Vm.xorKernel va.c2 vb.c2⟩)
    addresses := #[aa, ab, ac]
  | .deref o1 o2 o3 mode =>
    let a1 := fp + o1
    let (p, next) ← readLinear m a1
    m := next
    let base ← logLinear g p
    let a2 := base + o2
    let a3 := fp + o3
    match mode with
    | .cell =>
      if (cellAt m.cells a2).written then
        let w := (cellAt m.cells a2).word
        m ← putLinear m a3 w
      else if (cellAt m.cells a3).written then
        let w := (cellAt m.cells a3).word
        m ← putLinear m a2 w
      else m ← linkLinear m a2 a3
    | .pc => m ← putLinear m a2 (← powerLinear g (oldPc + 2))
    | .fp => m ← putLinear m a2 (← powerLinear g fp)
    addresses := #[a1, a2, a3]
  | .jump oc od of =>
    let (c, next) ← readLinear m (fp + oc)
    m := next
    let (d, next) ← readLinear m (fp + od)
    m := next
    let (f, next) ← readLinear m (fp + of)
    m := next
    for value in #[c, d, f] do
      if value.c1.toNat != 0 || value.c2.toNat != 0 then throw (.notInK value)
    addresses := #[fp + oc, fp + od, fp + of]
    if c.c0.toNat != 0 then
      pc ← logLinear g d
      fp ← logLinear g f
  | .keccak message tail b8 cap output inOdd outOdd =>
    if message.size != 4 then throw .badProgram
    let inputs := (message ++ (Array.range 4).map (tail + ·) |>.push b8) ++ (Array.range 4).map (cap + ·)
    let mut cells := #[]
    for address in inputs do
      let (value, next) ← readLinear m (fp + address)
      m := next
      if value.c2.toNat != 0 then throw (.notCanonical value)
      cells := cells.push value
    let result := KeccakInternal.cellsOfState outOdd
      (KeccakInternal.permute (KeccakInternal.stateOfCells inOdd cells))
    for i in [:13] do
      m ← putLinear m (fp + output + i) (result[i]?.getD Spec.Field.zero)
    addresses := inputs.map (fp + ·) ++ (Array.range 13).map (fun i => fp + output + i)
  for address in addresses do m ← bumpLinear m address
  let counts := opcodeCounts.modify (opcode op) (· + 1)
  return (m, pc, fp, counts)

def stepLinear (op : @& Op) (s : State) : Except Fault State := do
  let ⟨m, oldPc, oldFp, nextFree, g, cycles, opcodeCounts⟩ := s
  let g := growLinear g (max (oldPc + 2) oldFp)
  let (memory, pc, fp, counts) ← stepBodyLinear op m oldPc oldFp opcodeCounts g
  return ⟨memory, pc, fp, nextFree, g, cycles + 1, counts⟩

def scheduledRunLinear (fuel : Nat) (program : @& Array Op) (hints : @& Array (Array RHint))
    (r : Runtime) : Except Fault Runtime :=
  Nat.rec (motive := fun _ => Runtime → Except Fault Runtime)
    (fun _ => .error .stepLimit)
    (fun _ rec cur =>
      if cur.state.pc + 1 == program.size && cur.state.fp == 0 then .ok cur
      else match program[cur.state.pc]? with
        | none => .error .badProgram
        | some op =>
          let hs := hints[cur.state.pc]?.getD #[]
          match applyHintsLinear hs cur with
          | .error fault => .error fault
          | .ok ⟨ready, streams⟩ =>
            match stepLinear op ready with
            | .error fault => .error fault
            | .ok state => rec ⟨state, streams⟩)
    fuel r

end LeanVmXmss.Model.Vm
