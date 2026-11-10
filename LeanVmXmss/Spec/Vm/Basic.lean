import Spec.Xmss.Hints
import Spec.Vm.Equality
import Model.Vm.Kernel

namespace LeanVmXmss.Spec.Vm

open Spec.Field (E)

def maxCells : Nat := 1 <<< 28

inductive DerefMode where
  | cell | pc | fp
  deriving DecidableEq, Repr

inductive Op where
  | xor (a b c : Nat)
  | mul (a b c : Nat)
  | set (offset : Nat) (value : E)
  | deref (o1 o2 o3 : Nat) (mode : DerefMode)
  | jump (condition target frame : Nat)
  | keccak (message : Array Nat) (tail b8 cap output : Nat) (inOdd outOdd : Bool)
  deriving DecidableEq, Repr

structure Cell where
  word : E := Spec.Field.zero
  written : Bool := false
  accesses : Nat := 0
  deriving DecidableEq, Repr, Inhabited

structure Memory where
  cells : Array Cell := #[]
  links : Array (Nat × Nat) := #[]
  unconstrainedReads : Array Nat := #[]
  used : Nat := 0
  deriving DecidableEq, Repr, Inhabited

inductive Fault where
  | conflict (address : Nat) (had value : E)
  | outOfMemory
  | wildPointer (value : E)
  | notInK (value : E)
  | notCanonical (value : E)
  | backSolveThroughZero
  | badProgram
  | witness (name : String)
  | stepLimit
  deriving DecidableEq, Repr

def Memory.get (m : Memory) (address : Nat) : Cell := m.cells[address]?.getD {}

def Memory.ensure (m : Memory) (address : Nat) : Except Fault Memory :=
  if address >= maxCells then .error .outOfMemory
  else if address < m.cells.size then .ok {m with used := max m.used (address+1)}
  else
    let target := max (address+1) (max 65536 (2*m.cells.size))
    .ok {m with cells := m.cells ++ Array.replicate (target-m.cells.size) {}, used := max m.used (address+1)}

def Memory.store (m : Memory) (address : Nat) (value : E) : Except Fault Memory :=
  match m.ensure address with
  | .error fault => .error fault
  | .ok m =>
    let old := m.get address
    if old.written = true ∧ old.word ≠ value then .error (.conflict address old.word value)
    else .ok {m with cells := m.cells.set! address {old with word := value, written := true}}

def spread (fuel : Nat) (todo : List Nat) (initial : Memory) (value : E) : Except Fault Memory := do
  let mut m := initial
  let mut pending := todo
  for _ in [:fuel] do
    match pending with
    | [] => return m
    | a::rest =>
      pending := rest
      let neighbors := m.links.toList.filterMap fun (x,y) => if x == a then some y else none
      m := {m with links := m.links.filter fun (x,_) => x != a}
      for b in neighbors do
        if !(m.get b).written then pending := b::pending
        m ← m.store b value
  if pending.isEmpty then return m else throw .badProgram

def Memory.put (m : Memory) (address : Nat) (value : E) : Except Fault Memory := do
  let fuel := m.links.size+1
  let next ← m.store address value
  spread fuel [address] next value

def Memory.read (m : Memory) (address : Nat) : Except Fault (E × Memory) := do
  let m ← m.ensure address
  let old := m.get address
  let m := if old.written then m else
    {m with
      cells := m.cells.set! address {old with written := true}
      unconstrainedReads := m.unconstrainedReads.push address}
  return (old.word, m)

def Memory.bump (m : Memory) (address : Nat) : Except Fault Memory := do
  let m ← m.ensure address
  let old := m.get address
  return {m with cells := m.cells.set! address {old with accesses := old.accesses+1}}

def Memory.link (m : Memory) (a b : Nat) : Except Fault Memory := do
  let m ← m.ensure a
  let m ← m.ensure b
  return {m with links := m.links.push (a,b) |>.push (b,a)}

def epow (a : E) : Nat → E :=
  Nat.rec Spec.Field.one (fun _ previous => Model.Field.karatsubaMul previous a)

def inverse (a : E) : E := Id.run do
  let mut x := Spec.Field.one
  for i in [:192] do
    x := Model.Field.karatsubaMul x x
    if i < 191 then x := Model.Field.karatsubaMul x a
  return x

structure GPow where
  powers : Array UInt64 := #[1]
  coarse : Array (List (Nat × Nat)) := (Array.replicate 65536 []).set! 1 [(1,0)]
  deriving Inhabited

def GPow.power (g : GPow) (n : Nat) : Except Fault E :=
  match g.powers[n]? with
  | some value => .ok ⟨value,0,0⟩
  | none => .error .badProgram

def GPow.extend (g : GPow) : GPow :=
  let x := g.powers.back?.getD 1
  let value := (x <<< 1) ^^^ (if x.toNat / 2^63 == 0 then 0 else 0x1b)
  let index := g.powers.size
  let coarse := if index % 64 == 0 then
    g.coarse.modify (value.toNat % 65536) (fun xs => (value.toNat,index)::xs)
    else g.coarse
  ⟨g.powers.push value, coarse⟩

def GPow.extendMany : Nat → GPow → GPow :=
  Nat.rec (motive := fun _ => GPow → GPow) (fun g => g)
    (fun _ previous g => previous g.extend)

def GPow.grow (g : GPow) (n : Nat) : GPow :=
  GPow.extendMany (n+1-g.powers.size) g

def GPow.log (g : GPow) (value : E) : Except Fault Nat := do
  if value.c1.toNat != 0 || value.c2.toNat != 0 then throw (.notInK value)
  let mut y := value.c0
  for j in [:64] do
    if let some (_, index) := (g.coarse[y.toNat % 65536]?.getD []).find? (fun pair => pair.1 == y.toNat) then
      if index+j < g.powers.size then return index+j
    y := if y.toNat % 2 == 1 then ((y ^^^ 0x1b) >>> 1) ||| ((1 : UInt64) <<< 63) else y >>> 1
  throw (.wildPointer value)

structure State where
  memory : Memory := {}
  pc : Nat := 0
  fp : Nat := 0
  nextFree : Nat := 2
  g : GPow := {}
  cycles : Nat := 0
  opcodeCounts : Array Nat := Array.replicate 6 0
  deriving Inhabited

def opcode : Op → Nat
  | .xor .. => 0
  | .mul .. => 1
  | .set .. => 2
  | .deref .. => 3
  | .jump .. => 4
  | .keccak .. => 5

def stepBody (op : Op) (s : State) (g : GPow) : Except Fault (Memory × Nat × Nat × Array Nat) := do
  let ⟨memory, oldPc, oldFp, _, _, _, opcodeCounts⟩ := s
  let mut m := memory
  let mut pc := oldPc+1
  let mut fp := oldFp
  let mut addresses := #[]
  match op with
  | .set offset value =>
    m ← m.put (fp+offset) value
    addresses := #[fp+offset]
  | .xor a b c | .mul a b c =>
    let isMul := match op with | .mul .. => true | _ => false
    let aa := fp+a
    let ab := fp+b
    let ac := fp+c
    if isMul && (m.get ac).written then
      let ha := (m.get aa).written
      let hb := (m.get ab).written
      if ha != hb then
        let known := (m.get (if ha then aa else ab)).word
        if wordBEq known Spec.Field.zero then throw .backSolveThroughZero
        m ← m.put (if ha then ab else aa) (Model.Field.karatsubaMul (m.get ac).word (inverse known))
    let (va, next) ← m.read aa
    m := next
    let (vb, next) ← m.read ab
    m := next
    m ← m.put ac (if isMul then Model.Field.karatsubaMul va vb else
      ⟨Model.Vm.xorKernel va.c0 vb.c0, Model.Vm.xorKernel va.c1 vb.c1,
        Model.Vm.xorKernel va.c2 vb.c2⟩)
    addresses := #[aa,ab,ac]
  | .deref o1 o2 o3 mode =>
    let a1 := fp+o1
    let (p, next) ← m.read a1
    m := next
    let base ← g.log p
    let a2 := base+o2
    let a3 := fp+o3
    match mode with
    | .cell =>
      if (m.get a2).written then m ← m.put a3 (m.get a2).word
      else if (m.get a3).written then m ← m.put a2 (m.get a3).word
      else m ← m.link a2 a3
    | .pc => m ← m.put a2 (← g.power (oldPc+2))
    | .fp => m ← m.put a2 (← g.power fp)
    addresses := #[a1,a2,a3]
  | .jump oc od of =>
    let (c, next) ← m.read (fp+oc)
    m := next
    let (d, next) ← m.read (fp+od)
    m := next
    let (f, next) ← m.read (fp+of)
    m := next
    for value in #[c,d,f] do
      if value.c1.toNat != 0 || value.c2.toNat != 0 then throw (.notInK value)
    addresses := #[fp+oc,fp+od,fp+of]
    if c.c0.toNat != 0 then
      pc ← g.log d
      fp ← g.log f
  | .keccak message tail b8 cap output inOdd outOdd =>
    if message.size != 4 then throw .badProgram
    let inputs := (message ++ (Array.range 4).map (tail+·) |>.push b8) ++ (Array.range 4).map (cap+·)
    let mut cells := #[]
    for address in inputs do
      let (value, next) ← m.read (fp+address)
      m := next
      if value.c2.toNat != 0 then throw (.notCanonical value)
      cells := cells.push value
    let result := KeccakInternal.cellsOfState outOdd (KeccakInternal.permute (KeccakInternal.stateOfCells inOdd cells))
    for i in [:13] do
      m ← m.put (fp+output+i) (result[i]?.getD Spec.Field.zero)
    addresses := inputs.map (fp+·) ++ (Array.range 13).map (fun i => fp+output+i)
  for address in addresses do m ← m.bump address
  let counts := opcodeCounts.modify (opcode op) (·+1)
  return (m, pc, fp, counts)

def stepWithPowers (op : Op) (s : State) (g : GPow) : Except Fault State := do
  let (memory, pc, fp, counts) ← stepBody op s g
  return ⟨memory, pc, fp, s.nextFree, g, s.cycles+1, counts⟩

def step (op : Op) (s : State) : Except Fault State :=
  stepWithPowers op s (s.g.grow (max (s.pc+2) s.fp))

end LeanVmXmss.Spec.Vm
