import Spec.Vm.Basic

namespace LeanVmXmss.Spec.Vm

open Spec.Field (E)

inductive BitsDest where
  | stack (base : Nat)
  | heap (ptr : Nat)
  deriving DecidableEq, Repr

inductive RHint where
  | frameAddress (offset : Nat)
  | allocFrames (ptr size endOffset : Nat) (startInverse : UInt64) (tail : Nat)
  | alloc (ptr size : Nat)
  | allocDyn (ptr size : Nat)
  | witnessStack (name : String) (base len : Nat)
  | witnessHeap (name : String) (ptr lo len : Nat)
  | log2Ceil (bits : BitsDest) (dst nbits floor : Nat)
  | bitDecompose (value : Nat) (bits : BitsDest) (nbits start : Nat)
  | bitDecomposeExp (value : Nat) (bits : BitsDest) (nbits : Nat)
  | digitDecomposeExp (value : Nat) (dst : BitsDest) (nbits ndigits digitBits start : Nat) (startCell : Option Nat)
  | windowsExp (value : Nat) (dest : BitsDest) (offset start width count : Nat)
  | fieldLimbs (value base len : Nat)
  | inverse (value dst : Nat)
  | print (label : String) (cell : Nat)
  deriving Repr

structure Stream where
  name : String
  entries : Array (Array E)
  next : Nat := 0

structure Runtime where
  state : State
  streams : Array Stream := #[]

def heapBase (s : State) (ptr : Nat) : Except Fault Nat := s.g.log (s.memory.get (s.fp+ptr)).word

def bitsBase (s : State) : BitsDest → Except Fault Nat
  | .stack base => .ok (s.fp+base)
  | .heap ptr => heapBase s ptr

def inK (value : E) : Except Fault UInt64 :=
  if value.c1.toNat == 0 && value.c2.toNat == 0 then .ok value.c0 else .error (.notInK value)

def countOf (s : State) (value : E) (nbits : Nat) : Except Fault Nat := do
  let index ← s.g.log value
  if index < 2^nbits then return index else throw (.wildPointer value)

def limbsInteger (value : E) : Nat := value.c0.toNat + (value.c1.toNat <<< 64) + (value.c2.toNat <<< 128)

def putValues (s : State) (base : Nat) (values : Array E) : Except Fault State := do
  let mut m := s.memory
  for i in [:values.size] do m ← m.put (base+i) (values[i]?.getD Spec.Field.zero)
  return {s with memory := m}

def reserve (s : State) (ptr size : Nat) : Except Fault State := do
  if (s.memory.get (s.fp+ptr)).written then return s
  let endOffset := s.nextFree+size
  if endOffset >= maxCells then throw .outOfMemory
  let g := s.g.grow endOffset
  let m ← s.memory.ensure endOffset
  let m ← m.put (s.fp+ptr) (← g.power s.nextFree)
  return {s with memory := m, g, nextFree := endOffset}

def popWitness (r : Runtime) (name : String) (base len : Nat) : Except Fault Runtime := do
  let some index := r.streams.findIdx? (fun stream => stream.name == name) | throw (.witness name)
  let some stream := r.streams[index]? | throw (.witness name)
  let some values := stream.entries[stream.next]? | throw (.witness name)
  if values.size != len then throw (.witness name)
  let state ← putValues r.state base values
  return {state, streams := r.streams.set! index {stream with next := stream.next+1}}

def applyHint (h : RHint) (r : Runtime) : Except Fault Runtime := do
  let s := r.state
  let valueAt := fun offset => (s.memory.get (s.fp+offset)).word
  let mut next := s
  match h with
  | .frameAddress offset => next := {s with g := s.g.grow (s.fp+offset)}
  | .alloc ptr size => next ← reserve s ptr size
  | .allocDyn ptr size => next ← reserve s ptr (← countOf s (valueAt size) 28)
  | .allocFrames ptr size endOffset startInverse tail =>
    let span ← inK (valueAt endOffset)
    let count ← countOf s ⟨Model.Field.mul span startInverse,0,0⟩ 28
    next ← reserve s ptr (size*count+tail)
  | .witnessStack name base len => return ← popWitness r name (s.fp+base) len
  | .witnessHeap name ptr lo len => return ← popWitness r name ((← heapBase s ptr)+lo) len
  | .log2Ceil bits dst nbits floor =>
    let base ← bitsBase s bits
    let mut value := 0
    for i in [:nbits] do
      if !wordBEq (s.memory.get (base+i)).word Spec.Field.zero then value := value ||| (1 <<< i)
    let log := if value <= 1 then 0 else (value-1).log2+1
    next ← putValues s (s.fp+dst) #[Xmss.count (max log floor)]
  | .bitDecompose value bits nbits start =>
    if start+nbits > 192 then throw .badProgram
    let base ← bitsBase s bits
    let integer := limbsInteger (valueAt value)
    next ← putValues s base ((Array.range nbits).map fun i => Spec.Field.embed (if integer.testBit (start+i) then 1 else 0))
  | .bitDecomposeExp value bits nbits =>
    let integer ← countOf s (valueAt value) nbits
    let base ← bitsBase s bits
    next ← putValues s base ((Array.range nbits).map fun i => Spec.Field.embed (if integer.testBit i then 1 else 0))
  | .digitDecomposeExp value dst nbits ndigits digitBits start startCell =>
    let integer ← countOf s (valueAt value) nbits
    let start ← match startCell with
      | none => pure start
      | some offset => countOf s (valueAt offset) 7
    let base ← bitsBase s dst
    next ← putValues s base ((Array.range ndigits).map fun i => Xmss.count ((integer >>> (start+digitBits*i)) % 2^digitBits))
  | .windowsExp value dest offset start width count =>
    if start+width*count > 192 then throw .badProgram
    let base ← bitsBase s dest
    let integer := limbsInteger (valueAt value)
    next ← putValues s (base+offset) ((Array.range count).map fun i => Xmss.count ((integer >>> (start+width*i)) % 2^width))
  | .fieldLimbs value base len =>
    if len < 1 || len > 3 then throw .badProgram
    let v := valueAt value
    next ← putValues s (s.fp+base) ((#[v.c0,v.c1,v.c2].extract 0 len).map Spec.Field.embed)
  | .inverse value dst => next ← putValues s (s.fp+dst) #[inverse (valueAt value)]
  | .print .. => pure ()
  return {r with state := next}

def applyHints (hints : Array RHint) (r : Runtime) : Except Fault Runtime :=
  hints.foldlM (fun r hint => applyHint hint r) r

end LeanVmXmss.Spec.Vm
