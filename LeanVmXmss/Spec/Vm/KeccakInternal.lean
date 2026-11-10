import Spec.Field.Basic
import Model.Vm.Kernel

namespace LeanVmXmss.Spec.Vm.KeccakInternal

def rotations : Array Nat := #[0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]

def constants : Array UInt64 := #[0x0000000000000001, 0x0000000000008082,
  0x800000000000808a, 0x8000000080008000, 0x000000000000808b, 0x0000000080000001,
  0x8000000080008081, 0x8000000000008009, 0x000000000000008a, 0x0000000000000088,
  0x0000000080008009, 0x000000008000000a, 0x000000008000808b, 0x800000000000008b,
  0x8000000000008089, 0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
  0x000000000000800a, 0x800000008000000a, 0x8000000080008081, 0x8000000000008080,
  0x0000000080000001, 0x8000000080008008]

def rot (x : UInt64) (n : Nat) : UInt64 :=
  if n == 0 then x else Model.Vm.rotateLeftKernel x n.toUInt64 |||
    Model.Vm.rotateRightKernel x (64 - n).toUInt64

def round (s : Array UInt64) (rc : UInt64) : Array UInt64 := Id.run do
  let mut c := Array.replicate 5 (0 : UInt64)
  for x in [:5] do
    c := c.set! x (s[x]! ^^^ s[x+5]! ^^^ s[x+10]! ^^^ s[x+15]! ^^^ s[x+20]!)
  let mut b := Array.replicate 25 (0 : UInt64)
  for y in [:5] do
    for x in [:5] do
      let d := Model.Vm.thetaKernel c[(x+4)%5]! c[(x+1)%5]!
      b := b.set! (y + 5*((2*x+3*y)%5)) (rot (s[x+5*y]! ^^^ d) rotations[x+5*y]!)
  let mut out := Array.replicate 25 (0 : UInt64)
  for y in [:5] do
    for x in [:5] do
      out := out.set! (x+5*y) (Model.Vm.chiKernel b[x+5*y]! b[(x+1)%5+5*y]! b[(x+2)%5+5*y]!)
  return out.set! 0 (out[0]! ^^^ rc)

def permute (s : Array UInt64) : Array UInt64 := constants.foldl round s

def hash (bytes : ByteArray) : ByteArray := Id.run do
  let padding := 136 - bytes.size % 136
  let mut input := bytes
  for i in [:padding] do
    input := input.push ((if i == 0 then 1 else 0) ||| (if i+1 == padding then 128 else 0))
  let mut s := Array.replicate 25 (0 : UInt64)
  for block in [:input.size / 136] do
    for i in [:136] do
      let offset := block*136+i
      let lane := i/8
      s := s.set! lane (s[lane]! ^^^ (input[offset]!.toUInt64 <<< ((i%8)*8).toUInt64))
    s := permute s
  let mut out := ByteArray.empty
  for i in [:32] do
    out := out.push ((s[i/8]! >>> ((i%8)*8).toUInt64).toUInt8)
  return out

def cellLanes (odd : Bool) (c : Nat) : Option Nat × Option Nat :=
  if c >= 9 || (odd && c >= 1) then (some (2*c-1), some (2*c))
  else if odd then (none, some 0)
  else if c == 8 then (some 16, none)
  else (some (2*c), some (2*c+1))

def stateOfCells (odd : Bool) (cells : Array Spec.Field.E) : Array UInt64 := Id.run do
  let mut s := Array.replicate 25 (0 : UInt64)
  for c in [:13] do
    let (lo, hi) := cellLanes odd c
    if let some i := lo then s := s.set! i (cells[c]?.getD Spec.Field.zero).c0
    if let some i := hi then s := s.set! i (cells[c]?.getD Spec.Field.zero).c1
  return s

def cellsOfState (odd : Bool) (s : Array UInt64) : Array Spec.Field.E :=
  (Array.range 13).map fun c =>
    let (lo, hi) := cellLanes odd c
    ⟨lo.map (s[·]!) |>.getD 0, hi.map (s[·]!) |>.getD 0, 0⟩

end LeanVmXmss.Spec.Vm.KeccakInternal
