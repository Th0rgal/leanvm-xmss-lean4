import Spec.Layout.Basic
import Model.Field.Scalar
import Model.Keccak.Registers
import Model.Vm.Kernel
import Model.Pcs.Ntt

namespace LeanVmXmss.Model.Layout

open Spec.Field (K E)
open Spec.Layout

def log2Strict? (n : Nat) : Option Nat :=
  if n != 0 && n &&& (n - 1) == 0 then some (Nat.log2 n) else none

def gpowStep (ac : Array K × K) (_ : Nat) : Array K × K :=
  let (acc, cur) := ac
  let next := Model.Vm.scalarGeneratorStep cur
  (acc.push next, next)

def gpowTable (limit : Nat) : Array K :=
  (Model.Pcs.Ntt.foldRange limit gpowStep
    ((Array.emptyWithCapacity (limit + 1)).push 1, (1 : K))).1

def maxOpOffset (op : Spec.Vm.Op) : Nat :=
  match op with
  | .xor a b c | .mul a b c | .jump a b c => max a (max b c)
  | .set o _ => o
  | .deref o1 o2 o3 _ => max o1 (max o2 o3)
  | .keccak m tail b8 cap out _ _ =>
    let mm := m.foldl max 0
    max mm (max tail (max b8 (max cap out)))

def maxProgramOffset (prog : Array Spec.Vm.Op) : Nat :=
  prog.foldl (fun acc op => max acc (maxOpOffset op)) 5

def gAt (gpows : Array K) (n : Nat) : K :=
  match gpows[n]? with
  | some v => v
  | none => Spec.Xmss.gpow n

def bytecodeRowFast (gpows : Array K) (op : Spec.Vm.Op) : Array K :=
  let flag (b : Bool) : K := if b then 1 else 0
  match op with
  | .xor a b c =>
    #[gAt gpows opXor, gAt gpows a, gAt gpows b, gAt gpows c, 0, 0, 0, 0, 0, 0, 0]
  | .mul a b c =>
    #[gAt gpows opMul, gAt gpows a, gAt gpows b, gAt gpows c, 0, 0, 0, 0, 0, 0, 0]
  | .set o k =>
    #[gAt gpows opSet, gAt gpows o, k.c0, k.c1, k.c2, 0, 0, 0, 0, 0, 0]
  | .deref o1 o2 o3 mode =>
    #[gAt gpows opDeref, gAt gpows o1, gAt gpows o2, gAt gpows o3,
      derefFlagPc mode, derefFlagFp mode, 0, 0, 0, 0, 0]
  | .jump oc od of =>
    #[gAt gpows opJump, gAt gpows oc, gAt gpows od, gAt gpows of, 0, 0, 0, 0, 0, 0, 0]
  | .keccak m tail b8 cap out inOdd outOdd =>
    #[gAt gpows opKeccak, gAt gpows (m[0]?.getD 0), gAt gpows (m[1]?.getD 0),
      gAt gpows (m[2]?.getD 0), gAt gpows (m[3]?.getD 0),
      gAt gpows tail, gAt gpows b8, gAt gpows cap, gAt gpows out, flag inOdd, flag outOdd]

def bytecodeColumnsFast (prog : Array Spec.Vm.Op) : Array (Array K) :=
  let gpows := gpowTable (maxProgramOffset prog)
  (Array.range nBytecodeCols).map fun s =>
    prog.map fun op => (bytecodeRowFast gpows op)[s]?.getD 0

def pushWordLE (bytes : ByteArray) (w : UInt64) : ByteArray :=
  bytes.push w.toUInt8
    |>.push (w >>> 8).toUInt8
    |>.push (w >>> 16).toUInt8
    |>.push (w >>> 24).toUInt8
    |>.push (w >>> 32).toUInt8
    |>.push (w >>> 40).toUInt8
    |>.push (w >>> 48).toUInt8
    |>.push (w >>> 56).toUInt8

def wordsBytesFast (ws : Array UInt64) : ByteArray :=
  ws.foldl pushWordLE (ByteArray.emptyWithCapacity (ws.size * 8))

def readWordLE (b : ByteArray) (offset : Nat) : UInt64 :=
  (b[offset]?.getD 0).toUInt64 |||
    ((b[offset + 1]?.getD 0).toUInt64 <<< 8) |||
    ((b[offset + 2]?.getD 0).toUInt64 <<< 16) |||
    ((b[offset + 3]?.getD 0).toUInt64 <<< 24) |||
    ((b[offset + 4]?.getD 0).toUInt64 <<< 32) |||
    ((b[offset + 5]?.getD 0).toUInt64 <<< 40) |||
    ((b[offset + 6]?.getD 0).toUInt64 <<< 48) |||
    ((b[offset + 7]?.getD 0).toUInt64 <<< 56)

def absorb25 (s : Model.Keccak.State25) (b : ByteArray) (base : Nat) : Model.Keccak.State25 :=
  Model.Keccak.keccakF1600
    { s with
      a00 := s.a00 ^^^ readWordLE b base
      a01 := s.a01 ^^^ readWordLE b (base + 8)
      a02 := s.a02 ^^^ readWordLE b (base + 16)
      a03 := s.a03 ^^^ readWordLE b (base + 24)
      a04 := s.a04 ^^^ readWordLE b (base + 32)
      a05 := s.a05 ^^^ readWordLE b (base + 40)
      a06 := s.a06 ^^^ readWordLE b (base + 48)
      a07 := s.a07 ^^^ readWordLE b (base + 56)
      a08 := s.a08 ^^^ readWordLE b (base + 64)
      a09 := s.a09 ^^^ readWordLE b (base + 72)
      a10 := s.a10 ^^^ readWordLE b (base + 80)
      a11 := s.a11 ^^^ readWordLE b (base + 88)
      a12 := s.a12 ^^^ readWordLE b (base + 96)
      a13 := s.a13 ^^^ readWordLE b (base + 104)
      a14 := s.a14 ^^^ readWordLE b (base + 112)
      a15 := s.a15 ^^^ readWordLE b (base + 120)
      a16 := s.a16 ^^^ readWordLE b (base + 128) }

def zeroState25 : Model.Keccak.State25 :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

def absorb25Block (s : Model.Keccak.State25) (blk : ByteArray) : Model.Keccak.State25 :=
  absorb25 s blk 0

def keccak256Stream (b : ByteArray) : ByteArray :=
  let nFull := b.size / 136
  let st := (Array.range nFull).foldl (fun s i => absorb25 s b (136 * i)) zeroState25
  let tail := b.extract (136 * nFull) b.size
  let stFinal := absorb25Block st (Spec.Keccak.finalBlock tail 1)
  Spec.Keccak.wordsBytes #[stFinal.a00, stFinal.a01, stFinal.a02, stFinal.a03]

def stackBytecodeColumnsFast (logBytecode : Nat) (cols : Array (Array K)) : Array K :=
  let stride := 1 <<< logBytecode
  let indices := Array.range stride
  (Array.range nBytecodeCols).foldl
    (fun table s =>
      let col := cols[s]?.getD #[]
      let base := (bytecodePublicSlot + s) * stride
      indices.foldl
        (fun tbl i => tbl.set! (base + i) (col[i]?.getD 0))
        table)
    (Array.replicate (1 <<< (busBits + logBytecode)) (0 : K))

def keccak256Fast (b : ByteArray) : ByteArray :=
  let st := (Spec.Keccak.blocks b 1).foldl absorb25Block zeroState25
  Spec.Keccak.wordsBytes #[st.a00, st.a01, st.a02, st.a03]

def fiatShamirIvFast (table : Array K) : ByteArray :=
  keccak256Stream (versionTag ++ wordsBytesFast table)

def kappaOf (logMem logBytecode : Nat) (taus : Fin nTables → Nat) (col : Nat) : Option Nat :=
  Spec.Layout.kappaOf logMem logBytecode taus col

def placementsOf (logMem logBytecode : Nat) (taus : Fin nTables → Nat) :
    Array (Option Placement) × Shape × Nat :=
  Spec.Layout.placementsOf logMem logBytecode taus

structure PublicLayout where
  logMem : Nat
  logBytecode : Nat
  rows : Array Nat
  taus : Array Nat
  placements : Array (Option Placement)
  shape : Shape
  placed : Nat
  push : Array Block
  pull : Array Block
  count : Array Block
  pushLayout : BusLayout
  pullLayout : BusLayout
  countLayout : BusLayout
  deriving DecidableEq, Repr

def validateSizes (logMem logBytecode logInvRate : Nat) (rows : Array Nat) : Bool :=
  rows.size == nTables &&
    minLogMem ≤ logMem && logMem ≤ maxLogMem &&
    logBytecode ≤ maxTableLog &&
    minLogInvRate ≤ logInvRate && logInvRate ≤ maxLogInvRate &&
    rows.toList.all (fun r => r ≤ (1 <<< maxTableLog))

def buildPublicLayout (logMem logBytecode : Nat) (rowArr : Array Nat) : PublicLayout :=
  let rows (t : Fin nTables) : Nat := rowArr[t.val]?.getD 0
  let taus := tableLog rows
  let (placements, shape, placed) := placementsOf logMem logBytecode taus
  let (push, pull, count) := busBlocks logMem logBytecode rows taus
  let tausArr : Array Nat :=
    #[taus ⟨0, by decide⟩, taus ⟨1, by decide⟩, taus ⟨2, by decide⟩,
      taus ⟨3, by decide⟩, taus ⟨4, by decide⟩, taus ⟨5, by decide⟩]
  let rowsNorm : Array Nat :=
    #[rows ⟨0, by decide⟩, rows ⟨1, by decide⟩, rows ⟨2, by decide⟩,
      rows ⟨3, by decide⟩, rows ⟨4, by decide⟩, rows ⟨5, by decide⟩]
  { logMem
    logBytecode
    rows := rowsNorm
    taus := tausArr
    placements
    shape
    placed
    push
    pull
    count
    pushLayout := busSideLayout push
    pullLayout := busSideLayout pull
    countLayout := busSideLayout count }

def publicLayout (logMem logBytecode : Nat) (rows : Fin nTables → Nat) :
    Array (Option Placement) × Shape × Nat × (Fin nTables → Nat) :=
  let taus := tableLog rows
  let (placements, shape, placed) := placementsOf logMem logBytecode taus
  (placements, shape, placed, taus)

end LeanVmXmss.Model.Layout
