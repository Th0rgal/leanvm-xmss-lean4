import Spec.Field.Basic
import Spec.Keccak.Basic
import Spec.Vm.Basic

namespace LeanVmXmss.Spec.Layout

open Spec.Field (K E)

def versionTag : ByteArray := "leanvm-v1".toUTF8
def nTables : Nat := 6
def nGlobal : Nat := 6
def busBits : Nat := 4
def bytecodePublicSlot : Nat := 3
def stateLanes : Nat := 25
def keccakRounds : Nat := 24
def keccakDepth : Nat := 12
def keccakCells : Nat := 13
def keccakMinStepsLog : Nat := 9
def minLogMem : Nat := 16
def maxLogMem : Nat := 32
def maxTableLog : Nat := 32
def minStackedLog : Nat := 15
def maxStackedLog : Nat := 28
def logBatch : Nat := 6
def minLogInvRate : Nat := 1
def maxLogInvRate : Nat := 4
def bytecodeOperands : Nat := 10
def nBytecodeCols : Nat := 1 + bytecodeOperands

def memLo : Nat := 0
def memHi : Nat := 1
def memTop : Nat := 2
def memFinal : Nat := 3
def bytecodeFinal : Nat := 4
def qKeccak : Nat := 5

def opXor : Nat := 0
def opMul : Nat := 1
def opSet : Nat := 2
def opDeref : Nat := 3
def opJump : Nat := 4
def opKeccak : Nat := 5

def arithWidth : Nat := 15
def setWidth : Nat := 8
def derefWidth : Nat := 15
def jumpWidth : Nat := 14

def keccakHead : Nat := 13
def keccakIn : Nat := keccakHead
def keccakOut : Nat := keccakIn + stateLanes
def keccakCnt : Nat := keccakOut + stateLanes
def keccakCntBc : Nat := keccakCnt + 2 * keccakCells
def keccakWidth : Nat := keccakCntBc + 1

def tableWidth : Fin nTables → Nat
  | ⟨0, _⟩ => arithWidth
  | ⟨1, _⟩ => arithWidth
  | ⟨2, _⟩ => setWidth
  | ⟨3, _⟩ => derefWidth
  | ⟨4, _⟩ => jumpWidth
  | ⟨5, _⟩ => keccakWidth

def tableBase : Fin nTables → Nat
  | ⟨0, _⟩ => nGlobal
  | ⟨1, _⟩ => nGlobal + arithWidth
  | ⟨2, _⟩ => nGlobal + 2 * arithWidth
  | ⟨3, _⟩ => nGlobal + 2 * arithWidth + setWidth
  | ⟨4, _⟩ => nGlobal + 2 * arithWidth + setWidth + derefWidth
  | ⟨5, _⟩ => nGlobal + 2 * arithWidth + setWidth + derefWidth + jumpWidth

def nColumns : Nat := tableBase ⟨5, by decide⟩ + keccakWidth

def log2Ceil (n : Nat) : Nat :=
  if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

def qKeccakSlots : Nat := stateLanes * (keccakRounds / keccakDepth)

def slotLog : Nat := log2Ceil qKeccakSlots

def qKeccakSpare : Nat := (1 <<< slotLog) - qKeccakSlots

def spareLocal (k : Nat) : Nat :=
  if k < keccakIn then k else keccakCnt + (k - keccakIn)

inductive KeccakLane where
  | slot (s : Nat)
  | output (l : Nat)
  deriving DecidableEq, Repr

def findSpare (loc : Nat) : Option Nat :=
  if loc < keccakIn then some (qKeccakSlots + loc)
  else if keccakCnt ≤ loc && loc < keccakCnt + (qKeccakSpare - keccakIn) then
    some (qKeccakSlots + keccakIn + (loc - keccakCnt))
  else none

def keccakValue (col : Nat) : Option KeccakLane :=
  let base := tableBase ⟨5, by decide⟩
  if col < base then none else
    let loc := col - base
    if loc >= keccakWidth then none else
      match findSpare loc with
      | some s => some (.slot s)
      | none =>
        if loc < keccakIn then none else
          let lane := loc - keccakIn
          if lane < stateLanes then some (.slot lane)
          else if lane < 2 * stateLanes then some (.output (lane - stateLanes))
          else none

def tableLogFloor : Fin nTables → Nat
  | ⟨5, _⟩ => keccakMinStepsLog
  | _ => 0

def tableLog (rows : Fin nTables → Nat) (t : Fin nTables) : Nat :=
  max (log2Ceil (rows t)) (tableLogFloor t)

structure Placement where
  variables : Nat
  index : Nat
  deriving DecidableEq, Repr

def insertDesc (kappas : Array Nat) (idx : Nat) (acc : List Nat) : List Nat :=
  let ki := kappas[idx]?.getD 0
  let (out, placed) :=
    acc.foldl
      (fun (out, placed) h =>
        if placed then (out ++ [h], true)
        else
          let kh := kappas[h]?.getD 0
          if kh < ki || (kh == ki && idx < h) then (out ++ [idx, h], true)
          else (out ++ [h], false))
      ([], false)
  if placed then out else out ++ [idx]

def stackOrder (kappas : Array Nat) : List Nat :=
  (List.range kappas.size).foldl (fun acc idx => insertDesc kappas idx acc) []

def stackOffsets (kappas : Array Nat) : Array Nat × Nat × Nat :=
  let (offsets, total) :=
    (stackOrder kappas).foldl
      (fun (offsets, total) index =>
        (offsets.set! index total, total + (1 <<< (kappas[index]?.getD 0))))
      (Array.replicate kappas.size 0, 0)
  (offsets, total, log2Ceil total)

structure Shape where
  mu : Nat
  nLanes : Nat
  deriving DecidableEq, Repr

def shapeOf (placed totalLog : Nat) : Shape :=
  let mu := max minStackedLog totalLog
  let lane := 1 <<< (mu - logBatch)
  { mu, nLanes := max 1 ((placed + lane - 1) / lane) }

def committedLen (shape : Shape) : Nat :=
  shape.nLanes <<< (shape.mu - logBatch)

def tableSource (col : Nat) : Option (Nat × Nat) :=
  let tableOrder : List (Fin nTables) :=
    [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩,
     ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩]
  tableOrder.findSome? fun t =>
    let base := tableBase t
    let width := tableWidth t
    if col >= base && col < base + width then some (2 + t.val, 0) else none

def kappaSource (logBytecode : Nat) (col : Nat) : Option (Nat × Nat) :=
  match keccakValue col with
  | some _ => none
  | none =>
    if col == memLo || col == memHi || col == memTop || col == memFinal then some (1, 0)
    else if col == bytecodeFinal then some (0, logBytecode)
    else if col == qKeccak then some (2 + opKeccak, slotLog)
    else tableSource col

def kappaOf (logMem logBytecode : Nat) (taus : Fin nTables → Nat) (col : Nat) : Option Nat :=
  match kappaSource logBytecode col with
  | none => none
  | some (source, adj) =>
    if source == 0 then some adj
    else if source == 1 then some (logMem + adj)
    else
      if h : source - 2 < nTables then some (taus ⟨source - 2, h⟩ + adj)
      else none

def placementsOf (logMem logBytecode : Nat) (taus : Fin nTables → Nat) :
    Array (Option Placement) × Shape × Nat :=
  let (kappas, owners) :=
    (List.range nColumns).foldl
      (fun (kappas, owners) col =>
        match kappaOf logMem logBytecode taus col with
        | none => (kappas, owners)
        | some kappa => (kappas.push kappa, owners.push col))
      (#[], #[])
  let (offsets, placed, totalLog) := stackOffsets kappas
  let shape := shapeOf placed totalLog
  let out0 :=
    (List.range owners.size).foldl
      (fun out i =>
        let col := owners[i]?.getD 0
        let kappa := kappas[i]?.getD 0
        let off := offsets[i]?.getD 0
        out.set! col (some { variables := kappa, index := off }))
      (Array.replicate nColumns none)
  let q := out0[qKeccak]?.join
  let stepLog := taus ⟨opKeccak, by decide⟩
  let out1 :=
    (List.range nColumns).foldl
      (fun out col =>
        match keccakValue col, q with
        | some (.slot slot), some place =>
          out.set! col (some {
            variables := stepLog
            index := place.index + (slot <<< stepLog)
          })
        | _, _ => out)
      out0
  (out1, shape, placed)

def sepState : K := Spec.Xmss.gpow 0
def sepMem : K := Spec.Xmss.gpow 1
def sepBytecode : K := Spec.Xmss.gpow 2

def opTag (t : Nat) : K := Spec.Xmss.gpow t

def derefFlagPc : Spec.Vm.DerefMode → K
  | .pc => 1
  | _ => 0

def derefFlagFp : Spec.Vm.DerefMode → K
  | .fp => 1
  | _ => 0

def bytecodeRow (op : Spec.Vm.Op) : Array K :=
  let g := Spec.Xmss.gpow
  let flag (b : Bool) : K := if b then 1 else 0
  match op with
  | .xor a b c =>
    #[opTag opXor, g a, g b, g c, 0, 0, 0, 0, 0, 0, 0]
  | .mul a b c =>
    #[opTag opMul, g a, g b, g c, 0, 0, 0, 0, 0, 0, 0]
  | .set o k =>
    #[opTag opSet, g o, k.c0, k.c1, k.c2, 0, 0, 0, 0, 0, 0]
  | .deref o1 o2 o3 mode =>
    #[opTag opDeref, g o1, g o2, g o3, derefFlagPc mode, derefFlagFp mode, 0, 0, 0, 0, 0]
  | .jump oc od of =>
    #[opTag opJump, g oc, g od, g of, 0, 0, 0, 0, 0, 0, 0]
  | .keccak m tail b8 cap out inOdd outOdd =>
    #[opTag opKeccak, g (m[0]?.getD 0), g (m[1]?.getD 0), g (m[2]?.getD 0), g (m[3]?.getD 0),
      g tail, g b8, g cap, g out, flag inOdd, flag outOdd]

def defaultOp : Spec.Vm.Op := .xor 0 0 0

def bytecodeColumns (prog : Array Spec.Vm.Op) : Array (Array K) :=
  (Array.range nBytecodeCols).map fun s =>
    prog.map fun op => (bytecodeRow op)[s]?.getD 0

def stackBytecodeColumns (logBytecode : Nat) (cols : Array (Array K)) : Array K :=
  let stride := 1 <<< logBytecode
  (List.range nBytecodeCols).foldl
    (fun table s =>
      let col := cols[s]?.getD #[]
      let base := (bytecodePublicSlot + s) * stride
      (List.range stride).foldl
        (fun tbl i => tbl.set! (base + i) (col[i]?.getD 0))
        table)
    (Array.replicate (1 <<< (busBits + logBytecode)) (0 : K))

def fiatShamirIv (table : Array K) : ByteArray :=
  Spec.Keccak.keccak256 (versionTag ++ Spec.Keccak.wordsBytes table)

def fsSeed (iv : ByteArray) : E × E :=
  (⟨Spec.Keccak.wordAt iv 0, Spec.Keccak.wordAt iv 8, 0⟩,
   ⟨Spec.Keccak.wordAt iv 16, Spec.Keccak.wordAt iv 24, 0⟩)

inductive Atom where
  | const (v : K)
  | col (i : Nat)
  | gcol (i k : Nat)
  | prod (i j k : Nat)
  deriving DecidableEq, Repr

inductive Coord where
  | atom (a : Atom)
  | index
  | publicCol (slot : Nat)
  | sum (terms : Array Atom)
  deriving DecidableEq, Repr

def cConst (v : K) : Coord := .atom (.const v)
def cCol (i : Nat) : Coord := .atom (.col i)
def cGCol (i k : Nat) : Coord := .atom (.gcol i k)
def cProd (i j k : Nat) : Coord := .atom (.prod i j k)

def offsetAtom (base : Nat) : Atom → Atom
  | .const v => .const v
  | .col i => .col (base + i)
  | .gcol i k => .gcol (base + i) k
  | .prod i j k => .prod (base + i) (base + j) k

def offsetCoord (base : Nat) : Coord → Coord
  | .atom a => .atom (offsetAtom base a)
  | .index => .index
  | .publicCol s => .publicCol s
  | .sum ts => .sum (ts.map (offsetAtom base))

def atomAt (a : Atom) (row : Array K) : K :=
  match a with
  | .const v => v
  | .col i => row[i]?.getD 0
  | .gcol i k => Spec.Field.mul (Spec.Xmss.gpow k) (row[i]?.getD 0)
  | .prod i j k =>
    Spec.Field.mul (Spec.Field.mul (Spec.Xmss.gpow k) (row[i]?.getD 0)) (row[j]?.getD 0)

def coordAt (c : Coord) (row : Array K) : K :=
  match c with
  | .atom a => atomAt a row
  | .index => 0
  | .publicCol _ => 0
  | .sum ts => ts.foldl (fun acc t => Spec.Field.add acc (atomAt t row)) 0

structure Block where
  kappa : Nat
  rows : Nat
  coords : Array Coord
  padding : Array K
  owner : Option (Fin nTables)
  deriving DecidableEq, Repr

def fullBlock (kappa : Nat) (coords : Array Coord) : Block :=
  { kappa, rows := 1 <<< kappa, coords, padding := #[], owner := none }

structure FlushPairs where
  push : Array (Array Coord) := #[]
  pull : Array (Array Coord) := #[]
  deriving DecidableEq, Repr

def FlushPairs.pair (fb : FlushPairs) (u v : Array Coord) : FlushPairs :=
  { push := fb.push.push u, pull := fb.pull.push v }

def FlushPairs.stateDerived (fb : FlushPairs) (pc fp : Nat) (npc nfp : Coord) : FlushPairs :=
  fb.pair #[cConst sepState, npc, nfp] #[cConst sepState, cCol pc, cCol fp]

def FlushPairs.stateStep (fb : FlushPairs) (pc fp : Nat) : FlushPairs :=
  fb.stateDerived pc fp (cGCol pc 1) (cCol fp)

def FlushPairs.bytecode (fb : FlushPairs) (pc count : Nat) (tag : K) (ops : Array Coord) : FlushPairs :=
  fb.pair (#[cConst sepBytecode, cCol pc, cGCol count 1, cConst tag] ++ ops)
    (#[cConst sepBytecode, cCol pc, cCol count, cConst tag] ++ ops)

def FlushPairs.memoryCoords (fb : FlushPairs) (addr : Coord) (count : Nat)
    (v0 v1 v2 : Coord) : FlushPairs :=
  fb.pair #[cConst sepMem, addr, cGCol count 1, v0, v1, v2]
    #[cConst sepMem, addr, cCol count, v0, v1, v2]

def FlushPairs.memory (fb : FlushPairs) (addr : Coord) (count v0 v1 v2 : Nat) : FlushPairs :=
  fb.memoryCoords addr count (cCol v0) (cCol v1) (cCol v2)

def FlushPairs.memoryK (fb : FlushPairs) (addr : Coord) (count val : Nat) : FlushPairs :=
  fb.memoryCoords addr count (cCol val) (cConst 0) (cConst 0)

def towerLanes : Fin 3 → Array (Nat × Nat)
  | ⟨0, _⟩ => #[(0, 0), (1, 2), (2, 1)]
  | ⟨1, _⟩ => #[(0, 1), (1, 0), (1, 2), (2, 1), (2, 2)]
  | ⟨2, _⟩ => #[(0, 2), (1, 1), (2, 0), (2, 2)]

def arithResult (isXor : Bool) : Coord × Coord × Coord :=
  let va := #[5, 6, 7]
  let vb := #[8, 9, 10]
  if isXor then
    (.sum #[.col 5, .col 8], .sum #[.col 6, .col 9], .sum #[.col 7, .col 10])
  else
    let lane (idx : Fin 3) : Coord :=
      .sum ((towerLanes idx).map fun (j, k) => .prod va[j]! vb[k]! 0)
    (lane ⟨0, by decide⟩, lane ⟨1, by decide⟩, lane ⟨2, by decide⟩)

def flushesArith (isXor : Bool) : FlushPairs :=
  let tag := opTag (if isXor then opXor else opMul)
  let ops := #[cCol 2, cCol 3, cCol 4, cConst 0, cConst 0]
  let (r0, r1, r2) := arithResult isXor
  ({} : FlushPairs)
    |>.stateStep 0 1
    |>.bytecode 0 14 tag ops
    |>.memory (cProd 1 2 0) 11 5 6 7
    |>.memory (cProd 1 3 0) 12 8 9 10
    |>.memoryCoords (cProd 1 4 0) 13 r0 r1 r2

def flushesSet : FlushPairs :=
  let ops := #[cCol 2, cCol 3, cCol 4, cCol 5, cConst 0]
  ({} : FlushPairs)
    |>.stateStep 0 1
    |>.bytecode 0 7 (opTag opSet) ops
    |>.memory (cProd 1 2 0) 6 3 4 5

def derefStore : Coord × Coord × Coord :=
  let gated (v : Nat) : Array Atom := #[.col v, .prod 5 v 0, .prod 6 v 0]
  (.sum (gated 8 ++ #[.prod 5 0 2, .prod 6 1 0]),
   .sum (gated 9),
   .sum (gated 10))

def flushesDeref : FlushPairs :=
  let ops := #[cCol 2, cCol 3, cCol 4, cCol 5, cCol 6]
  let (s0, s1, s2) := derefStore
  ({} : FlushPairs)
    |>.stateStep 0 1
    |>.bytecode 0 14 (opTag opDeref) ops
    |>.memoryK (cProd 1 2 0) 11 7
    |>.memoryCoords (cProd 7 3 0) 12 s0 s1 s2
    |>.memory (cProd 1 4 0) 13 8 9 10

def flushesJump : FlushPairs :=
  let npc : Coord := .sum #[.prod 13 6 0, .prod 13 0 1, .gcol 0 1]
  let nfp : Coord := .sum #[.prod 13 7 0, .prod 13 1 0, .col 1]
  let ops := #[cCol 2, cCol 3, cCol 4, cConst 0, cConst 0]
  ({} : FlushPairs)
    |>.stateDerived 0 1 npc nfp
    |>.bytecode 0 11 (opTag opJump) ops
    |>.memoryK (cProd 1 2 0) 8 5
    |>.memoryK (cProd 1 3 0) 9 6
    |>.memoryK (cProd 1 4 0) 10 7

def keccakCellSpec (c : Nat) : Nat × Nat :=
  if c < 4 then (c, 0)
  else if c < 8 then (4, c - 4)
  else if c == 8 then (5, 0)
  else if c < 13 then (6, c - 9)
  else (7, c - 13)

def layoutLimb (even odd : Option Nat) (values flag : Nat) (missing : Option Nat) : Coord :=
  let pick (lane : Option Nat) : Option Nat :=
    match lane with
    | some l => some (values + l)
    | none => missing
  let a := pick even
  let b := pick odd
  if a == b then
    match a with
    | some col => cCol col
    | none => cConst 0
  else
    let termsA : Array Atom :=
      match a with
      | some col => #[.col col, .prod flag col 0]
      | none => #[]
    let termsB : Array Atom :=
      match b with
      | some col => #[.prod flag col 0]
      | none => #[]
    .sum (termsA ++ termsB)

def flushesKeccak : FlushPairs :=
  let fb0 := ({} : FlushPairs).stateStep 0 1
  let ops : Array Coord :=
    #[cCol 2, cCol 3, cCol 4, cCol 5, cCol 6, cCol 7, cCol 8, cCol 9, cCol 10, cCol 11]
  let fb1 := fb0.bytecode 0 keccakCntBc (opTag opKeccak) ops
  (List.range (2 * keccakCells)).foldl
    (fun fb c =>
      let (operand, step) := keccakCellSpec c
      let (s, values, flag, free) :=
        if c < keccakCells then (c, keccakIn, 10, some 12)
        else (c - keccakCells, keccakOut, 11, none)
      let (eLo, eHi) := Spec.Vm.KeccakInternal.cellLanes false s
      let (oLo, oHi) := Spec.Vm.KeccakInternal.cellLanes true s
      let lo := layoutLimb eLo oLo values flag free
      let hi := layoutLimb eHi oHi values flag free
      fb.memoryCoords (cProd 1 (2 + operand) step) (keccakCnt + c) lo hi (cConst 0))
    fb1

def tableFlushes : Fin nTables → FlushPairs
  | ⟨0, _⟩ => flushesArith true
  | ⟨1, _⟩ => flushesArith false
  | ⟨2, _⟩ => flushesSet
  | ⟨3, _⟩ => flushesDeref
  | ⟨4, _⟩ => flushesJump
  | ⟨5, _⟩ => flushesKeccak

def tableCountColumns : Fin nTables → Array Nat
  | ⟨0, _⟩ => #[11, 12, 13, 14]
  | ⟨1, _⟩ => #[11, 12, 13, 14]
  | ⟨2, _⟩ => #[6, 7]
  | ⟨3, _⟩ => #[11, 12, 13, 14]
  | ⟨4, _⟩ => #[8, 9, 10, 11]
  | ⟨5, _⟩ =>
    #[63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89]

def tablePadding : Fin nTables → Array K
  | ⟨5, _⟩ =>
    let out := Spec.Keccak.permute Spec.Keccak.zero
    (List.range stateLanes).foldl
      (fun row l => row.set! (keccakOut + l) (out[l]?.getD 0))
      (Array.replicate keccakWidth (0 : K))
  | t => Array.replicate (tableWidth t) 0

def tableConstraints : Fin nTables → Nat
  | ⟨4, _⟩ => 2
  | _ => 0

def xiFormBase : Nat :=
  (List.range nTables).foldl
    (fun acc t => if h : t < nTables then acc + tableConstraints ⟨t, h⟩ else acc) 0

def sharedPushBlocks (logMem logBytecode : Nat) : Array Block :=
  let bcCoords := #[cConst sepBytecode, .index, cConst 1] ++
    (Array.range nBytecodeCols).map Coord.publicCol
  #[fullBlock 0 #[cConst sepState, cConst 1, cConst 1],
    fullBlock logMem #[cConst sepMem, .index, cConst 1, cCol memLo, cCol memHi, cCol memTop],
    fullBlock logBytecode bcCoords]

def sharedPullBlocks (logMem logBytecode : Nat) : Array Block :=
  let finalPc := Spec.Xmss.gpow ((1 <<< logBytecode) - 1)
  let bcCoords := #[cConst sepBytecode, .index, cCol bytecodeFinal] ++
    (Array.range nBytecodeCols).map Coord.publicCol
  #[fullBlock 0 #[cConst sepState, cConst finalPc, cConst 1],
    fullBlock logMem #[cConst sepMem, .index, cCol memFinal, cCol memLo, cCol memHi, cCol memTop],
    fullBlock logBytecode bcCoords]

def mkTableBlock (t : Fin nTables) (tau rowCount : Nat) (padRow : Array K)
    (coords : Array Coord) : Block :=
  let base := tableBase t
  { kappa := tau
    rows := rowCount
    padding := coords.map (coordAt · padRow)
    coords := coords.map (offsetCoord base)
    owner := some t }

def busBlocks (logMem logBytecode : Nat) (rows taus : Fin nTables → Nat) :
    Array Block × Array Block × Array Block :=
  let tableOrder : List (Fin nTables) :=
    [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩,
     ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩]
  tableOrder.foldl
    (fun (push, pull, count) t =>
      let tau := taus t
      let r := rows t
      let pad := tablePadding t
      let fl := tableFlushes t
      let push' := push ++ fl.push.map (mkTableBlock t tau r pad)
      let pull' := pull ++ fl.pull.map (mkTableBlock t tau r pad)
      let count' := count ++ (tableCountColumns t).map (fun c => mkTableBlock t tau r pad #[cCol c])
      (push', pull', count'))
    (sharedPushBlocks logMem logBytecode, sharedPullBlocks logMem logBytecode, #[])

structure BusLayout where
  mu : Nat
  offsets : Array Nat
  deriving DecidableEq, Repr

def busSideLayout (blocks : Array Block) : BusLayout :=
  let kappas := blocks.map (·.kappa)
  let (offsets, placed, _) := stackOffsets kappas
  { mu := log2Ceil (max 1 placed), offsets }

end LeanVmXmss.Spec.Layout
