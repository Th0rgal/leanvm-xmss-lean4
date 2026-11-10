import Spec.Layout.Basic
import Spec.Pcs.Commit
import Spec.Transcript.Basic
import Spec.Vm.Hints
import Model.Field.NativeKernel
import Model.Keccak.Registers
import Model.Layout.Scalar
import Model.Pcs.Commit
import Model.Transcript.Registers
import Model.Vm.Linear

namespace LeanVmXmss.Spec.Witness

open Spec.Field (K E)
open Spec.Layout
open Spec.Vm

def logInvRateDefault : Nat := 1

structure StepTrace where
  pc : Nat
  fp : Nat
  bytecodeRead : Nat
  extras : Array Nat
  deriving Inhabited, Repr

structure ExecutionTrace where
  tables : Array (Array StepTrace)
  bytecodeCount : Array Nat
  cycles : Nat
  memUsed : Nat
  unconstrained : Nat
  memory : Memory
  g : GPow
  deriving Inhabited

def emptyTrace : ExecutionTrace :=
  { tables := Array.replicate nTables #[], bytecodeCount := #[], cycles := 0,
    memUsed := 0, unconstrained := 0, memory := {}, g := {} }

def rowCount (trace : @& ExecutionTrace) (table : Nat) : Nat :=
  (trace.tables[table]?.getD #[]).size

def rowsOf (trace : ExecutionTrace) : Array Nat :=
  (Array.range nTables).map (rowCount trace)

def log2FloorPow2 (n : Nat) : Nat :=
  if n ≤ 1 then 0 else Nat.log2 (n / 2) + 1

def pow2 (k : Nat) : Nat := 1 <<< k

def memoryCells (memUsed : Nat) : Nat :=
  max (pow2 minLogMem) (pow2 (log2Ceil (max memUsed 1)))

structure SizedRun where
  trace : ExecutionTrace
  logMem : Nat
  logBytecode : Nat
  cells : Nat
  rows : Array Nat
  layout : Model.Layout.PublicLayout

def sizeRun (program : Array Op) (trace : ExecutionTrace) : SizedRun :=
  let rows := rowsOf trace
  let logBytecode := log2FloorPow2 program.size
  let cells := memoryCells trace.memory.used
  { trace, logMem := log2FloorPow2 cells, logBytecode, cells, rows,
    layout := Model.Layout.buildPublicLayout (log2FloorPow2 cells) logBytecode rows }

def gAt (g : GPow) (n : Nat) : K := g.powers[n]?.getD 0

def cellWord (memory : Memory) (address : Nat) : E :=
  (Model.Vm.cellAt memory.cells address).word

def zeroColumn (height : Nat) : Array K := Array.replicate height 0

def writeRows (height : Nat) (rows : Array StepTrace) (padding : Array K)
    (base offset width : Nat) (project : StepTrace → Array K) (out : Array (Array K)) :
    Array (Array K) :=
  let projected := rows.map project
  Model.Pcs.Ntt.foldRange width
    (fun out lane =>
      let padVal := padding[offset + lane]?.getD 0
      let filled := Model.Pcs.Ntt.foldRange rows.size
        (fun column row =>
          let value := (projected[row]?.getD #[])[lane]?.getD 0
          column.setIfInBounds row value)
        (Array.replicate height padVal)
      out.setIfInBounds (base + offset + lane) filled)
    out

def arithPadding : Array K := Array.replicate arithWidth 0
def setPadding : Array K := Array.replicate setWidth 0
def derefPadding : Array K := Array.replicate derefWidth 0
def jumpPadding : Array K := Array.replicate jumpWidth 0

def keccakPaddingValue : Array K :=
  let state := (Model.Keccak.rounds25 keccakRounds 0 Model.Layout.zeroState25).toSpec
  Model.Pcs.Ntt.foldRange stateLanes
    (fun row lane => row.setIfInBounds (keccakOut + lane) (state[lane]?.getD 0))
    (Array.replicate keccakWidth 0)

def fillBinary (base : Nat) (memory : Memory) (g : GPow) (height : Nat)
    (rows : Array StepTrace) (out : Array (Array K)) : Array (Array K) :=
  writeRows height rows arithPadding base 0 arithWidth
    (fun row =>
      let a := row.extras[0]?.getD 0
      let b := row.extras[1]?.getD 0
      let c := row.extras[2]?.getD 0
      let va := cellWord memory (row.fp + a)
      let vb := cellWord memory (row.fp + b)
      #[gAt g row.pc, gAt g row.fp, gAt g a, gAt g b, gAt g c,
        va.c0, va.c1, va.c2, vb.c0, vb.c1, vb.c2,
        gAt g (row.extras[3]?.getD 0), gAt g (row.extras[4]?.getD 0),
        gAt g (row.extras[5]?.getD 0), gAt g row.bytecodeRead])
    out

def fillSet (program : Array Op) (g : GPow) (height : Nat) (rows : Array StepTrace)
    (out : Array (Array K)) : Array (Array K) :=
  writeRows height rows setPadding (tableBase ⟨2, by decide⟩) 0 setWidth
    (fun row =>
      match program[row.pc]? with
      | some (.set offset value) =>
        #[gAt g row.pc, gAt g row.fp, gAt g offset, value.c0, value.c1, value.c2,
          gAt g (row.extras[0]?.getD 0), gAt g row.bytecodeRead]
      | _ => Array.replicate setWidth 0)
    out

def fillDeref (program : Array Op) (memory : Memory) (g : GPow) (height : Nat)
    (rows : Array StepTrace) (out : Array (Array K)) : Array (Array K) :=
  writeRows height rows derefPadding (tableBase ⟨3, by decide⟩) 0 derefWidth
    (fun row =>
      match program[row.pc]? with
      | some (.deref o1 o2 o3 mode) =>
        let word3 := cellWord memory (row.fp + o3)
        #[gAt g row.pc, gAt g row.fp, gAt g o1, gAt g o2, gAt g o3,
          derefFlagPc mode, derefFlagFp mode, (cellWord memory (row.fp + o1)).c0,
          word3.c0, word3.c1, word3.c2, gAt g (row.extras[0]?.getD 0),
          gAt g (row.extras[1]?.getD 0), gAt g (row.extras[2]?.getD 0),
          gAt g row.bytecodeRead]
      | _ => Array.replicate derefWidth 0)
    out

def conditionAt (memory : Memory) (row : StepTrace) : E :=
  cellWord memory (row.fp + (row.extras[3]?.getD 0))

def jumpScan (rows : Array StepTrace) (memory : Memory) :
    E × Array E × Array K :=
  Model.Pcs.Ntt.foldRange rows.size
    (fun acc index =>
      let ⟨prod, prefixes, bits⟩ := acc
      let condition := conditionAt memory (rows[index]?.getD default)
      if condition.c0 = 0 && condition.c1 = 0 && condition.c2 = 0 then
        (prod, prefixes.setIfInBounds index prod, bits.setIfInBounds index 0)
      else
        (Model.Field.nativeKaratsuba prod condition,
          prefixes.setIfInBounds index prod, bits.setIfInBounds index 1))
    (Spec.Field.one, Array.replicate rows.size Spec.Field.zero, Array.replicate rows.size 0)

def jumpInverse (rows : Array StepTrace) (memory : Memory) (prefixes : Array E)
    (full : E) : Array K :=
  (Model.Pcs.Ntt.foldRange rows.size
    (fun acc step =>
      let index := rows.size - 1 - step
      let condition := conditionAt memory (rows[index]?.getD default)
      if condition.c0 = 0 && condition.c1 = 0 && condition.c2 = 0 then acc
      else
        let ⟨invAcc, outArr⟩ := acc
        let witness := Model.Field.nativeKaratsuba invAcc (prefixes[index]?.getD Spec.Field.zero)
        (Model.Field.nativeKaratsuba invAcc condition, outArr.setIfInBounds index witness.c0))
    (Model.Vm.inverseLinear full, Array.replicate rows.size 0)).2

def fillJump (memory : Memory) (g : GPow) (height : Nat) (rows : Array StepTrace)
    (out : Array (Array K)) : Array (Array K) :=
  let scanned := jumpScan rows memory
  let inverse := jumpInverse rows memory scanned.2.1 scanned.1
  writeRows height rows jumpPadding (tableBase ⟨4, by decide⟩) 0 jumpWidth
    (fun row =>
      let index := row.extras[6]?.getD 0
      let oc := row.extras[3]?.getD 0
      let od := row.extras[4]?.getD 0
      let of_ := row.extras[5]?.getD 0
      #[gAt g row.pc, gAt g row.fp, gAt g oc, gAt g od, gAt g of_,
        (cellWord memory (row.fp + oc)).c0, (cellWord memory (row.fp + od)).c0,
        (cellWord memory (row.fp + of_)).c0, gAt g (row.extras[0]?.getD 0),
        gAt g (row.extras[1]?.getD 0), gAt g (row.extras[2]?.getD 0),
        gAt g row.bytecodeRead, inverse[index]?.getD 0, scanned.2.2[index]?.getD 0])
    out

def keccakOffsets (op : Op) : Array Nat :=
  match op with
  | .keccak message tail b8 cap output _ _ => message.extract 0 4 ++ #[tail, b8, cap, output]
  | _ => Array.replicate 8 0

def keccakAddress (fp : Nat) (offsets : Array Nat) (cell : Nat) : Nat :=
  let place := keccakCellSpec cell
  fp + (offsets[place.1]?.getD 0) + place.2

def fillKeccak (program : Array Op) (memory : Memory) (g : GPow) (height : Nat)
    (rows : Array StepTrace) (out : Array (Array K)) : Array (Array K) :=
  let base := tableBase ⟨5, by decide⟩
  let head := writeRows height rows keccakPaddingValue base 0 keccakIn
    (fun row =>
      match program[row.pc]? with
      | some op@(.keccak _ _ _ _ _ inOdd outOdd) =>
        let offsets := keccakOffsets op
        let powers := (Array.range 8).map fun index => gAt g (offsets[index]?.getD 0)
        let word := cellWord memory (keccakAddress row.fp offsets (if inOdd then 0 else 8))
        #[gAt g row.pc, gAt g row.fp] ++ powers ++
          #[if inOdd then 1 else 0, if outOdd then 1 else 0, if inOdd then word.c0 else word.c1]
      | _ => Array.replicate keccakIn 0)
    out
  let counts := writeRows height rows keccakPaddingValue base keccakCnt (2 * keccakCells)
    (fun row => (Array.range (2 * keccakCells)).map fun index => gAt g (row.extras[index]?.getD 0))
    head
  writeRows height rows keccakPaddingValue base keccakCntBc 1
    (fun row => #[gAt g row.bytecodeRead]) counts

def maxNatArray (values : Array Nat) : Nat :=
  Model.Pcs.Ntt.foldRange values.size
    (fun best index => max best (values[index]?.getD 0))
    0

def maxCellAccesses (memory : Memory) : Nat :=
  Model.Pcs.Ntt.foldRange memory.used
    (fun best index => max best (Model.Vm.cellAt memory.cells index).accesses)
    0

def fillShared (sized : SizedRun) (g : GPow) : Array (Array K) :=
  let memory := sized.trace.memory
  let used := min sized.cells memory.used
  let c0 := Model.Pcs.Ntt.foldRange used
    (fun col i => col.setIfInBounds i (Model.Vm.cellAt memory.cells i).word.c0)
    (zeroColumn sized.cells)
  let c1 := Model.Pcs.Ntt.foldRange used
    (fun col i => col.setIfInBounds i (Model.Vm.cellAt memory.cells i).word.c1)
    (zeroColumn sized.cells)
  let c2 := Model.Pcs.Ntt.foldRange used
    (fun col i => col.setIfInBounds i (Model.Vm.cellAt memory.cells i).word.c2)
    (zeroColumn sized.cells)
  let c3 := Model.Pcs.Ntt.foldRange sized.cells
    (fun col i =>
      let acc := if i < memory.used then (Model.Vm.cellAt memory.cells i).accesses else 0
      col.setIfInBounds i (gAt g acc))
    (zeroColumn sized.cells)
  let image := (Array.replicate nColumns #[])
    |>.setIfInBounds 0 c0
    |>.setIfInBounds 1 c1
    |>.setIfInBounds 2 c2
    |>.setIfInBounds 3 c3
  image.setIfInBounds bytecodeFinal
    (Model.Pcs.Ntt.foldRange (pow2 sized.logBytecode)
      (fun column index =>
        column.setIfInBounds index (gAt g (sized.trace.bytecodeCount[index]?.getD 0)))
      (zeroColumn (pow2 sized.logBytecode)))

def inputState25 (program : Array Op) (memory : Memory) (row : StepTrace) :
    Model.Keccak.State25 :=
  match program[row.pc]? with
  | some op@(.keccak _ _ _ _ _ inOdd _) =>
    let offsets := keccakOffsets op
    Model.Keccak.State25.fromSpec <|
      KeccakInternal.stateOfCells inOdd
        ((Array.range keccakCells).map fun index =>
          cellWord memory (keccakAddress row.fp offsets index))
  | _ => Model.Layout.zeroState25

def fillQKeccak (program : Array Op) (rows : Array StepTrace) (memory : Memory)
    (height : Nat) : Array K :=
  let zeroMid := (Model.Keccak.rounds25 keccakDepth 0 Model.Layout.zeroState25).toSpec
  let base := Model.Pcs.Ntt.foldRange stateLanes
    (fun column lane =>
      let padVal := zeroMid[lane]?.getD 0
      if padVal = 0 then column
      else
        Model.Pcs.Ntt.foldRange (height - rows.size)
          (fun col offset =>
            let step := rows.size + offset
            col.setIfInBounds ((stateLanes + lane) * height + step) padVal)
          column)
    (Array.replicate (qKeccakSlots * height) 0)
  Model.Pcs.Ntt.foldRange rows.size
    (fun column step =>
      let start := inputState25 program memory (rows[step]?.getD default)
      let inSpec := start.toSpec
      let midSpec := (Model.Keccak.rounds25 keccakDepth 0 start).toSpec
      let column := Model.Pcs.Ntt.foldRange stateLanes
        (fun col lane => col.setIfInBounds (lane * height + step) (inSpec[lane]?.getD 0))
        column
      Model.Pcs.Ntt.foldRange stateLanes
        (fun col lane =>
          col.setIfInBounds ((stateLanes + lane) * height + step) (midSpec[lane]?.getD 0))
        column)
    base

def placeColumn (placement : Option Placement) (source : Array K) (message : Array K) : Array K :=
  match placement with
  | none => message
  | some place =>
    Model.Pcs.Ntt.foldRange (pow2 place.variables)
      (fun message row => message.setIfInBounds (place.index + row) (source[row]?.getD 0))
      message

def stackedMessage (sized : SizedRun) (windows : Array (Array K)) : Array K :=
  let placed := Model.Pcs.Ntt.foldRange nColumns
    (fun message column =>
      if column == qKeccak then message
      else if (keccakValue column).isSome then message
      else placeColumn (sized.layout.placements[column]?.join) (windows[column]?.getD #[]) message)
    (Array.replicate (committedLen sized.layout.shape) 0)
  let qBase := (sized.layout.placements[qKeccak]?.join).map Placement.index |>.getD 0
  let steps := pow2 (sized.layout.taus[opKeccak]?.getD 0)
  let qWindow := windows[qKeccak]?.getD #[]
  let withQ := Model.Pcs.Ntt.foldRange qWindow.size
    (fun message index =>
      message.setIfInBounds (qBase + index) (qWindow[index]?.getD 0))
    placed
  Model.Pcs.Ntt.foldRange qKeccakSpare
    (fun message spare =>
      let source := windows[tableBase ⟨5, by decide⟩ + spareLocal spare]?.getD #[]
      Model.Pcs.Ntt.foldRange steps
        (fun message row =>
          message.setIfInBounds (qBase + (qKeccakSlots + spare) * steps + row) (source[row]?.getD 0))
        message)
    withQ

def announceWords (sized : SizedRun) : Array E :=
  #[Spec.Field.embed (UInt64.ofNat sized.logMem)] ++
    sized.rows.map (fun count => Spec.Field.embed (UInt64.ofNat count)) ++
    #[Spec.Field.embed (UInt64.ofNat logInvRateDefault)]

def wordBytes (bytes : ByteArray) (word : E) : ByteArray :=
  Model.Layout.pushWordLE (Model.Layout.pushWordLE (Model.Layout.pushWordLE bytes word.c0) word.c1) word.c2

def announceDigest (sized : SizedRun) : ByteArray :=
  Model.Layout.keccak256Stream ((announceWords sized).foldl wordBytes ByteArray.empty)

def publicBytes (publicInput : Array E) : ByteArray :=
  let first := publicInput[0]?.getD Spec.Field.zero
  let second := publicInput[1]?.getD Spec.Field.zero
  Model.Layout.pushWordLE (Model.Layout.pushWordLE
    (Model.Layout.pushWordLE (Model.Layout.pushWordLE ByteArray.empty first.c0) first.c1)
    second.c0) second.c1

def sampleAfter (start : Model.Transcript.Registers.Sponge) (words : Array E) :
    E × Model.Transcript.Registers.Sponge :=
  Model.Transcript.Registers.sample (words.foldl Model.Transcript.Registers.observe start)

def challengePair (iv : ByteArray) (publicInput : Array E) (sized : SizedRun)
    (root : ByteArray) : E × E :=
  let first := sampleAfter (Model.Transcript.Registers.init iv (publicBytes publicInput))
    (announceWords sized)
  let roots := Spec.Merkle.hashToScalars root
  (first.1, (sampleAfter first.2 #[roots.1, roots.2]).1)

def l0Root (message : Array K) (shape : Shape) : ByteArray :=
  Model.Pcs.Commit.rootBytes message shape.nLanes (shape.mu - logBatch) logInvRateDefault

structure WitnessBundle where
  sized : SizedRun
  message : Array K
  root : ByteArray
  announce : ByteArray
  challenge : E
  official : E

def bundleOf (program : Array Op) (iv : ByteArray) (publicInput : Array E)
    (trace : ExecutionTrace) : WitnessBundle :=
  let sized := sizeRun program trace
  let maxCount := max (maxNatArray trace.bytecodeCount) (maxCellAccesses trace.memory)
  let g := Model.Vm.growLinear trace.g (max trace.memUsed (max program.size maxCount))
  let heights := sized.layout.taus.map pow2
  let shared := fillShared sized g
  let binary := fillBinary (tableBase ⟨0, by decide⟩) trace.memory g
    (heights[0]?.getD 1) (trace.tables[0]?.getD #[]) shared
  let multiplied := fillBinary (tableBase ⟨1, by decide⟩) trace.memory g
    (heights[1]?.getD 1) (trace.tables[1]?.getD #[]) binary
  let sets := fillSet program g (heights[2]?.getD 1) (trace.tables[2]?.getD #[]) multiplied
  let derefs := fillDeref program trace.memory g (heights[3]?.getD 1)
    (trace.tables[3]?.getD #[]) sets
  let jumps := fillJump trace.memory g (heights[4]?.getD 1) (trace.tables[4]?.getD #[]) derefs
  let keccakRows := trace.tables[5]?.getD #[]
  let keccak := fillKeccak program trace.memory g (heights[5]?.getD 1) keccakRows jumps
  let windows := keccak.setIfInBounds qKeccak
    (fillQKeccak program keccakRows trace.memory (heights[5]?.getD 1))
  let message := stackedMessage sized windows
  let root := l0Root message sized.layout.shape
  let pair := challengePair iv publicInput sized root
  { sized, message, root, announce := announceDigest sized, challenge := pair.1, official := pair.2 }

def pushRow (table : Nat) (row : StepTrace) (trace : ExecutionTrace) : ExecutionTrace :=
  let ⟨tables, bytecodeCount, cycles, memUsed, unconstrained, memory, g⟩ := trace
  let tables' := tables.modify table (fun rows => rows.push row)
  ⟨tables', bytecodeCount, cycles, memUsed, unconstrained, memory, g⟩

def bumpCounts (addresses : @& Array Nat) (cells : @& Array Cell) : Array Nat :=
  Model.Pcs.Ntt.foldRange addresses.size
    (fun (counts : Array Nat) index =>
      let address := addresses[index]?.getD 0
      let base := (Model.Vm.cellAt cells address).accesses
      let prior := Model.Pcs.Ntt.foldRange index
        (fun acc prev => if (addresses[prev]?.getD 0) = address then acc + 1 else acc)
        0
      counts.push (base + prior))
    (Array.emptyWithCapacity addresses.size)

def binaryExtras (fp a b c : Nat) (cells : @& Array Cell) : Array Nat :=
  #[a, b, c] ++ bumpCounts #[fp + a, fp + b, fp + c] cells

def capture (op : @& Op) (beforeCells : @& Array Cell) (g : @& GPow)
    (pc fp : Nat) (trace : ExecutionTrace) (readCount : Nat) :
    Except Fault ExecutionTrace := do
  let row (extras : Array Nat) : StepTrace := ⟨pc, fp, readCount, extras⟩
  match op with
  | .xor a b c => return pushRow 0 (row (binaryExtras fp a b c beforeCells)) trace
  | .mul a b c => return pushRow 1 (row (binaryExtras fp a b c beforeCells)) trace
  | .set offset _ => return pushRow 2 (row (bumpCounts #[fp + offset] beforeCells)) trace
  | .deref o1 o2 o3 _ =>
    let base ← Model.Vm.logLinear g (Model.Vm.cellAt beforeCells (fp + o1)).word
    return pushRow 3 (row (bumpCounts #[fp + o1, base + o2, fp + o3] beforeCells)) trace
  | .jump oc od of =>
    let jIdx := rowCount trace 4
    return pushRow 4 (row (bumpCounts #[fp + oc, fp + od, fp + of] beforeCells ++
      #[oc, od, of, jIdx])) trace
  | .keccak .. =>
    let offsets := keccakOffsets op
    let addresses := (Array.range (2 * keccakCells)).map fun index =>
      keccakAddress fp offsets index
    return pushRow 5 (row (bumpCounts addresses beforeCells)) trace

def runLoop (fuel : Nat) (program : @& Array Op) (hints : @& Array (Array RHint))
    (runtime : Runtime) (trace : ExecutionTrace) : Except Fault (Runtime × ExecutionTrace) :=
  Nat.rec (motive := fun _ => Runtime → ExecutionTrace → Except Fault (Runtime × ExecutionTrace))
    (fun _ _ => .error Fault.stepLimit)
    (fun _ previous runtime trace =>
      if runtime.state.pc + 1 = program.size && runtime.state.fp = 0 then .ok (runtime, trace)
      else match program[runtime.state.pc]? with
      | none => .error Fault.badProgram
      | some op => match Model.Vm.applyHintsLinear (hints[runtime.state.pc]?.getD #[]) runtime with
        | .error fault => .error fault
        | .ok ⟨⟨mem0, pc, fp, nextFree, g0, cycles, opcodeCounts⟩, streams⟩ =>
          let g := Model.Vm.growLinear g0 (max (pc + 2) fp)
          let ⟨tables0, bcCounts0, _, tMemUsed, tUncon, tMem, tG⟩ := trace
          let bcCounts := if bcCounts0.size = program.size then bcCounts0
            else Array.replicate program.size 0
          let readCount := bcCounts[pc]?.getD 0
          let trace0 : ExecutionTrace := ⟨tables0, #[], 0, tMemUsed, tUncon, tMem, tG⟩
          match capture op mem0.cells g pc fp trace0 readCount with
          | .error fault => .error fault
          | .ok ⟨tables, _, _, _, _, _, _⟩ =>
            match Model.Vm.stepBodyLinear op mem0 pc fp opcodeCounts g with
            | .error fault => .error fault
            | .ok stepped =>
              let state : State := ⟨stepped.1, stepped.2.1, stepped.2.2.1, nextFree, g,
                cycles + 1, stepped.2.2.2⟩
              previous ⟨state, streams⟩
                ⟨tables, bcCounts.setIfInBounds pc (readCount + 1), state.cycles, tMemUsed, tUncon, tMem, tG⟩)
    fuel runtime trace

def executeTrace (fuel : Nat) (program : Array Op) (hints : Array (Array RHint))
    (runtime : Runtime) : Except Fault ExecutionTrace := do
  let initTrace : ExecutionTrace :=
    ⟨Array.replicate nTables #[], Array.replicate program.size 0, 0, 0, 0, {}, {}⟩
  let result ← runLoop fuel program hints runtime initTrace
  let ⟨tables, bcCounts, cycles, _, _, _, _⟩ := result.2
  return ⟨tables, bcCounts, cycles, result.1.state.memory.used,
    result.1.state.memory.unconstrainedReads.size, result.1.state.memory, result.1.state.g⟩

def proveBundle (fuel : Nat) (program : Array Op) (hints : Array (Array RHint))
    (runtime : Runtime) (iv : ByteArray) : Except Fault WitnessBundle := do
  let trace ← executeTrace fuel program hints runtime
  let publicInput := #[cellWord runtime.state.memory 0, cellWord runtime.state.memory 1]
  return bundleOf program iv publicInput trace

end LeanVmXmss.Spec.Witness
