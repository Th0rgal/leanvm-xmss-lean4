import Model.Witness.Scalar
import Spec.KeccakGkr.Basic
import Native.Kernels.VmWitness

namespace LeanVmXmss.Model.Witness

open Spec.Field (K E)
open Spec.Layout Spec.Witness
open Model.Pcs.Ntt (Vec8 foldRange foldRangeLoop)
open Model.Pcs.Commit (rowWords zeroPrefixState absorbWords17 absorbFinal13 hashPair25 subtreeRoot subtreeRootBuf)

structure PlanarNat where
  bytes : ByteArray
  deriving Inhabited

def planarNatEmpty (n : Nat) : PlanarNat :=
  ⟨ByteArray.emptyWithCapacity (8 * n)⟩

@[noinline] def pushU64LE (bytes : ByteArray) (w : UInt64) : ByteArray :=
  foldRange 8 (fun acc i => acc.push ((w >>> UInt64.ofNat (8 * i)).toUInt8)) bytes

@[noinline] def readU64LE (bytes : @& ByteArray) (index : Nat) : UInt64 :=
  let b := 8 * index
  let lo :=
    (bytes[b]?.getD 0).toUInt64 |||
    ((bytes[b + 1]?.getD 0).toUInt64 <<< 8) |||
    ((bytes[b + 2]?.getD 0).toUInt64 <<< 16) |||
    ((bytes[b + 3]?.getD 0).toUInt64 <<< 24)
  let hi :=
    ((bytes[b + 4]?.getD 0).toUInt64 <<< 32) |||
    ((bytes[b + 5]?.getD 0).toUInt64 <<< 40) |||
    ((bytes[b + 6]?.getD 0).toUInt64 <<< 48) |||
    ((bytes[b + 7]?.getD 0).toUInt64 <<< 56)
  lo ||| hi

def planarPush (p : PlanarNat) (n : Nat) : PlanarNat :=
  ⟨pushU64LE p.bytes (UInt64.ofNat n)⟩

def planarGet (p : @& PlanarNat) (i : Nat) : Nat :=
  (readU64LE p.bytes i).toNat

def decodePlanarNat (p : @& PlanarNat) : Array Nat :=
  let n := p.bytes.size / 8
  foldRange n (fun acc i => acc.push (planarGet p i)) (Array.emptyWithCapacity n)

def bumpCountsFlat (addresses : @& Array Nat) (cells : @& Array Spec.Vm.Cell) : PlanarNat :=
  let n := addresses.size
  let limit := foldRange n (fun m i => max m ((addresses[i]?.getD 0) + 1)) 1
  (foldRange n (fun (acc, seen) i =>
    let a := addresses[i]?.getD 0
    let pr := seen[a]?.getD 0
    let next := planarPush acc ((Model.Vm.cellAt cells a).accesses + pr)
    (next, seen.setIfInBounds a (pr + 1))) (planarNatEmpty n, Array.replicate limit 0)).1

def bumpCounts (addresses : Array Nat) (cells : Array Spec.Vm.Cell) : Array Nat :=
  decodePlanarNat (bumpCountsFlat addresses cells)

theorem bumpCounts_flat_empty : bumpCounts #[] #[] = Spec.Witness.bumpCounts #[] #[] := by
  simp [bumpCounts, bumpCountsFlat, decodePlanarNat, Spec.Witness.bumpCounts,
    planarNatEmpty, foldRange, Model.Pcs.Ntt.foldRangeLoop]

def executeTraceFlat (fuel : Nat) (program : @& Array Spec.Vm.Op)
    (hints : @& Array (Array Spec.Vm.RHint))
    (runtime : Spec.Vm.Runtime) : Except Spec.Vm.Fault ExecutionTrace := do
  let s := runtime.state
  let fs : Model.Vm.Flat.FlatState :=
    ⟨Model.Vm.Flat.flatOf s.memory, s.pc, s.fp, s.nextFree, s.g, s.cycles, s.opcodeCounts⟩
  let (fs', tbls, bc) ← runTraceLoop fuel program hints fs runtime.streams
    (Array.replicate nTables #[]) (Array.replicate program.size 0)
  let mem := Model.Vm.Flat.toMemory fs'.m
  return ⟨tbls, bc, fs'.cycles, mem.used, mem.unconstrainedReads.size, mem, fs'.g⟩

def bundleFlat (program : Array Spec.Vm.Op) (iv : ByteArray) (publicInput : Array E)
    (trace : ExecutionTrace) : WitnessBundle :=
  let sized := Spec.Witness.sizeRun program trace
  let maxC := max (Spec.Witness.maxNatArray trace.bytecodeCount) (Spec.Witness.maxCellAccesses trace.memory)
  let g := Model.Vm.growLinear trace.g (max trace.memUsed (max program.size maxC))
  let hs := sized.layout.taus.map Spec.Witness.pow2
  let qCol := Spec.Witness.fillQKeccak program (trace.tables[5]?.getD #[]) trace.memory (hs[5]?.getD 1)
  let wins := (fillTablesFast program sized g).setIfInBounds qKeccak qCol
  let message := Spec.Witness.stackedMessage sized wins
  let root := Spec.Witness.l0Root message sized.layout.shape
  let pair := Spec.Witness.challengePair iv publicInput sized root
  ⟨sized, message, root, Spec.Witness.announceDigest sized, pair.1, pair.2⟩

def wqBytes (message : @& Array K) : ByteArray :=
  foldRange message.size (fun acc i => pushU64LE acc (message[i]?.getD 0))
    (ByteArray.emptyWithCapacity (8 * message.size))

def bundleWq (bundle : @& WitnessBundle) : ByteArray :=
  wqBytes bundle.message

def pushVec8LE (bytes : ByteArray) (x : Vec8) : ByteArray :=
  let b1 := pushU64LE (pushU64LE (pushU64LE (pushU64LE bytes x.w0) x.w1) x.w2) x.w3
  pushU64LE (pushU64LE (pushU64LE (pushU64LE b1 x.w4) x.w5) x.w6) x.w7

def encodeColWq (tbl : @& Array K) (wq : @& ByteArray)
    (lanes nVecs logRows logInv coset v : Nat) : ByteArray :=
  let rows := 1 <<< logRows
  let w := 8 * nVecs
  let b := 8 * v
  let first := foldRange rows (fun o r =>
    let wd (j : Nat) : K :=
      let col := b + j
      if col + lanes ≥ w then readU64LE wq ((w - 1 - col) * rows + r) else 0
    o.push ⟨wd 0, wd 1, wd 2, wd 3, wd 4, wd 5, wd 6, wd 7⟩) (Array.emptyWithCapacity rows)
  let enc := Model.Pcs.Ntt.encodeCosetVec8 tbl first 1 logRows logInv coset
  foldRange rows (fun acc r => pushVec8LE acc (enc.getD r default))
    (ByteArray.emptyWithCapacity (64 * rows))

def hashLeafCols (st1 st2 st3 : Model.Keccak.State25)
    (b0 b1 b2 b3 b4 b5 b6 b7 : @& ByteArray) (nVecs row : Nat) : Model.Merkle.Digest32 :=
  let i := 8 * row
  let s1 :=
    if nVecs ≤ 5 then st1
    else
      absorbWords17 Model.Layout.zeroState25
        (readU64LE b0 i) (readU64LE b0 (i + 1)) (readU64LE b0 (i + 2)) (readU64LE b0 (i + 3))
        (readU64LE b0 (i + 4)) (readU64LE b0 (i + 5)) (readU64LE b0 (i + 6)) (readU64LE b0 (i + 7))
        (readU64LE b1 i) (readU64LE b1 (i + 1)) (readU64LE b1 (i + 2)) (readU64LE b1 (i + 3))
        (readU64LE b1 (i + 4)) (readU64LE b1 (i + 5)) (readU64LE b1 (i + 6)) (readU64LE b1 (i + 7))
        (readU64LE b2 i)
  let s2 :=
    if nVecs ≤ 3 then st2
    else
      absorbWords17 s1
        (readU64LE b2 (i + 1)) (readU64LE b2 (i + 2)) (readU64LE b2 (i + 3)) (readU64LE b2 (i + 4))
        (readU64LE b2 (i + 5)) (readU64LE b2 (i + 6)) (readU64LE b2 (i + 7))
        (readU64LE b3 i) (readU64LE b3 (i + 1)) (readU64LE b3 (i + 2)) (readU64LE b3 (i + 3))
        (readU64LE b3 (i + 4)) (readU64LE b3 (i + 5)) (readU64LE b3 (i + 6)) (readU64LE b3 (i + 7))
        (readU64LE b4 i) (readU64LE b4 (i + 1))
  let s3 :=
    if nVecs ≤ 1 then st3
    else
      absorbWords17 s2
        (readU64LE b4 (i + 2)) (readU64LE b4 (i + 3)) (readU64LE b4 (i + 4)) (readU64LE b4 (i + 5))
        (readU64LE b4 (i + 6)) (readU64LE b4 (i + 7))
        (readU64LE b5 i) (readU64LE b5 (i + 1)) (readU64LE b5 (i + 2)) (readU64LE b5 (i + 3))
        (readU64LE b5 (i + 4)) (readU64LE b5 (i + 5)) (readU64LE b5 (i + 6)) (readU64LE b5 (i + 7))
        (readU64LE b6 i) (readU64LE b6 (i + 1)) (readU64LE b6 (i + 2))
  absorbFinal13 s3
    (readU64LE b6 (i + 3)) (readU64LE b6 (i + 4)) (readU64LE b6 (i + 5))
    (readU64LE b6 (i + 6)) (readU64LE b6 (i + 7))
    (readU64LE b7 i) (readU64LE b7 (i + 1)) (readU64LE b7 (i + 2)) (readU64LE b7 (i + 3))
    (readU64LE b7 (i + 4)) (readU64LE b7 (i + 5)) (readU64LE b7 (i + 6)) (readU64LE b7 (i + 7))

def subtreeRootCols (st1 st2 st3 : Model.Keccak.State25)
    (b0 b1 b2 b3 b4 b5 b6 b7 : @& ByteArray) (nVecs k : Nat) : Nat → Model.Merkle.Digest32 :=
  Nat.rec (motive := fun _ => Nat → Model.Merkle.Digest32)
    (fun base => hashLeafCols st1 st2 st3 b0 b1 b2 b3 b4 b5 b6 b7 nVecs base)
    (fun k ih base => hashPair25 (ih base) (ih (base + (1 <<< k)))) k

def commitRootWqPar (wq : @& ByteArray) (lanes logRows logInv : Nat) : IO ByteArray := do
  let nVecs := rowWords lanes / 8
  let rate := 1 <<< logInv
  let tbl := Model.Pcs.Ntt.evals (logRows + logInv)
  let cTasks ← (Array.range (rate * nVecs)).mapM fun idx =>
    IO.asTask (prio := .dedicated) <| IO.lazyPure fun () =>
      encodeColWq tbl wq lanes nVecs logRows logInv (idx / nVecs) (idx % nVecs)
  let mut cols : Array ByteArray := Array.emptyWithCapacity (rate * nVecs)
  for t in cTasks do
    match ← IO.wait t with
    | .ok c => cols := cols.push c
    | .error e => throw e
  let st1 := zeroPrefixState 1
  let st2 := zeroPrefixState 2
  let st3 := zeroPrefixState 3
  let z := ByteArray.empty
  let colAt (c pos : Nat) : ByteArray :=
    if pos + nVecs < 8 then z else cols[c * nVecs + (pos + nVecs - 8)]?.getD z
  if logRows < 5 then
    let roots := foldRange rate (fun acc c =>
      acc.push (subtreeRootCols st1 st2 st3
        (colAt c 0) (colAt c 1) (colAt c 2) (colAt c 3)
        (colAt c 4) (colAt c 5) (colAt c 6) (colAt c 7) nVecs logRows 0)) #[]
    return (subtreeRoot (fun i => roots.getD i default) logInv 0).toBytes
  let subK := logRows - 4
  let mTasks ← (Array.range (rate * 16)).mapM fun q => do
    let c := q / 16
    let p := q % 16
    let b0 := colAt c 0
    let b1 := colAt c 1
    let b2 := colAt c 2
    let b3 := colAt c 3
    let b4 := colAt c 4
    let b5 := colAt c 5
    let b6 := colAt c 6
    let b7 := colAt c 7
    IO.asTask (prio := .dedicated) <| IO.lazyPure fun () =>
      subtreeRootCols st1 st2 st3 b0 b1 b2 b3 b4 b5 b6 b7 nVecs subK (p <<< subK)
  let mut ds : Array Model.Merkle.Digest32 := Array.emptyWithCapacity (rate * 16)
  for t in mTasks do
    match ← IO.wait t with
    | .ok d => ds := ds.push d
    | .error e => throw e
  return (subtreeRoot (fun i => ds.getD i default) (logInv + 4) 0).toBytes

def commitRootPar (msg : @& Array K) (lanes logRows logInv : Nat) : IO ByteArray :=
  commitRootWqPar (wqBytes msg) lanes logRows logInv

def stackChunk (sized : @& SizedRun) (wins : @& Array (Array K)) (lo hi : Nat) : Array K :=
  let n := hi - lo
  let placed := foldRange nColumns (fun acc col =>
    if col == qKeccak || (keccakValue col).isSome then acc
    else
      match sized.layout.placements[col]?.join with
      | none => acc
      | some pl =>
        let a := max lo pl.index
        let b := min hi (pl.index + Spec.Witness.pow2 pl.variables)
        let src := wins[col]?.getD #[]
        if a >= b then acc
        else
          foldRange (b - a) (fun m j =>
            m.set! (a + j - lo) (src[a + j - pl.index]?.getD 0)) acc)
    (Array.replicate n 0)
  let qb := (sized.layout.placements[qKeccak]?.join).map Placement.index |>.getD 0
  let qw := wins[qKeccak]?.getD #[]
  let qa := max lo qb
  let qb' := min hi (qb + qw.size)
  let wq :=
    if qa >= qb' then placed
    else foldRange (qb' - qa) (fun m j => m.set! (qa + j - lo) (qw[qa + j - qb]?.getD 0)) placed
  let steps := Spec.Witness.pow2 (sized.layout.taus[opKeccak]?.getD 0)
  foldRange qKeccakSpare (fun m sp =>
    let sb := qb + (qKeccakSlots + sp) * steps
    let sa := max lo sb
    let sb' := min hi (sb + steps)
    let src := wins[tableBase ⟨5, by decide⟩ + spareLocal sp]?.getD #[]
    if sa >= sb' then m
    else foldRange (sb' - sa) (fun m0 j => m0.set! (sa + j - lo) (src[sa + j - sb]?.getD 0)) m) wq

def limbWordOf (limb : Nat) (w : Spec.Field.E) : UInt64 :=
  match limb with
  | 0 => w.c0
  | 1 => w.c1
  | _ => w.c2

def memLimbBytes (cells : @& Array Spec.Vm.Cell) (used : Nat) (limb : Nat) : ByteArray :=
  let buf := Native.Kernels.VmWitness.zeroU64Bulk
    (ByteArray.emptyWithCapacity (8 * used)) 0 (USize.ofNat used)
  foldRange used (fun b i =>
    Native.Kernels.VmWitness.uset64LE b (USize.ofNat i)
      (limbWordOf limb (Model.Vm.cellAt cells i).word)) buf

def colIndexOf (sized : @& SizedRun) (col : Nat) : Nat :=
  match sized.layout.placements[col]?.join with
  | some place => place.index
  | none => 0

def packColAt (wq : ByteArray) (src : @& Array K) (base height tot : Nat) : ByteArray :=
  let n := min (min src.size height) (tot - base)
  Fin.foldl n (fun acc k =>
    Native.Kernels.VmWitness.uset64LE acc (USize.ofNat (base + k.val)) (src[k.val]?.getD 0)) wq

def stackWqK4 (sized : @& SizedRun) (wins : @& Array (Array K))
    (memC0 memC1 memC2 : ByteArray) : ByteArray :=
  let tot := committedLen sized.layout.shape
  let cells := sized.cells
  let used := min cells sized.trace.memory.used
  let buf := Native.Kernels.VmWitness.zeroU64Bulk
    (ByteArray.emptyWithCapacity (8 * tot)) 0 (USize.ofNat tot)
  let loBase := colIndexOf sized memLo
  let hiBase := colIndexOf sized memHi
  let topBase := colIndexOf sized memTop
  let withMem := Native.Kernels.VmWitness.vmMemPackLanes buf memC0 memC1 memC2
    (USize.ofNat used) (USize.ofNat cells) (USize.ofNat loBase) (USize.ofNat hiBase)
    (USize.ofNat topBase)
  let placed := foldRange nColumns (fun wq col =>
    if col == qKeccak || (keccakValue col).isSome || col == memLo || col == memHi || col == memTop
    then wq
    else
      match sized.layout.placements[col]?.join with
      | none => wq
      | some pl =>
        let height := Spec.Witness.pow2 pl.variables
        let src := wins[col]?.getD #[]
        packColAt wq src pl.index height tot) withMem
  let qb := (sized.layout.placements[qKeccak]?.join).map Placement.index |>.getD 0
  let qw := wins[qKeccak]?.getD #[]
  let withQ := packColAt placed qw qb (tot - qb) tot
  let steps := Spec.Witness.pow2 (sized.layout.taus[opKeccak]?.getD 0)
  foldRange qKeccakSpare (fun wq sp =>
    let sb := qb + (qKeccakSlots + sp) * steps
    let src := wins[tableBase ⟨5, by decide⟩ + spareLocal sp]?.getD #[]
    packColAt wq src sb steps tot) withQ

def extractWordsWq (wq : @& ByteArray) (start len : Nat) : Array K :=
  let acc := Array.replicate len 0
  foldRange len (fun a j => a.setIfInBounds j (readU64LE wq (start + j))) acc

def qKeccakWindowWq (sized : @& SizedRun) (wq : @& ByteArray) : ByteArray :=
  let qBase := (sized.layout.placements[qKeccak]?.join).map Placement.index |>.getD 0
  let executed := sized.rows[opKeccak]?.getD 0
  let span := (1 <<< Spec.KeccakGkr.slotBits) * (1 <<< Spec.KeccakGkr.stepsLog executed)
  foldRange span (fun acc i =>
    Model.Layout.pushWordLE acc (readU64LE wq (qBase + i)))
    (ByteArray.emptyWithCapacity (8 * span))

def bundleFlatParallel (program : Array Spec.Vm.Op) (iv : ByteArray) (publicInput : Array E)
    (trace : ExecutionTrace) : IO (WitnessBundle × ByteArray) := do
  let sized := Spec.Witness.sizeRun program trace
  let maxC := max (Spec.Witness.maxNatArray trace.bytecodeCount) (Spec.Witness.maxCellAccesses trace.memory)
  let g := Model.Vm.growLinear trace.g (max trace.memUsed (max program.size maxC))
  let kr := trace.tables[5]?.getD #[]
  let kh := (sized.layout.taus.map Spec.Witness.pow2)[5]?.getD 1
  let gTasks ← (Array.range 7).mapM fun grp =>
    IO.asTask (prio := .dedicated) <| IO.lazyPure fun () => fillTablesGroup grp program sized g
  let qTasks ← (Array.range 16).mapM fun p =>
    IO.asTask (prio := .dedicated) <| IO.lazyPure fun () =>
      fillQKeccakChunk program kr trace.memory (p * kr.size / 16) ((p + 1) * kr.size / 16)
  let mut qChunks := #[]
  for t in qTasks do
    match ← IO.wait t with
    | .ok c => qChunks := qChunks.push c
    | .error e => throw e
  let mut wins := (Array.replicate nColumns #[]).setIfInBounds qKeccak (assembleQKeccak kr.size kh qChunks)
  for t in gTasks do
    let part ← match ← IO.wait t with
      | .ok w => pure w
      | .error e => throw e
    wins := foldRange nColumns (fun a i =>
      let c := part[i]?.getD #[]
      if c.isEmpty then a else a.set! i c) wins
  let tot := committedLen sized.layout.shape
  let sh := sized.layout.shape
  let mTasks ← (Array.range 16).mapM fun p =>
    IO.asTask (prio := .dedicated) <| IO.lazyPure fun () =>
      let lo := p * tot / 16
      let hi := (p + 1) * tot / 16
      let mc := stackChunk sized wins lo hi
      (mc, wqBytes mc)
  let mut mChunks := Array.emptyWithCapacity 16
  for t in mTasks do
    match ← IO.wait t with
    | .ok c => mChunks := mChunks.push c
    | .error e => throw e
  let mut wq := ByteArray.emptyWithCapacity (8 * tot)
  for (_, wc) in mChunks do
    wq := wc.copySlice 0 wq wq.size wc.size false
  let msgTask ← IO.asTask (prio := .dedicated) <| IO.lazyPure fun () => Id.run do
    let mut msg := Array.emptyWithCapacity tot
    for (mc, _) in mChunks do
      msg := foldRange mc.size (fun a j => a.push (mc[j]?.getD 0)) msg
    msg
  let root ← commitRootWqPar wq sh.nLanes (sh.mu - logBatch) logInvRateDefault
  let message ← match ← IO.wait msgTask with
    | .ok m => pure m
    | .error e => throw e
  let pair := Spec.Witness.challengePair iv publicInput sized root
  return (⟨sized, message, root, Spec.Witness.announceDigest sized, pair.1, pair.2⟩, wq)

end LeanVmXmss.Model.Witness
