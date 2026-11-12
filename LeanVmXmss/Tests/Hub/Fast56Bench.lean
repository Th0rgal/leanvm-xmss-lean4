import Model.Pcs.Ntt
import Model.Pcs.Commit
import Model.Pcs.Whir
import Model.Keccak.Simd8
import Model.Pcs.CommitSlab
import Model.Field.NativeKernel

set_option maxHeartbeats 8000000

open LeanVmXmss
open Model.Pcs.Ntt (Vec8 foldRange evals rowFromEvals)
open Model.Merkle (Digest32)
open Model.Keccak.Simd8 (Row5x8 mkFreshRow5x8 copyRow5Into KeccakWs8 mkKeccakWs8 Digests8 xorRow5FromCols setRow5FromCols permuteWs8 extractDigestsWs8)
open Model.Field (nativeMul)

structure Row56 where
  w00 : UInt64 := 0
  w01 : UInt64 := 0
  w02 : UInt64 := 0
  w03 : UInt64 := 0
  w04 : UInt64 := 0
  w05 : UInt64 := 0
  w06 : UInt64 := 0
  w07 : UInt64 := 0
  w08 : UInt64 := 0
  w09 : UInt64 := 0
  w10 : UInt64 := 0
  w11 : UInt64 := 0
  w12 : UInt64 := 0
  w13 : UInt64 := 0
  w14 : UInt64 := 0
  w15 : UInt64 := 0
  w16 : UInt64 := 0
  w17 : UInt64 := 0
  w18 : UInt64 := 0
  w19 : UInt64 := 0
  w20 : UInt64 := 0
  w21 : UInt64 := 0
  w22 : UInt64 := 0
  w23 : UInt64 := 0
  w24 : UInt64 := 0
  w25 : UInt64 := 0
  w26 : UInt64 := 0
  w27 : UInt64 := 0
  w28 : UInt64 := 0
  w29 : UInt64 := 0
  w30 : UInt64 := 0
  w31 : UInt64 := 0
  w32 : UInt64 := 0
  w33 : UInt64 := 0
  w34 : UInt64 := 0
  w35 : UInt64 := 0
  w36 : UInt64 := 0
  w37 : UInt64 := 0
  w38 : UInt64 := 0
  w39 : UInt64 := 0
  w40 : UInt64 := 0
  w41 : UInt64 := 0
  w42 : UInt64 := 0
  w43 : UInt64 := 0
  w44 : UInt64 := 0
  w45 : UInt64 := 0
  w46 : UInt64 := 0
  w47 : UInt64 := 0
  w48 : UInt64 := 0
  w49 : UInt64 := 0
  w50 : UInt64 := 0
  w51 : UInt64 := 0
  w52 : UInt64 := 0
  w53 : UInt64 := 0
  w54 : UInt64 := 0
  w55 : UInt64 := 0
  deriving Inhabited

@[noinline] def mkFreshRow56 (seed : UInt64) : Row56 :=
  { (default : Row56) with w00 := seed ^^^ seed }

def allocUniqueRow56Array (n : Nat) : Array Row56 :=
  let out := Array.emptyWithCapacity n
  Fin.foldl n (fun out i => out.push (mkFreshRow56 (UInt64.ofNat i.val))) out

@[noinline] def copyRow56Into (dst : Row56) (src : @& Row56) : Row56 :=
  { dst with
    w00 := (dst.w00 ^^^ dst.w00) ^^^ src.w00, w01 := src.w01, w02 := src.w02, w03 := src.w03,
    w04 := src.w04, w05 := src.w05, w06 := src.w06, w07 := src.w07,
    w08 := src.w08, w09 := src.w09, w10 := src.w10, w11 := src.w11,
    w12 := src.w12, w13 := src.w13, w14 := src.w14, w15 := src.w15,
    w16 := src.w16, w17 := src.w17, w18 := src.w18, w19 := src.w19,
    w20 := src.w20, w21 := src.w21, w22 := src.w22, w23 := src.w23,
    w24 := src.w24, w25 := src.w25, w26 := src.w26, w27 := src.w27,
    w28 := src.w28, w29 := src.w29, w30 := src.w30, w31 := src.w31,
    w32 := src.w32, w33 := src.w33, w34 := src.w34, w35 := src.w35,
    w36 := src.w36, w37 := src.w37, w38 := src.w38, w39 := src.w39,
    w40 := src.w40, w41 := src.w41, w42 := src.w42, w43 := src.w43,
    w44 := src.w44, w45 := src.w45, w46 := src.w46, w47 := src.w47,
    w48 := src.w48, w49 := src.w49, w50 := src.w50, w51 := src.w51,
    w52 := src.w52, w53 := src.w53, w54 := src.w54, w55 := src.w55 }

@[noinline] def copyRow5IntoBorrowed (src : @& Row5x8) (dst : Row5x8) : Row5x8 :=
  copyRow5Into src dst

def bflyRow56U (top : Row56) (bot : @& Row56) (t : UInt64) : Row56 :=
  if decide (t < 1) then top else
  let z := top.w00 ^^^ top.w00
  { top with
    w00 := z ^^^ top.w00 ^^^ nativeMul bot.w00 t, w01 := top.w01 ^^^ nativeMul bot.w01 t,
    w02 := top.w02 ^^^ nativeMul bot.w02 t, w03 := top.w03 ^^^ nativeMul bot.w03 t,
    w04 := top.w04 ^^^ nativeMul bot.w04 t, w05 := top.w05 ^^^ nativeMul bot.w05 t,
    w06 := top.w06 ^^^ nativeMul bot.w06 t, w07 := top.w07 ^^^ nativeMul bot.w07 t,
    w08 := top.w08 ^^^ nativeMul bot.w08 t, w09 := top.w09 ^^^ nativeMul bot.w09 t,
    w10 := top.w10 ^^^ nativeMul bot.w10 t, w11 := top.w11 ^^^ nativeMul bot.w11 t,
    w12 := top.w12 ^^^ nativeMul bot.w12 t, w13 := top.w13 ^^^ nativeMul bot.w13 t,
    w14 := top.w14 ^^^ nativeMul bot.w14 t, w15 := top.w15 ^^^ nativeMul bot.w15 t,
    w16 := top.w16 ^^^ nativeMul bot.w16 t, w17 := top.w17 ^^^ nativeMul bot.w17 t,
    w18 := top.w18 ^^^ nativeMul bot.w18 t, w19 := top.w19 ^^^ nativeMul bot.w19 t,
    w20 := top.w20 ^^^ nativeMul bot.w20 t, w21 := top.w21 ^^^ nativeMul bot.w21 t,
    w22 := top.w22 ^^^ nativeMul bot.w22 t, w23 := top.w23 ^^^ nativeMul bot.w23 t,
    w24 := top.w24 ^^^ nativeMul bot.w24 t, w25 := top.w25 ^^^ nativeMul bot.w25 t,
    w26 := top.w26 ^^^ nativeMul bot.w26 t, w27 := top.w27 ^^^ nativeMul bot.w27 t,
    w28 := top.w28 ^^^ nativeMul bot.w28 t, w29 := top.w29 ^^^ nativeMul bot.w29 t,
    w30 := top.w30 ^^^ nativeMul bot.w30 t, w31 := top.w31 ^^^ nativeMul bot.w31 t,
    w32 := top.w32 ^^^ nativeMul bot.w32 t, w33 := top.w33 ^^^ nativeMul bot.w33 t,
    w34 := top.w34 ^^^ nativeMul bot.w34 t, w35 := top.w35 ^^^ nativeMul bot.w35 t,
    w36 := top.w36 ^^^ nativeMul bot.w36 t, w37 := top.w37 ^^^ nativeMul bot.w37 t,
    w38 := top.w38 ^^^ nativeMul bot.w38 t, w39 := top.w39 ^^^ nativeMul bot.w39 t,
    w40 := top.w40 ^^^ nativeMul bot.w40 t, w41 := top.w41 ^^^ nativeMul bot.w41 t,
    w42 := top.w42 ^^^ nativeMul bot.w42 t, w43 := top.w43 ^^^ nativeMul bot.w43 t,
    w44 := top.w44 ^^^ nativeMul bot.w44 t, w45 := top.w45 ^^^ nativeMul bot.w45 t,
    w46 := top.w46 ^^^ nativeMul bot.w46 t, w47 := top.w47 ^^^ nativeMul bot.w47 t,
    w48 := top.w48 ^^^ nativeMul bot.w48 t, w49 := top.w49 ^^^ nativeMul bot.w49 t,
    w50 := top.w50 ^^^ nativeMul bot.w50 t, w51 := top.w51 ^^^ nativeMul bot.w51 t,
    w52 := top.w52 ^^^ nativeMul bot.w52 t, w53 := top.w53 ^^^ nativeMul bot.w53 t,
    w54 := top.w54 ^^^ nativeMul bot.w54 t, w55 := top.w55 ^^^ nativeMul bot.w55 t }

def bflyRow56V (bot : Row56) (u : @& Row56) : Row56 :=
  let z := bot.w00 ^^^ bot.w00
  { bot with
    w00 := z ^^^ bot.w00 ^^^ u.w00, w01 := bot.w01 ^^^ u.w01, w02 := bot.w02 ^^^ u.w02, w03 := bot.w03 ^^^ u.w03,
    w04 := bot.w04 ^^^ u.w04, w05 := bot.w05 ^^^ u.w05, w06 := bot.w06 ^^^ u.w06, w07 := bot.w07 ^^^ u.w07,
    w08 := bot.w08 ^^^ u.w08, w09 := bot.w09 ^^^ u.w09, w10 := bot.w10 ^^^ u.w10, w11 := bot.w11 ^^^ u.w11,
    w12 := bot.w12 ^^^ u.w12, w13 := bot.w13 ^^^ u.w13, w14 := bot.w14 ^^^ u.w14, w15 := bot.w15 ^^^ u.w15,
    w16 := bot.w16 ^^^ u.w16, w17 := bot.w17 ^^^ u.w17, w18 := bot.w18 ^^^ u.w18, w19 := bot.w19 ^^^ u.w19,
    w20 := bot.w20 ^^^ u.w20, w21 := bot.w21 ^^^ u.w21, w22 := bot.w22 ^^^ u.w22, w23 := bot.w23 ^^^ u.w23,
    w24 := bot.w24 ^^^ u.w24, w25 := bot.w25 ^^^ u.w25, w26 := bot.w26 ^^^ u.w26, w27 := bot.w27 ^^^ u.w27,
    w28 := bot.w28 ^^^ u.w28, w29 := bot.w29 ^^^ u.w29, w30 := bot.w30 ^^^ u.w30, w31 := bot.w31 ^^^ u.w31,
    w32 := bot.w32 ^^^ u.w32, w33 := bot.w33 ^^^ u.w33, w34 := bot.w34 ^^^ u.w34, w35 := bot.w35 ^^^ u.w35,
    w36 := bot.w36 ^^^ u.w36, w37 := bot.w37 ^^^ u.w37, w38 := bot.w38 ^^^ u.w38, w39 := bot.w39 ^^^ u.w39,
    w40 := bot.w40 ^^^ u.w40, w41 := bot.w41 ^^^ u.w41, w42 := bot.w42 ^^^ u.w42, w43 := bot.w43 ^^^ u.w43,
    w44 := bot.w44 ^^^ u.w44, w45 := bot.w45 ^^^ u.w45, w46 := bot.w46 ^^^ u.w46, w47 := bot.w47 ^^^ u.w47,
    w48 := bot.w48 ^^^ u.w48, w49 := bot.w49 ^^^ u.w49, w50 := bot.w50 ^^^ u.w50, w51 := bot.w51 ^^^ u.w51,
    w52 := bot.w52 ^^^ u.w52, w53 := bot.w53 ^^^ u.w53, w54 := bot.w54 ^^^ u.w54, w55 := bot.w55 ^^^ u.w55 }

/-- Fast 256-entry byte subset-sum twiddle table (matches Rust `AdditiveNttF64`):
    `byteTabs` has `logD * 768` `UInt64`s (`3 × 256` per eval row), `rows` stores `rowFromEvals`. -/
structure ByteTwiddles where
  logD : Nat
  rows : Array (Array UInt64)
  byteTabs : Array UInt64
  deriving Inhabited

def spanGetSlice (basis : Array UInt64) (off len idx : Nat) : UInt64 :=
  Fin.foldl len (fun acc j =>
    if decide (((idx >>> j.val) &&& 1) = 1) then
      acc ^^^ basis.getD (off + j.val) 0
    else acc) 0

def mkByteTwiddles (logD : Nat) : ByteTwiddles :=
  let table := evals logD
  let rows := (Array.range logD).map fun r => rowFromEvals table logD r
  let byteTabsInit := Array.emptyWithCapacity (logD * 768)
  let byteTabs :=
    Fin.foldl logD (fun acc r =>
      let row := rows.getD r.val #[]
      let basisLen := if row.size > 0 then row.size - 1 else 0
      Fin.foldl 3 (fun acc k =>
        let subStart := min (8 * k.val) basisLen
        let subEnd := min (8 * k.val + 8) basisLen
        let subLen := subEnd - subStart
        Fin.foldl 256 (fun acc x =>
          acc.push (spanGetSlice row (1 + subStart) subLen x.val)) acc) acc) byteTabsInit
  ⟨logD, rows, byteTabs⟩

@[inline] def ByteTwiddles.twiddle (bt : ByteTwiddles) (layer block : Nat) : UInt64 :=
  let rowIdx := bt.logD - layer - 1
  if decide (block < (1 <<< 24)) then
    let base := rowIdx * 768
    let b0 := bt.byteTabs.getD (base + (block &&& 255)) 0
    let b1 := bt.byteTabs.getD (base + 256 + ((block >>> 8) &&& 255)) 0
    let b2 := bt.byteTabs.getD (base + 512 + ((block >>> 16) &&& 255)) 0
    b0 ^^^ b1 ^^^ b2
  else
    let row := bt.rows.getD rowIdx #[]
    spanGetSlice row 1 (row.size - 1) block

@[inline] def bflyAt (arr : Array Row56) (i0 i1 : Nat) (t : UInt64) : Array Row56 :=
  if h : i0 < arr.size ∧ i1 < arr.size then
    let r0 := arr[i0]'h.1
    let r1 := arr[i1]'h.2
    let arr1 := arr.set i0 default h.1
    let arr2 := arr1.set i1 default (by simpa [arr1] using h.2)
    let u0 := bflyRow56U r0 r1 t
    let v1 := bflyRow56V r1 u0
    let arr3 := arr2.set i0 u0 (by simpa [arr2, arr1] using h.1)
    arr3.set i1 v1 (by simpa [arr3, arr2, arr1] using h.2)
  else arr

def sweepRadix2 (arr : Array Row56) (bt : @& ByteTwiddles) (layer logBlocks half gb0 : Nat) : Array Row56 :=
  let nBlocks := 1 <<< logBlocks
  Fin.foldl nBlocks (fun arr lb =>
    let t := bt.twiddle layer (gb0 + lb.val)
    let rowBase := lb.val * (2 * half)
    Fin.foldl half (fun arr r =>
      let i0 := rowBase + r.val
      bflyAt arr i0 (i0 + half) t) arr) arr

def sweepRadix4 (arr : Array Row56) (bt : @& ByteTwiddles) (layer logBlocks quarter gb0 : Nat) : Array Row56 :=
  let nBlocks := 1 <<< logBlocks
  let v1 := bt.rows.getD (bt.logD - layer - 2) #[]
  let d := v1.getD 1 0
  Fin.foldl nBlocks (fun arr lb =>
    let gb := gb0 + lb.val
    let t0 := bt.twiddle layer gb
    let t10 := bt.twiddle (layer + 1) (2 * gb)
    let t11 := t10 ^^^ d
    let base := lb.val * (4 * quarter)
    Fin.foldl quarter (fun arr r =>
      let j0 := base + r.val
      let j1 := j0 + quarter
      let j2 := j0 + 2 * quarter
      let j3 := j0 + 3 * quarter
      let arr := bflyAt arr j0 j2 t0
      let arr := bflyAt arr j1 j3 t0
      let arr := bflyAt arr j0 j1 t10
      bflyAt arr j2 j3 t11) arr) arr

def sweepRadix8 (arr : Array Row56) (bt : @& ByteTwiddles) (layer logBlocks eighth gb0 : Nat) : Array Row56 :=
  let nBlocks := 1 <<< logBlocks
  let v1 := bt.rows.getD (bt.logD - layer - 2) #[]
  let v2 := bt.rows.getD (bt.logD - layer - 3) #[]
  let d := v1.getD 1 0
  let e0 := v2.getD 1 0
  let e1 := v2.getD 2 0
  Fin.foldl nBlocks (fun arr lb =>
    let gb := gb0 + lb.val
    let t0 := bt.twiddle layer gb
    let a := bt.twiddle (layer + 1) (2 * gb)
    let c := bt.twiddle (layer + 2) (4 * gb)
    let t10 := a
    let t11 := a ^^^ d
    let t20 := c
    let t21 := c ^^^ e0
    let t22 := c ^^^ e1
    let t23 := t21 ^^^ e1
    let base := lb.val * (8 * eighth)
    Fin.foldl eighth (fun arr r =>
      let j0 := base + r.val
      let j1 := j0 + eighth
      let j2 := j0 + 2 * eighth
      let j3 := j0 + 3 * eighth
      let j4 := j0 + 4 * eighth
      let j5 := j0 + 5 * eighth
      let j6 := j0 + 6 * eighth
      let j7 := j0 + 7 * eighth
      let arr := bflyAt arr j0 j4 t0
      let arr := bflyAt arr j1 j5 t0
      let arr := bflyAt arr j2 j6 t0
      let arr := bflyAt arr j3 j7 t0
      let arr := bflyAt arr j0 j2 t10
      let arr := bflyAt arr j1 j3 t10
      let arr := bflyAt arr j4 j6 t11
      let arr := bflyAt arr j5 j7 t11
      let arr := bflyAt arr j0 j1 t20
      let arr := bflyAt arr j2 j3 t21
      let arr := bflyAt arr j4 j5 t22
      bflyAt arr j6 j7 t23) arr) arr

def runFused (bt : @& ByteTwiddles) (firstLayer endLayer outerLog subIdx : Nat) (arr : Array Row56) : Array Row56 :=
  let rec go (layer fuel : Nat) (arr : Array Row56) : Array Row56 :=
    match fuel with
    | 0 => arr
    | fuel + 1 =>
      if decide (layer ≥ endLayer) then arr else
      let left := endLayer - layer
      let localLog := layer - outerLog
      let gb0 := subIdx <<< localLog
      if decide (left ≥ 4 ∧ left % 3 = 1) then
        let quarter := 1 <<< (left - 2)
        go (layer + 2) fuel (sweepRadix4 arr bt layer localLog quarter gb0)
      else if decide (left ≥ 3) then
        let eighth := 1 <<< (left - 3)
        go (layer + 3) fuel (sweepRadix8 arr bt layer localLog eighth gb0)
      else if decide (left = 2) then
        let quarter := 1 <<< (left - 2)
        go (layer + 2) fuel (sweepRadix4 arr bt layer localLog quarter gb0)
      else
        let half := 1 <<< (left - 1)
        go (layer + 1) fuel (sweepRadix2 arr bt layer localLog half gb0)
  go firstLayer (endLayer - firstLayer + 1) arr

/-- Write one residue row into an existing `Row56` slot (`dst` kept live so Lean reuses the ctor). -/
def fillOneResidueRow56 (msg : @& Array UInt64) (rows baseRow : Nat) (s : Nat) (dst : Row56) : Row56 :=
  let off := baseRow + s
  let z := dst.w00 ^^^ dst.w00
  if h : 50 * rows + off < msg.size then
    { dst with
      w00 := z, w01 := z, w02 := z, w03 := z, w04 := z,
      w05 := msg[50 * rows + off]'(by omega), w06 := msg[49 * rows + off]'(by omega),
      w07 := msg[48 * rows + off]'(by omega), w08 := msg[47 * rows + off]'(by omega),
      w09 := msg[46 * rows + off]'(by omega), w10 := msg[45 * rows + off]'(by omega),
      w11 := msg[44 * rows + off]'(by omega), w12 := msg[43 * rows + off]'(by omega),
      w13 := msg[42 * rows + off]'(by omega), w14 := msg[41 * rows + off]'(by omega),
      w15 := msg[40 * rows + off]'(by omega), w16 := msg[39 * rows + off]'(by omega),
      w17 := msg[38 * rows + off]'(by omega), w18 := msg[37 * rows + off]'(by omega),
      w19 := msg[36 * rows + off]'(by omega), w20 := msg[35 * rows + off]'(by omega),
      w21 := msg[34 * rows + off]'(by omega), w22 := msg[33 * rows + off]'(by omega),
      w23 := msg[32 * rows + off]'(by omega), w24 := msg[31 * rows + off]'(by omega),
      w25 := msg[30 * rows + off]'(by omega), w26 := msg[29 * rows + off]'(by omega),
      w27 := msg[28 * rows + off]'(by omega), w28 := msg[27 * rows + off]'(by omega),
      w29 := msg[26 * rows + off]'(by omega), w30 := msg[25 * rows + off]'(by omega),
      w31 := msg[24 * rows + off]'(by omega), w32 := msg[23 * rows + off]'(by omega),
      w33 := msg[22 * rows + off]'(by omega), w34 := msg[21 * rows + off]'(by omega),
      w35 := msg[20 * rows + off]'(by omega), w36 := msg[19 * rows + off]'(by omega),
      w37 := msg[18 * rows + off]'(by omega), w38 := msg[17 * rows + off]'(by omega),
      w39 := msg[16 * rows + off]'(by omega), w40 := msg[15 * rows + off]'(by omega),
      w41 := msg[14 * rows + off]'(by omega), w42 := msg[13 * rows + off]'(by omega),
      w43 := msg[12 * rows + off]'(by omega), w44 := msg[11 * rows + off]'(by omega),
      w45 := msg[10 * rows + off]'(by omega), w46 := msg[9 * rows + off]'(by omega),
      w47 := msg[8 * rows + off]'(by omega),  w48 := msg[7 * rows + off]'(by omega),
      w49 := msg[6 * rows + off]'(by omega),  w50 := msg[5 * rows + off]'(by omega),
      w51 := msg[4 * rows + off]'(by omega),  w52 := msg[3 * rows + off]'(by omega),
      w53 := msg[2 * rows + off]'(by omega),  w54 := msg[1 * rows + off]'(by omega),
      w55 := msg[off]'(by omega) }
  else
    { dst with
      w00 := z, w01 := z, w02 := z, w03 := z, w04 := z,
      w05 := msg.getD (50 * rows + off) 0, w06 := msg.getD (49 * rows + off) 0,
      w07 := msg.getD (48 * rows + off) 0, w08 := msg.getD (47 * rows + off) 0,
      w09 := msg.getD (46 * rows + off) 0, w10 := msg.getD (45 * rows + off) 0,
      w11 := msg.getD (44 * rows + off) 0, w12 := msg.getD (43 * rows + off) 0,
      w13 := msg.getD (42 * rows + off) 0, w14 := msg.getD (41 * rows + off) 0,
      w15 := msg.getD (40 * rows + off) 0, w16 := msg.getD (39 * rows + off) 0,
      w17 := msg.getD (38 * rows + off) 0, w18 := msg.getD (37 * rows + off) 0,
      w19 := msg.getD (36 * rows + off) 0, w20 := msg.getD (35 * rows + off) 0,
      w21 := msg.getD (34 * rows + off) 0, w22 := msg.getD (33 * rows + off) 0,
      w23 := msg.getD (32 * rows + off) 0, w24 := msg.getD (31 * rows + off) 0,
      w25 := msg.getD (30 * rows + off) 0, w26 := msg.getD (29 * rows + off) 0,
      w27 := msg.getD (28 * rows + off) 0, w28 := msg.getD (27 * rows + off) 0,
      w29 := msg.getD (26 * rows + off) 0, w30 := msg.getD (25 * rows + off) 0,
      w31 := msg.getD (24 * rows + off) 0, w32 := msg.getD (23 * rows + off) 0,
      w33 := msg.getD (22 * rows + off) 0, w34 := msg.getD (21 * rows + off) 0,
      w35 := msg.getD (20 * rows + off) 0, w36 := msg.getD (19 * rows + off) 0,
      w37 := msg.getD (18 * rows + off) 0, w38 := msg.getD (17 * rows + off) 0,
      w39 := msg.getD (16 * rows + off) 0, w40 := msg.getD (15 * rows + off) 0,
      w41 := msg.getD (14 * rows + off) 0, w42 := msg.getD (13 * rows + off) 0,
      w43 := msg.getD (12 * rows + off) 0, w44 := msg.getD (11 * rows + off) 0,
      w45 := msg.getD (10 * rows + off) 0, w46 := msg.getD (9 * rows + off) 0,
      w47 := msg.getD (8 * rows + off) 0,  w48 := msg.getD (7 * rows + off) 0,
      w49 := msg.getD (6 * rows + off) 0,  w50 := msg.getD (5 * rows + off) 0,
      w51 := msg.getD (4 * rows + off) 0,  w52 := msg.getD (3 * rows + off) 0,
      w53 := msg.getD (2 * rows + off) 0,  w54 := msg.getD (1 * rows + off) 0,
      w55 := msg.getD off 0 }

def fill8ResiduesRow56 (msg : @& Array UInt64) (rows baseRow groupRows i : Nat) (grpTile : Array Row56) : Array Row56 :=
  Fin.foldl 8 (fun grpTile s =>
    let idx := s.val * groupRows + i
    if h : idx < grpTile.size then
      let dst := grpTile[idx]'h
      let grpTile1 := grpTile.set idx default h
      let v := fillOneResidueRow56 msg rows baseRow s.val dst
      grpTile1.set idx v (by simpa [grpTile1] using h)
    else grpTile) grpTile

structure GatherWs where
  workerId : Nat
  grpTile : Array Row56
  sc : Array Row56
  out : Array Row56

/-- Gather coset `coset` (`0` or `1`) into preallocated `out` (`groupRows * resCount` rows),
    reusing `grpTile`, `sc`, and `out` in-place with ZERO allocations! -/
def runGatheredShardCoset (msg : @& Array UInt64) (bt : @& ByteTwiddles)
    (logRows logInvRate g coset resLo resCount : Nat) (ws : GatherWs) : GatherWs :=
  let rows := 1 <<< logRows
  let groupRows := 1 <<< g
  let step := 1 <<< (logRows - g)
  let tiles := resCount >>> 3
  let endLayer := logInvRate + g
  Fin.foldl tiles (fun (ws : GatherWs) b =>
    let ⟨wId, grpTile, sc, out⟩ := ws
    let rBase := resLo + b.val * 8
    let grpTile :=
      Fin.foldl groupRows (fun grpTile i =>
        fill8ResiduesRow56 msg rows (rBase + i.val * step) groupRows i.val grpTile) grpTile
    let (sc, out) :=
      Fin.foldl 8 (fun (p : Array Row56 × Array Row56) s =>
        let sc := p.1
        let out := p.2
        let rOff := b.val * 8 + s.val
        let srcOff := s.val * groupRows
        let sc :=
          Fin.foldl groupRows (fun sc i =>
            if h : i.val < sc.size ∧ srcOff + i.val < grpTile.size then
              let dstV := sc[i.val]'h.1
              let sc1 := sc.set i.val default h.1
              let srcV := grpTile[srcOff + i.val]'h.2
              let newV := copyRow56Into dstV srcV
              sc1.set i.val newV (by simpa [sc1] using h.1)
            else sc) sc
        let sc := runFused bt logInvRate endLayer logInvRate coset sc
        Fin.foldl groupRows (fun (p : Array Row56 × Array Row56) i =>
          let sc := p.1
          let out := p.2
          let dstIdx := i.val * resCount + rOff
          if h : i.val < sc.size ∧ dstIdx < out.size then
            let scV := sc[i.val]'h.1
            let outV := out[dstIdx]'h.2
            let sc1 := sc.set i.val outV h.1
            let out1 := out.set dstIdx scV h.2
            (sc1, out1)
          else (sc, out)) (sc, out)) (sc, out)
    ⟨wId, grpTile, sc, out⟩) ws

/-- Reusable per-worker workspace for zero-allocation 64-leaf -> level-3 Merkle compression. -/
structure Leaf64Ws where
  kws : KeccakWs8
  s0 : Row5x8
  s1 : Row5x8
  s2 : Row5x8
  deriving Inhabited

@[noinline] def mkLeaf64Ws (seed : Nat := 0) : Leaf64Ws :=
  let s := UInt64.ofNat (seed * 32 + 100)
  ⟨mkKeccakWs8 seed, mkFreshRow5x8 s, mkFreshRow5x8 (s + 1), mkFreshRow5x8 (s + 2)⟩

structure DeepWs where
  workerId : Nat
  slab : Array Row56
  lws : Leaf64Ws

def hash8Rows56WsOnly (ws : KeccakWs8) (r0 r1 r2 r3 r4 r5 r6 r7 : @& Row56) : KeccakWs8 :=
  let ws :=
    { ws with
      r0 := setRow5FromCols ws.r0
        0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0,
      r1 := setRow5FromCols ws.r1
        0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0
        r0.w00 r1.w00 r2.w00 r3.w00 r4.w00 r5.w00 r6.w00 r7.w00
        r0.w01 r1.w01 r2.w01 r3.w01 r4.w01 r5.w01 r6.w01 r7.w01,
      r2 := setRow5FromCols ws.r2
        r0.w02 r1.w02 r2.w02 r3.w02 r4.w02 r5.w02 r6.w02 r7.w02
        r0.w03 r1.w03 r2.w03 r3.w03 r4.w03 r5.w03 r6.w03 r7.w03
        r0.w04 r1.w04 r2.w04 r3.w04 r4.w04 r5.w04 r6.w04 r7.w04
        r0.w05 r1.w05 r2.w05 r3.w05 r4.w05 r5.w05 r6.w05 r7.w05
        r0.w06 r1.w06 r2.w06 r3.w06 r4.w06 r5.w06 r6.w06 r7.w06,
      r3 := setRow5FromCols ws.r3
        r0.w07 r1.w07 r2.w07 r3.w07 r4.w07 r5.w07 r6.w07 r7.w07
        r0.w08 r1.w08 r2.w08 r3.w08 r4.w08 r5.w08 r6.w08 r7.w08
        0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0,
      r4 := setRow5FromCols ws.r4
        0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0 }
  let ws := permuteWs8 ws
  let ws :=
    { ws with
      r0 := xorRow5FromCols ws.r0
        r0.w09 r1.w09 r2.w09 r3.w09 r4.w09 r5.w09 r6.w09 r7.w09
        r0.w10 r1.w10 r2.w10 r3.w10 r4.w10 r5.w10 r6.w10 r7.w10
        r0.w11 r1.w11 r2.w11 r3.w11 r4.w11 r5.w11 r6.w11 r7.w11
        r0.w12 r1.w12 r2.w12 r3.w12 r4.w12 r5.w12 r6.w12 r7.w12
        r0.w13 r1.w13 r2.w13 r3.w13 r4.w13 r5.w13 r6.w13 r7.w13,
      r1 := xorRow5FromCols ws.r1
        r0.w14 r1.w14 r2.w14 r3.w14 r4.w14 r5.w14 r6.w14 r7.w14
        r0.w15 r1.w15 r2.w15 r3.w15 r4.w15 r5.w15 r6.w15 r7.w15
        r0.w16 r1.w16 r2.w16 r3.w16 r4.w16 r5.w16 r6.w16 r7.w16
        r0.w17 r1.w17 r2.w17 r3.w17 r4.w17 r5.w17 r6.w17 r7.w17
        r0.w18 r1.w18 r2.w18 r3.w18 r4.w18 r5.w18 r6.w18 r7.w18,
      r2 := xorRow5FromCols ws.r2
        r0.w19 r1.w19 r2.w19 r3.w19 r4.w19 r5.w19 r6.w19 r7.w19
        r0.w20 r1.w20 r2.w20 r3.w20 r4.w20 r5.w20 r6.w20 r7.w20
        r0.w21 r1.w21 r2.w21 r3.w21 r4.w21 r5.w21 r6.w21 r7.w21
        r0.w22 r1.w22 r2.w22 r3.w22 r4.w22 r5.w22 r6.w22 r7.w22
        r0.w23 r1.w23 r2.w23 r3.w23 r4.w23 r5.w23 r6.w23 r7.w23,
      r3 := xorRow5FromCols ws.r3
        r0.w24 r1.w24 r2.w24 r3.w24 r4.w24 r5.w24 r6.w24 r7.w24
        r0.w25 r1.w25 r2.w25 r3.w25 r4.w25 r5.w25 r6.w25 r7.w25
        0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0 }
  let ws := permuteWs8 ws
  let ws :=
    { ws with
      r0 := xorRow5FromCols ws.r0
        r0.w26 r1.w26 r2.w26 r3.w26 r4.w26 r5.w26 r6.w26 r7.w26
        r0.w27 r1.w27 r2.w27 r3.w27 r4.w27 r5.w27 r6.w27 r7.w27
        r0.w28 r1.w28 r2.w28 r3.w28 r4.w28 r5.w28 r6.w28 r7.w28
        r0.w29 r1.w29 r2.w29 r3.w29 r4.w29 r5.w29 r6.w29 r7.w29
        r0.w30 r1.w30 r2.w30 r3.w30 r4.w30 r5.w30 r6.w30 r7.w30,
      r1 := xorRow5FromCols ws.r1
        r0.w31 r1.w31 r2.w31 r3.w31 r4.w31 r5.w31 r6.w31 r7.w31
        r0.w32 r1.w32 r2.w32 r3.w32 r4.w32 r5.w32 r6.w32 r7.w32
        r0.w33 r1.w33 r2.w33 r3.w33 r4.w33 r5.w33 r6.w33 r7.w33
        r0.w34 r1.w34 r2.w34 r3.w34 r4.w34 r5.w34 r6.w34 r7.w34
        r0.w35 r1.w35 r2.w35 r3.w35 r4.w35 r5.w35 r6.w35 r7.w35,
      r2 := xorRow5FromCols ws.r2
        r0.w36 r1.w36 r2.w36 r3.w36 r4.w36 r5.w36 r6.w36 r7.w36
        r0.w37 r1.w37 r2.w37 r3.w37 r4.w37 r5.w37 r6.w37 r7.w37
        r0.w38 r1.w38 r2.w38 r3.w38 r4.w38 r5.w38 r6.w38 r7.w38
        r0.w39 r1.w39 r2.w39 r3.w39 r4.w39 r5.w39 r6.w39 r7.w39
        r0.w40 r1.w40 r2.w40 r3.w40 r4.w40 r5.w40 r6.w40 r7.w40,
      r3 := xorRow5FromCols ws.r3
        r0.w41 r1.w41 r2.w41 r3.w41 r4.w41 r5.w41 r6.w41 r7.w41
        r0.w42 r1.w42 r2.w42 r3.w42 r4.w42 r5.w42 r6.w42 r7.w42
        0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0 }
  let ws := permuteWs8 ws
  let ws :=
    { ws with
      r0 := xorRow5FromCols ws.r0
        r0.w43 r1.w43 r2.w43 r3.w43 r4.w43 r5.w43 r6.w43 r7.w43
        r0.w44 r1.w44 r2.w44 r3.w44 r4.w44 r5.w44 r6.w44 r7.w44
        r0.w45 r1.w45 r2.w45 r3.w45 r4.w45 r5.w45 r6.w45 r7.w45
        r0.w46 r1.w46 r2.w46 r3.w46 r4.w46 r5.w46 r6.w46 r7.w46
        r0.w47 r1.w47 r2.w47 r3.w47 r4.w47 r5.w47 r6.w47 r7.w47,
      r1 := xorRow5FromCols ws.r1
        r0.w48 r1.w48 r2.w48 r3.w48 r4.w48 r5.w48 r6.w48 r7.w48
        r0.w49 r1.w49 r2.w49 r3.w49 r4.w49 r5.w49 r6.w49 r7.w49
        r0.w50 r1.w50 r2.w50 r3.w50 r4.w50 r5.w50 r6.w50 r7.w50
        r0.w51 r1.w51 r2.w51 r3.w51 r4.w51 r5.w51 r6.w51 r7.w51
        r0.w52 r1.w52 r2.w52 r3.w52 r4.w52 r5.w52 r6.w52 r7.w52,
      r2 := xorRow5FromCols ws.r2
        r0.w53 r1.w53 r2.w53 r3.w53 r4.w53 r5.w53 r6.w53 r7.w53
        r0.w54 r1.w54 r2.w54 r3.w54 r4.w54 r5.w54 r6.w54 r7.w54
        r0.w55 r1.w55 r2.w55 r3.w55 r4.w55 r5.w55 r6.w55 r7.w55
        1 1 1 1 1 1 1 1
        0 0 0 0 0 0 0 0,
      r3 := xorRow5FromCols ws.r3
        0 0 0 0 0 0 0 0
        0x8000000000000000 0x8000000000000000 0x8000000000000000 0x8000000000000000 0x8000000000000000 0x8000000000000000 0x8000000000000000 0x8000000000000000
        0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0 }
  permuteWs8 ws

/-- Compress two 8-digest `Row5x8` states (`a` = 8 digests `a[0..7]`, `b` = 8 digests `b[0..7]`)
    as consecutive sibling pairs `(a0,a1), (a2,a3), (a4,a5), (a6,a7), (b0,b1), (b2,b3), (b4,b5), (b6,b7)`
    directly in unboxed `Row5x8`s with ZERO `Digest32` heap allocations! -/
@[noinline] def hashConsecPairsRow5Ws (ws : KeccakWs8) (a b : @& Row5x8) : KeccakWs8 :=
  let top := (0x8000000000000000 : UInt64)
  let ws :=
    { ws with
      r0 := setRow5FromCols ws.r0
        a.a0_0 a.a0_2 a.a0_4 a.a0_6 b.a0_0 b.a0_2 b.a0_4 b.a0_6
        a.a1_0 a.a1_2 a.a1_4 a.a1_6 b.a1_0 b.a1_2 b.a1_4 b.a1_6
        a.a2_0 a.a2_2 a.a2_4 a.a2_6 b.a2_0 b.a2_2 b.a2_4 b.a2_6
        a.a3_0 a.a3_2 a.a3_4 a.a3_6 b.a3_0 b.a3_2 b.a3_4 b.a3_6
        a.a0_1 a.a0_3 a.a0_5 a.a0_7 b.a0_1 b.a0_3 b.a0_5 b.a0_7,
      r1 := setRow5FromCols ws.r1
        a.a1_1 a.a1_3 a.a1_5 a.a1_7 b.a1_1 b.a1_3 b.a1_5 b.a1_7
        a.a2_1 a.a2_3 a.a2_5 a.a2_7 b.a2_1 b.a2_3 b.a2_5 b.a2_7
        a.a3_1 a.a3_3 a.a3_5 a.a3_7 b.a3_1 b.a3_3 b.a3_5 b.a3_7
        1 1 1 1 1 1 1 1
        0 0 0 0 0 0 0 0,
      r2 := setRow5FromCols ws.r2
        0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0,
      r3 := setRow5FromCols ws.r3
        0 0 0 0 0 0 0 0
        top top top top top top top top
        0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0,
      r4 := setRow5FromCols ws.r4
        0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0
        0 0 0 0 0 0 0 0 }
  permuteWs8 ws

def hash64LeavesToLvl3Ws (lws : Leaf64Ws) (slab : @& Array Row56) (base64 : Nat)
    : Digests8 × Leaf64Ws :=
  let ⟨ws, s0, s1, s2⟩ := lws
  if h : base64 + 64 ≤ slab.size then
    let ws := hash8Rows56WsOnly ws
      (slab[base64 + 0]'(by omega)) (slab[base64 + 1]'(by omega)) (slab[base64 + 2]'(by omega)) (slab[base64 + 3]'(by omega))
      (slab[base64 + 4]'(by omega)) (slab[base64 + 5]'(by omega)) (slab[base64 + 6]'(by omega)) (slab[base64 + 7]'(by omega))
    let s0 := copyRow5IntoBorrowed ws.r0 s0
    let ws := hash8Rows56WsOnly ws
      (slab[base64 + 8]'(by omega))  (slab[base64 + 9]'(by omega))  (slab[base64 + 10]'(by omega)) (slab[base64 + 11]'(by omega))
      (slab[base64 + 12]'(by omega)) (slab[base64 + 13]'(by omega)) (slab[base64 + 14]'(by omega)) (slab[base64 + 15]'(by omega))
    let ws := hashConsecPairsRow5Ws ws s0 ws.r0
    let s0 := copyRow5IntoBorrowed ws.r0 s0
    let ws := hash8Rows56WsOnly ws
      (slab[base64 + 16]'(by omega)) (slab[base64 + 17]'(by omega)) (slab[base64 + 18]'(by omega)) (slab[base64 + 19]'(by omega))
      (slab[base64 + 20]'(by omega)) (slab[base64 + 21]'(by omega)) (slab[base64 + 22]'(by omega)) (slab[base64 + 23]'(by omega))
    let s1 := copyRow5IntoBorrowed ws.r0 s1
    let ws := hash8Rows56WsOnly ws
      (slab[base64 + 24]'(by omega)) (slab[base64 + 25]'(by omega)) (slab[base64 + 26]'(by omega)) (slab[base64 + 27]'(by omega))
      (slab[base64 + 28]'(by omega)) (slab[base64 + 29]'(by omega)) (slab[base64 + 30]'(by omega)) (slab[base64 + 31]'(by omega))
    let ws := hashConsecPairsRow5Ws ws s1 ws.r0
    let ws := hashConsecPairsRow5Ws ws s0 ws.r0
    let s0 := copyRow5IntoBorrowed ws.r0 s0
    let ws := hash8Rows56WsOnly ws
      (slab[base64 + 32]'(by omega)) (slab[base64 + 33]'(by omega)) (slab[base64 + 34]'(by omega)) (slab[base64 + 35]'(by omega))
      (slab[base64 + 36]'(by omega)) (slab[base64 + 37]'(by omega)) (slab[base64 + 38]'(by omega)) (slab[base64 + 39]'(by omega))
    let s1 := copyRow5IntoBorrowed ws.r0 s1
    let ws := hash8Rows56WsOnly ws
      (slab[base64 + 40]'(by omega)) (slab[base64 + 41]'(by omega)) (slab[base64 + 42]'(by omega)) (slab[base64 + 43]'(by omega))
      (slab[base64 + 44]'(by omega)) (slab[base64 + 45]'(by omega)) (slab[base64 + 46]'(by omega)) (slab[base64 + 47]'(by omega))
    let ws := hashConsecPairsRow5Ws ws s1 ws.r0
    let s1 := copyRow5IntoBorrowed ws.r0 s1
    let ws := hash8Rows56WsOnly ws
      (slab[base64 + 48]'(by omega)) (slab[base64 + 49]'(by omega)) (slab[base64 + 50]'(by omega)) (slab[base64 + 51]'(by omega))
      (slab[base64 + 52]'(by omega)) (slab[base64 + 53]'(by omega)) (slab[base64 + 54]'(by omega)) (slab[base64 + 55]'(by omega))
    let s2 := copyRow5IntoBorrowed ws.r0 s2
    let ws := hash8Rows56WsOnly ws
      (slab[base64 + 56]'(by omega)) (slab[base64 + 57]'(by omega)) (slab[base64 + 58]'(by omega)) (slab[base64 + 59]'(by omega))
      (slab[base64 + 60]'(by omega)) (slab[base64 + 61]'(by omega)) (slab[base64 + 62]'(by omega)) (slab[base64 + 63]'(by omega))
    let ws := hashConsecPairsRow5Ws ws s2 ws.r0
    let ws := hashConsecPairsRow5Ws ws s1 ws.r0
    let ws := hashConsecPairsRow5Ws ws s0 ws.r0
    (extractDigestsWs8 ws, ⟨ws, s0, s1, s2⟩)
  else
    (default, ⟨ws, s0, s1, s2⟩)

/-- Assemble coset-local sub-block `localSubIdx` (`0 .. groupRows - 1`) from `shards` (`nWorkers` half-coset shards),
    run deep NTT at global `subIdx = coset * groupRows + localSubIdx`, and hash 64-leaf micro-subtrees to level 3! -/
def deepAndHashLvl3CosetSub (shards : @& Array (Array Row56)) (resPerShard : Nat)
    (bt : @& ByteTwiddles) (deepStart subLog localSubIdx globalSubIdx : Nat)
    (slab : Array Row56) (lws : Leaf64Ws) : Array Row56 × Array (Array Digest32) × Digest32 × Leaf64Ws :=
  let subRows := 1 <<< subLog
  let (_, slab) :=
    Fin.foldl shards.size (fun (p : Nat × Array Row56) shIdx =>
      let dstOff := p.1
      let slab := p.2
      let sh := shards[shIdx.val]!
      let rCnt := min resPerShard (subRows - dstOff)
      let srcBase := localSubIdx * resPerShard
      let slab := Fin.foldl rCnt (fun slab r =>
        let dstIdx := dstOff + r.val
        let srcIdx := srcBase + r.val
        if h : dstIdx < slab.size ∧ srcIdx < sh.size then
          let dstV := slab[dstIdx]'h.1
          let slab1 := slab.set dstIdx default h.1
          let srcV := sh[srcIdx]'h.2
          let newV := copyRow56Into dstV srcV
          slab1.set dstIdx newV (by simpa [slab1] using h.1)
        else slab) slab
      (dstOff + rCnt, slab)) (0, slab)
  let slab := runFused bt deepStart (deepStart + subLog) deepStart globalSubIdx slab
  let nBlocks64 := subRows >>> 6
  let lvl3Init := Array.emptyWithCapacity (nBlocks64 * 8)
  let (lvl3, lws) :=
    Fin.foldl nBlocks64 (fun (p : Array Digest32 × Leaf64Ws) b64 =>
      let (d8, lws) := hash64LeavesToLvl3Ws p.2 slab (b64.val * 64)
      let acc := (((((((p.1.push d8.d0).push d8.d1).push d8.d2).push d8.d3).push d8.d4).push d8.d5).push d8.d6).push d8.d7
      (acc, lws)) (lvl3Init, lws)
  let (lvlsFrom3, _) := Model.Pcs.CommitSlab.buildSubtreeLevels lws.kws (subLog - 3) lvl3
  let root := (lvlsFrom3.getD (subLog - 3) #[]).getD 0 default
  (slab, lvlsFrom3, root, lws)

@[noinline] def runOneTrial (msg : Array UInt64) (subLog rep : Nat) : IO (Nat × Nat × Nat × UInt64 × UInt64) := do
  let logRows := 21
  let logInvRate := 1
  let logD := 22
  let g := logRows - subLog
  let groupRows := 1 <<< g
  let deepStart := logInvRate + g
  let nWorkers := 16
  let t0 ← IO.monoMsNow
  let bt := mkByteTwiddles (logD + rep * 0)
  let t1 ← IO.monoMsNow
  let step := 1 <<< subLog
  let resPerShard := step / nWorkers
  let subsPerCosetWorker := groupRows / nWorkers
  -- Allocate per-worker scratch ONCE (reused across coset 0 and coset 1 -> halves memory & cold page faults!)
  let initTasks := (Array.range nWorkers).map fun w =>
    Task.spawn fun _ =>
      let gws : GatherWs :=
        ⟨w, allocUniqueRow56Array (8 * groupRows), allocUniqueRow56Array groupRows,
         allocUniqueRow56Array (groupRows * resPerShard)⟩
    
      (gws, dws)
  let workerInit := initTasks.map Task.get
  let mut gWsPool : Array GatherWs := workerInit.map (·.1)
  let mut dPool : Array DeepWs := workerInit.map (·.2)
  let mut gTotal := 0
  let mut dhTotal := 0
  let mut chkG : UInt64 := 0
  let mut allRoots : Array Digest32 := Array.emptyWithCapacity ((1 <<< logInvRate) * groupRows)
  for coset in [0, 1] do
    let tg0 ← IO.monoMsNow
    let gTasks := gWsPool.map fun wsW =>
      Task.spawn fun _ =>
        runGatheredShardCoset msg bt logRows logInvRate g coset (wsW.workerId * resPerShard) resPerShard wsW
    let gRes := gTasks.map Task.get
    let shards : Array (Array Row56) := gRes.map (·.out)
    let gShells : Array GatherWs := gRes.map fun ws => { ws with out := #[] }
    chkG := chkG ^^^ ((shards.getD (rep % nWorkers) #[]).getD 0 default).w55
    let tg1 ← IO.monoMsNow
    gTotal := gTotal + (tg1 - tg0)
    let dTasks := dPool.map fun dws =>
      Task.spawn fun _ =>
        let (slabOut, trees, roots, lwsOut) :=
          Fin.foldl subsPerCosetWorker (fun (st : Array Row56 × Array (Array (Array Digest32)) × Array Digest32 × Leaf64Ws) k =>
            let localIdx := dws.workerId * subsPerCosetWorker + k.val
            let globalIdx := coset * groupRows + localIdx
            let (slab, lvls, r, lws) := deepAndHashLvl3CosetSub shards resPerShard bt deepStart subLog localIdx globalIdx st.1 st.2.2.2
            (slab, st.2.1.push lvls, st.2.2.1.push r, lws))
            (dws.slab, Array.emptyWithCapacity subsPerCosetWorker, Array.emptyWithCapacity subsPerCosetWorker, dws.lws)
        (({ workerId := dws.workerId, slab := slabOut, lws := lwsOut } : DeepWs), trees, roots)
    let dRes := dTasks.map Task.get
    for r in dRes do
      allRoots := allRoots ++ r.2.2
    dPool := dRes.map (·.1)
    gWsPool := gShells.map fun ws => { ws with out := shards.getD ws.workerId #[] }
    let tg2 ← IO.monoMsNow
    dhTotal := dhTotal + (tg2 - tg1)
  let td0 ← IO.monoMsNow
  let (topLvls, _) := Model.Pcs.CommitSlab.buildSubtreeLevels (mkKeccakWs8 0) deepStart allRoots
  let root := (topLvls.getD deepStart #[]).getD 0 default
  let td1 ← IO.monoMsNow
  pure (t1 - t0, gTotal, dhTotal + (td1 - td0), root.lo0, chkG)

def main : IO Unit := do
  let smLanes := 51
  let smLogRows := 10
  let smRate := 1
  let smLogD := 11
  let smSubLog := 6
  let smG := 4
  let smMsg := (Array.range (smLanes * (1 <<< smLogRows))).map fun i => UInt64.ofNat (i * 0x9e3779b97f4a7c15 + 17)
  let expectedRoot := Model.Pcs.Commit.rootBytes smMsg smLanes smLogRows smRate
  let smBt := mkByteTwiddles smLogD
  let smWs0 : GatherWs := ⟨0, allocUniqueRow56Array (8 * 16), allocUniqueRow56Array 16, allocUniqueRow56Array (16 * 32)⟩
  let smWs1 : GatherWs := ⟨1, allocUniqueRow56Array (8 * 16), allocUniqueRow56Array 16, allocUniqueRow56Array (16 * 32)⟩
  let mut smRoots : Array Digest32 := #[]
  let mut smSlab := allocUniqueRow56Array 64
  let mut smLws := mkLeaf64Ws 0
  let mut w0 := smWs0
  let mut w1 := smWs1
  for c in [0, 1] do
    w0 := runGatheredShardCoset smMsg smBt smLogRows smRate smG c 0 32 w0
    w1 := runGatheredShardCoset smMsg smBt smLogRows smRate smG c 32 32 w1
    let cShards := #[w0.out, w1.out]
    for loc in [:16] do
      let (sl, _, r, lw) := deepAndHashLvl3CosetSub cShards 32 smBt (smRate + smG) smSubLog loc (c * 16 + loc) smSlab smLws
      smSlab := sl
      smLws := lw
      smRoots := smRoots.push r
  let (smTop, _) := Model.Pcs.CommitSlab.buildSubtreeLevels (mkKeccakWs8 0) (smRate + smG) smRoots
  let gotRoot := ((smTop.getD (smRate + smG) #[]).getD 0 default).toBytes
  if gotRoot != expectedRoot then
    IO.println s!"SMALL_PARITY=FAIL got={gotRoot.data} exp={expectedRoot.data}"
    IO.Process.exit 1
  IO.println "SMALL_PARITY=PASS"
  let n := 51 * (1 <<< 21)
  let msgInit := Array.emptyWithCapacity n
  let msg := foldRange n (fun acc i => acc.push (UInt64.ofNat (i * 6364136223846793005 + 1))) msgInit
  for subLog in [11, 12, 13] do
    for rep in [0, 1] do
      let msgRun := (msg.push (UInt64.ofNat rep)).pop
      let (twMs, gMs, dhMs, rLo, chk) ← runOneTrial msgRun subLog rep
      IO.println s!"subLog={subLog} rep={rep} tw={twMs}ms gather={gMs}ms deep_hash={dhMs}ms TOTAL={twMs + gMs + dhMs}ms root={rLo} chk={chk}"
  let status ← IO.FS.readFile "/proc/self/status"
  for line in status.splitOn "\n" do
    if line.startsWith "VmHWM:" || line.startsWith "VmRSS:" then
      IO.println line
