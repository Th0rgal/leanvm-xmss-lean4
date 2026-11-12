import Model.Prim.Slice64
import Model.Field.NativeKernel
import Model.Bus.Scalar

namespace LeanVmXmss.Native.Kernels

open Spec.Field (K E zero one)
open LeanVmXmss.Model.Prim.Slice64
open LeanVmXmss.Model.Field
open LeanVmXmss.Model.Bus (GroupedForm)

@[inline] def busGf64Mul (a b : UInt64) : UInt64 :=
  nativeMul a b

@[inline] def busExtAdd0 (a0 b0 : UInt64) : UInt64 := a0 ^^^ b0

@[inline] def busExtAdd1 (a1 b1 : UInt64) : UInt64 := a1 ^^^ b1

@[inline] def busExtAdd2 (a2 b2 : UInt64) : UInt64 := a2 ^^^ b2

@[inline] def busExtMul0 (a0 a1 a2 b0 b1 b2 : UInt64) : UInt64 :=
  nativeKaratsuba0 a0 a1 a2 b0 b1 b2

@[inline] def busExtMul1 (a0 a1 a2 b0 b1 b2 : UInt64) : UInt64 :=
  nativeKaratsuba1 a0 a1 a2 b0 b1 b2

@[inline] def busExtMul2 (a0 a1 a2 b0 b1 b2 : UInt64) : UInt64 :=
  nativeKaratsuba2 a0 a1 a2 b0 b1 b2

@[inline] def busMulBase0 (a0 k : UInt64) : UInt64 := nativeMul a0 k

@[inline] def busMulBase1 (a1 k : UInt64) : UInt64 := nativeMul a1 k

@[inline] def busMulBase2 (a2 k : UInt64) : UInt64 := nativeMul a2 k

@[inline] def busInterp0 (l0 l1 l2 h0 h1 h2 r0 r1 r2 : UInt64) : UInt64 :=
  l0 ^^^ nativeKaratsuba0 r0 r1 r2 (l0 ^^^ h0) (l1 ^^^ h1) (l2 ^^^ h2)

@[inline] def busInterp1 (l0 l1 l2 h0 h1 h2 r0 r1 r2 : UInt64) : UInt64 :=
  l1 ^^^ nativeKaratsuba1 r0 r1 r2 (l0 ^^^ h0) (l1 ^^^ h1) (l2 ^^^ h2)

@[inline] def busInterp2 (l0 l1 l2 h0 h1 h2 r0 r1 r2 : UInt64) : UInt64 :=
  l2 ^^^ nativeKaratsuba2 r0 r1 r2 (l0 ^^^ h0) (l1 ^^^ h1) (l2 ^^^ h2)

@[inline] def busInterpK0 (lo hi r0 : UInt64) : UInt64 :=
  lo ^^^ nativeMul r0 (lo ^^^ hi)

@[inline] def busInterpK1 (lo hi r1 : UInt64) : UInt64 :=
  nativeMul r1 (lo ^^^ hi)

@[inline] def busInterpK2 (lo hi r2 : UInt64) : UInt64 :=
  nativeMul r2 (lo ^^^ hi)

@[inline] def busEadd (a b : E) : E :=
  ⟨busExtAdd0 a.c0 b.c0, busExtAdd1 a.c1 b.c1, busExtAdd2 a.c2 b.c2⟩

@[inline] def busEmul (a b : E) : E :=
  let p0 := nativeMul a.c0 b.c0
  let p1 := nativeMul a.c1 b.c1
  let p2 := nativeMul a.c2 b.c2
  let e1 := nativeMul (a.c0 ^^^ a.c1) (b.c0 ^^^ b.c1) ^^^ p0 ^^^ p1
  let e2 := nativeMul (a.c0 ^^^ a.c2) (b.c0 ^^^ b.c2) ^^^ p0 ^^^ p2 ^^^ p1
  let e3 := nativeMul (a.c1 ^^^ a.c2) (b.c1 ^^^ b.c2) ^^^ p1 ^^^ p2
  ⟨p0 ^^^ e3, e1 ^^^ e3 ^^^ p2, e2 ^^^ p2⟩

@[inline] def busMulBase (a : E) (k : K) : E :=
  ⟨busMulBase0 a.c0 k, busMulBase1 a.c1 k, busMulBase2 a.c2 k⟩

@[inline] def busInterp (lo hi r : E) : E :=
  let d0 := lo.c0 ^^^ hi.c0
  let d1 := lo.c1 ^^^ hi.c1
  let d2 := lo.c2 ^^^ hi.c2
  let p0 := nativeMul r.c0 d0
  let p1 := nativeMul r.c1 d1
  let p2 := nativeMul r.c2 d2
  let e1 := nativeMul (r.c0 ^^^ r.c1) (d0 ^^^ d1) ^^^ p0 ^^^ p1
  let e2 := nativeMul (r.c0 ^^^ r.c2) (d0 ^^^ d2) ^^^ p0 ^^^ p2 ^^^ p1
  let e3 := nativeMul (r.c1 ^^^ r.c2) (d1 ^^^ d2) ^^^ p1 ^^^ p2
  ⟨lo.c0 ^^^ p0 ^^^ e3, lo.c1 ^^^ e1 ^^^ e3 ^^^ p2, lo.c2 ^^^ e2 ^^^ p2⟩

@[inline] def busInterpK (lo hi : K) (r : E) : E :=
  ⟨busInterpK0 lo hi r.c0, busInterpK1 lo hi r.c1, busInterpK2 lo hi r.c2⟩

@[inline] def busSliceFoldAt (c0 c1 c2 : @& ByteArray) (i half : USize) (r : E) : E :=
  let j := i + half
  let l0 := readU64LEU c0 i
  let l1 := readU64LEU c1 i
  let l2 := readU64LEU c2 i
  let h0 := readU64LEU c0 j
  let h1 := readU64LEU c1 j
  let h2 := readU64LEU c2 j
  busInterp ⟨l0, l1, l2⟩ ⟨h0, h1, h2⟩ r

@[inline] def busSliceMleTerm (table : @& ByteArray) (eqs : @& SliceE) (z : USize) : E :=
  let tv := readU64LEU table z
  let e0 := readU64LEU eqs.c0 z
  let e1 := readU64LEU eqs.c1 z
  let e2 := readU64LEU eqs.c2 z
  busMulBase ⟨e0, e1, e2⟩ tv

@[inline] def busSliceJoinLeftAt (kc : @& ByteArray) (i half : USize) (r : E) : E :=
  busInterpK (readU64LEU kc i) (readU64LEU kc (i + half)) r

def busQuarticSummand (g0 s0 g1 s1 g2 s2 g3 s3 eqWeight : E) : E × E × E × E :=
  let a0 := busEmul eqWeight g0
  let d0 := busEmul eqWeight s0
  let right0 := busEmul g2 g3
  let right2 := busEmul s2 s3
  let left0 := busEmul a0 g1
  let left2 := busEmul d0 s1
  let leftAtOne := busEmul (busEadd a0 d0) (busEadd g1 s1)
  let rightAtOne := busEmul (busEadd g2 s2) (busEadd g3 s3)
  let left1 := busEadd leftAtOne (busEadd left0 left2)
  let right1 := busEadd rightAtOne (busEadd right0 right2)
  let c0 := busEmul left0 right0
  let c4 := busEmul left2 right2
  let middle := busEmul left1 right1
  let atOne := busEmul leftAtOne rightAtOne
  let crossEven := busEmul (busEadd left0 left2) (busEadd right0 right2)
  let crossHigh := busEmul (busEadd left1 left2) (busEadd right1 right2)
  (busEadd c0 atOne, busEadd (busEadd crossEven c0) (busEadd c4 middle),
    busEadd crossHigh (busEadd middle c4), c4)

@[inline] def busAddMsg4 (a b : E × E × E × E) : E × E × E × E :=
  (busEadd a.1 b.1, busEadd a.2.1 b.2.1, busEadd a.2.2.1 b.2.2.1, busEadd a.2.2.2 b.2.2.2)

def busTreePairSummandSlice (values eqWeights : @& SliceE) (pair : Nat) : E × E × E × E :=
  let lo := 8 * pair
  let hi := lo + 4
  let g0 := sliceEGetOr values lo one
  let g1 := sliceEGetOr values (lo + 1) one
  let g2 := sliceEGetOr values (lo + 2) one
  let g3 := sliceEGetOr values (lo + 3) one
  let s0 := busEadd g0 (sliceEGetOr values hi one)
  let s1 := busEadd g1 (sliceEGetOr values (hi + 1) one)
  let s2 := busEadd g2 (sliceEGetOr values (hi + 2) one)
  let s3 := busEadd g3 (sliceEGetOr values (hi + 3) one)
  let w := sliceEGetOr eqWeights pair zero
  busQuarticSummand g0 s0 g1 s1 g2 s2 g3 s3 w

def busTreeRoundMessageRangeSlice (values eqWeights : @& SliceE)
    (start count : Nat) : E × E × E × E :=
  foldNat count
    (fun acc k => busAddMsg4 acc (busTreePairSummandSlice values eqWeights (start + k)))
    (zero, zero, zero, zero)

def busTreeRoundMessageSlice (values eqWeights : @& SliceE) : E × E × E × E :=
  let storedRows := sliceESize values / 4
  let fullPairs := storedRows / 2
  let msg := busTreeRoundMessageRangeSlice values eqWeights 0 fullPairs
  if storedRows % 2 = 1 then
    let lo := 8 * fullPairs
    let g0 := sliceEGetOr values lo one
    let g1 := sliceEGetOr values (lo + 1) one
    let g2 := sliceEGetOr values (lo + 2) one
    let g3 := sliceEGetOr values (lo + 3) one
    let w := sliceEGetOr eqWeights fullPairs zero
    busAddMsg4 msg (busQuarticSummand g0 (busEadd g0 one) g1 (busEadd g1 one)
      g2 (busEadd g2 one) g3 (busEadd g3 one) w)
  else
    msg

def busFoldTreeRangeSlice (values : @& SliceE) (challenge : E)
    (start count : Nat) : SliceE :=
  foldNat count
    (fun acc k =>
      let row := start + k
      let lo := 8 * row
      let v0 := sliceEGetOr values lo one
      let v1 := sliceEGetOr values (lo + 1) one
      let v2 := sliceEGetOr values (lo + 2) one
      let v3 := sliceEGetOr values (lo + 3) one
      let h0 := sliceEGetOr values (lo + 4) one
      let h1 := sliceEGetOr values (lo + 5) one
      let h2 := sliceEGetOr values (lo + 6) one
      let h3 := sliceEGetOr values (lo + 7) one
      let acc := sliceEPush acc (busInterp v0 h0 challenge)
      let acc := sliceEPush acc (busInterp v1 h1 challenge)
      let acc := sliceEPush acc (busInterp v2 h2 challenge)
      sliceEPush acc (busInterp v3 h3 challenge))
    (sliceEEmpty (4 * count))

def busFoldTreeSlice (values : @& SliceE) (challenge : E) : SliceE :=
  let storedRows := sliceESize values / 4
  let fullRows := storedRows / 2
  let folded := busFoldTreeRangeSlice values challenge 0 fullRows
  if storedRows % 2 = 1 then
    let lo := 8 * fullRows
    let v0 := sliceEGetOr values lo one
    let v1 := sliceEGetOr values (lo + 1) one
    let v2 := sliceEGetOr values (lo + 2) one
    let v3 := sliceEGetOr values (lo + 3) one
    let folded := sliceEPush folded (busInterp v0 one challenge)
    let folded := sliceEPush folded (busInterp v1 one challenge)
    let folded := sliceEPush folded (busInterp v2 one challenge)
    sliceEPush folded (busInterp v3 one challenge)
  else
    folded

def busNextLevelRangeSlice (current : @& SliceE) (start count : Nat) : SliceE :=
  foldNat count
    (fun acc k =>
      let row := start + k
      let c0 := sliceEGetOr current (4 * row) one
      let c1 := sliceEGetOr current (4 * row + 1) one
      let c2 := sliceEGetOr current (4 * row + 2) one
      let c3 := sliceEGetOr current (4 * row + 3) one
      sliceEPush acc (busEmul (busEmul c0 c1) (busEmul c2 c3)))
    (sliceEEmpty count)

def busNextLevelSlice (current : @& SliceE) : SliceE :=
  let n := sliceESize current
  let fullRows := n / 4
  let full := busNextLevelRangeSlice current 0 fullRows
  if 4 * fullRows < n then
    let c0 := sliceEGetOr current (4 * fullRows) one
    let c1 := sliceEGetOr current (4 * fullRows + 1) one
    let c2 := sliceEGetOr current (4 * fullRows + 2) one
    let c3 := sliceEGetOr current (4 * fullRows + 3) one
    sliceEPush full (busEmul (busEmul c0 c1) (busEmul c2 c3))
  else
    full

def busFoldColumnRangeSlice (col : @& SliceE) (r : E) (half start count : Nat) : SliceE :=
  let halfU := half.toUSize
  foldNat count
    (fun out k =>
      let iU := (start + k).toUSize
      sliceEPush out (busSliceFoldAt col.c0 col.c1 col.c2 iU halfU r))
    (sliceEEmpty count)

def busFoldColumnSlice (col : @& SliceE) (r : E) (half : Nat) : SliceE :=
  busFoldColumnRangeSlice col r half 0 half

def busFoldTableStateSlice (state : @& Array SliceE) (r : E) (half : Nat) : Array SliceE :=
  foldNat state.size
    (fun acc c =>
      let col := state[c]?.getD (sliceEEmpty 0)
      acc.push (busFoldColumnSlice col r half))
    (Array.emptyWithCapacity state.size)

def busTableMessageERangeSlice (state : @& Array SliceE) (eqr : @& SliceE)
    (half : Nat) (atOne : Bool) (start count : Nat) : E × E :=
  let nGroups := (state.size - 1) / 2
  let linCol := state[0]?.getD (sliceEEmpty 0)
  foldNat count
    (fun (eAcc, sAcc) k =>
      let i := start + k
      let endIdx := if atOne then i + half else i
      let linEnd := sliceEGetOr linCol endIdx zero
      let (ep, sl) := foldNat nGroups
        (fun (epG, slG) g =>
          let lCol := state[1 + 2 * g]?.getD (sliceEEmpty 0)
          let rCol := state[2 + 2 * g]?.getD (sliceEEmpty 0)
          let lEnd := sliceEGetOr lCol endIdx zero
          let rEnd := sliceEGetOr rCol endIdx zero
          let lSum := busEadd (sliceEGetOr lCol i zero) (sliceEGetOr lCol (i + half) zero)
          let rSum := busEadd (sliceEGetOr rCol i zero) (sliceEGetOr rCol (i + half) zero)
          (busEadd epG (busEmul lEnd rEnd), busEadd slG (busEmul lSum rSum)))
        (linEnd, zero)
      let eqw := sliceEGetOr eqr i zero
      (busEadd eAcc (busEmul eqw ep), busEadd sAcc (busEmul eqw sl)))
    (zero, zero)

def busTableMessageESlice (constant : E) (state : @& Array SliceE) (eqr : @& SliceE)
    (half : Nat) (atOne : Bool) : E × E :=
  let (eSum, sSum) := busTableMessageERangeSlice state eqr half atOne 0 half
  (busEadd constant eSum, sSum)

def busEvalLinKSlice (terms : @& Array (Nat × E)) (cols : @& Array ByteArray)
    (base row : Nat) : E :=
  foldNat terms.size
    (fun acc idx =>
      match terms[idx]? with
      | none => acc
      | some (c, w) =>
        let col := cols[base + c]?.getD ByteArray.empty
        let v := readU64LEOr col row 0
        busEadd acc (busMulBase w v))
    zero

def busEvalLinSumKSlice (terms : @& Array (Nat × E)) (cols : @& Array ByteArray)
    (base i half : Nat) : E :=
  foldNat terms.size
    (fun acc idx =>
      match terms[idx]? with
      | none => acc
      | some (c, w) =>
        let col := cols[base + c]?.getD ByteArray.empty
        let s := (readU64LEOr col i 0) ^^^ (readU64LEOr col (i + half) 0)
        busEadd acc (busMulBase w s))
    zero

def busTableMessageKRangeSlice (gf : @& GroupedForm) (cols : @& Array ByteArray)
    (base : Nat) (eqr : @& SliceE) (half : Nat) (atOne : Bool) (start count : Nat) : E × E :=
  foldNat count
    (fun (eAcc, sAcc) k =>
      let i := start + k
      let endIdx := if atOne then i + half else i
      let linEnd := busEvalLinKSlice gf.lin cols base endIdx
      let (ep, sl) := foldNat gf.groups.size
        (fun (epG, slG) g =>
          match gf.groups[g]? with
          | none => (epG, slG)
          | some (left, right) =>
            let leftCol := cols[base + left]?.getD ByteArray.empty
            let leftEnd := readU64LEOr leftCol endIdx 0
            let leftSum := (readU64LEOr leftCol i 0) ^^^ (readU64LEOr leftCol (i + half) 0)
            let rightEnd := busEvalLinKSlice right cols base endIdx
            let rightSum := busEvalLinSumKSlice right cols base i half
            (busEadd epG (busMulBase rightEnd leftEnd),
              busEadd slG (busMulBase rightSum leftSum)))
        (linEnd, zero)
      let eqw := sliceEGetOr eqr i zero
      (busEadd eAcc (busEmul eqw ep), busEadd sAcc (busEmul eqw sl)))
    (zero, zero)

def busTableMessageKSlice (gf : @& GroupedForm) (cols : @& Array ByteArray)
    (base : Nat) (eqr : @& SliceE) (half : Nat) (atOne : Bool) : E × E :=
  let (endAcc, slopeAcc) := busTableMessageKRangeSlice gf cols base eqr half atOne 0 half
  (busEadd endAcc gf.constant, slopeAcc)

def busJoinLinColRangeSlice (terms : @& Array (Nat × E)) (cols : @& Array ByteArray)
    (base : Nat) (r : E) (half start count : Nat) : SliceE :=
  foldNat count
    (fun col k =>
      let i := start + k
      let v := foldNat terms.size
        (fun acc idx =>
          match terms[idx]? with
          | none => acc
          | some (c, w) =>
            let kc := cols[base + c]?.getD ByteArray.empty
            let lo := readU64LEOr kc i 0
            let hi := readU64LEOr kc (i + half) 0
            let wr := busEmul w r
            busEadd acc (busEadd (busMulBase w lo) (busMulBase wr (lo ^^^ hi))))
        zero
      sliceEPush col v)
    (sliceEEmpty count)

def busJoinLinColSlice (terms : @& Array (Nat × E)) (cols : @& Array ByteArray)
    (base : Nat) (r : E) (half : Nat) : SliceE :=
  busJoinLinColRangeSlice terms cols base r half 0 half

def busJoinLeftColRangeSlice (kc : @& ByteArray) (r : E) (half start count : Nat) : SliceE :=
  let halfU := half.toUSize
  foldNat count
    (fun col k =>
      let iU := (start + k).toUSize
      sliceEPush col (busSliceJoinLeftAt kc iU halfU r))
    (sliceEEmpty count)

def busJoinLeftColSlice (kc : @& ByteArray) (r : E) (half : Nat) : SliceE :=
  busJoinLeftColRangeSlice kc r half 0 half

def busJoinTableStateSlice (gf : @& GroupedForm) (cols : @& Array ByteArray)
    (base : Nat) (r : E) (half : Nat) : Array SliceE :=
  let initCols := #[busJoinLinColSlice gf.lin cols base r half]
  foldNat gf.groups.size
    (fun stateCols g =>
      match gf.groups[g]? with
      | none => stateCols
      | some (left, right) =>
        let kc := cols[base + left]?.getD ByteArray.empty
        let leftCol := busJoinLeftColSlice kc r half
        let rightCol := busJoinLinColSlice right cols base r half
        (stateCols.push leftCol).push rightCol)
    initCols

def busMleEvalRangeSlice (table : @& ByteArray) (eqs : @& SliceE)
    (start count : Nat) : E :=
  foldNat count
    (fun acc k =>
      let zU := (start + k).toUSize
      busEadd acc (busSliceMleTerm table eqs zU))
    zero

def busMleEvalSlice (table : @& ByteArray) (eqs : @& SliceE) : E :=
  busMleEvalRangeSlice table eqs 0 (sliceESize eqs)

end LeanVmXmss.Native.Kernels
