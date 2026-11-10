import Spec.Pcs.Ntt
import Model.Field.NativeKernel

namespace LeanVmXmss.Model.Pcs.Ntt

open Spec.Field (K add)
open Model.Field (nativeMul nativeInv)

@[inline] def foldRangeLoop {α : Type} (f : α → Nat → α) (rem idx : Nat) (acc : α) : α :=
  Fin.foldl rem (fun a k => f a (idx + k.val)) acc

@[inline] def foldRange {α : Type} (n : Nat) (f : α → Nat → α) (init : α) : α :=
  foldRangeLoop f n 0 init

def basisBit := Spec.Pcs.Ntt.basisBit
def basis := Spec.Pcs.Ntt.basis

def nextRow (prev : Array K) : Array K :=
  (Array.range (prev.size - 1)).map fun k =>
    let v := prev.getD (k + 1) 0
    nativeMul v (add v (prev.getD 0 0))

def rowList (dim : Nat) : List (Array K) :=
  (List.range (dim - 1)).foldl (fun acc _ =>
    match acc.getLast? with
    | some prev => acc ++ [nextRow prev]
    | none => acc) (if dim == 0 then [] else [basis dim])

def scaleRow (row : Array K) : Array K :=
  let scale := nativeInv (row.getD 0 0)
  row.map (nativeMul scale)

def evals (dim : Nat) : Array K :=
  (rowList dim).foldl (fun acc row => acc ++ scaleRow row) #[]

def rowStart := Spec.Pcs.Ntt.rowStart

def rowFromEvals (table : Array K) (dim i : Nat) : Array K :=
  let start := rowStart dim i
  table.extract start (start + dim - i)

def row (dim i : Nat) : Array K :=
  rowFromEvals (evals dim) dim i

@[inline] def twiddleLoop (values : Array K) (block rem j : Nat) (acc : K) : K :=
  foldRangeLoop
    (fun cur idx => if Nat.testBit block idx then add cur (values.getD (idx + 1) 0) else cur)
    rem j acc

@[inline] def twiddleFromRow (values : Array K) (block : Nat) : K :=
  twiddleLoop values block (values.size - 1) 0 0

def twiddle (dim layer block : Nat) : K :=
  twiddleFromRow (row dim (dim - layer - 1)) block

@[inline] def butterfly (top bot t : K) : K × K :=
  let u := add top (nativeMul bot t)
  (u, add bot u)

def encodeLayerWithEvals (table : Array K) (data : Array K) (lanes layer logD : Nat) : Array K :=
  let blocks := 1 <<< layer
  let half := 1 <<< (logD - layer - 1)
  let values := rowFromEvals table logD (logD - layer - 1)
  foldRange blocks (fun data block =>
    let t := twiddleFromRow values block
    foldRange half (fun data rowIndex =>
      let top := (block * (2 * half) + rowIndex) * lanes
      let bot := top + half * lanes
      foldRange lanes (fun data lane =>
        let pair := butterfly (data.getD (top + lane) 0) (data.getD (bot + lane) 0) t
        (data.setIfInBounds (top + lane) pair.1).setIfInBounds (bot + lane) pair.2) data) data) data

def encodeLayer (data : Array K) (lanes layer logD : Nat) : Array K :=
  encodeLayerWithEvals (evals logD) data lanes layer logD

def encode (data : Array K) (lanes startLayer : Nat) : Array K :=
  let logD := (data.size / lanes).log2
  let table := evals logD
  foldRange (logD - startLayer) (fun data step =>
    encodeLayerWithEvals table data lanes (startLayer + step) logD) data

structure Vec8 where
  w0 : K
  w1 : K
  w2 : K
  w3 : K
  w4 : K
  w5 : K
  w6 : K
  w7 : K
  deriving Inhabited, DecidableEq, Repr

def Vec8.lane (v : Vec8) : Nat → K
  | 0 => v.w0
  | 1 => v.w1
  | 2 => v.w2
  | 3 => v.w3
  | 4 => v.w4
  | 5 => v.w5
  | 6 => v.w6
  | 7 => v.w7
  | _ => 0

@[inline] def butterflyVec8U (top bot : Vec8) (t : K) : Vec8 :=
  if t = 0 then top
  else
    ⟨top.w0 ^^^ nativeMul bot.w0 t,
     top.w1 ^^^ nativeMul bot.w1 t,
     top.w2 ^^^ nativeMul bot.w2 t,
     top.w3 ^^^ nativeMul bot.w3 t,
     top.w4 ^^^ nativeMul bot.w4 t,
     top.w5 ^^^ nativeMul bot.w5 t,
     top.w6 ^^^ nativeMul bot.w6 t,
     top.w7 ^^^ nativeMul bot.w7 t⟩

@[inline] def butterflyVec8V (bot u : Vec8) : Vec8 :=
  ⟨bot.w0 ^^^ u.w0,
   bot.w1 ^^^ u.w1,
   bot.w2 ^^^ u.w2,
   bot.w3 ^^^ u.w3,
   bot.w4 ^^^ u.w4,
   bot.w5 ^^^ u.w5,
   bot.w6 ^^^ u.w6,
   bot.w7 ^^^ u.w7⟩

@[inline] def vecPairLoop (topBase botBase : Nat) (t : K)
    (rem v : Nat) (data : Array Vec8) : Array Vec8 :=
  foldRangeLoop (fun data curV =>
    let topIdx := topBase + curV
    let botIdx := botBase + curV
    let topV := data.getD topIdx default
    let botV := data.getD botIdx default
    let data := data.setIfInBounds topIdx default
    let data := data.setIfInBounds botIdx default
    let uV := butterflyVec8U topV botV t
    let vV := butterflyVec8V botV uV
    (data.setIfInBounds topIdx uV).setIfInBounds botIdx vV) rem v data

@[inline] def rowPairLoop (blockRowBase half nVecs : Nat) (t : K)
    (rem rowIndex : Nat) (data : Array Vec8) : Array Vec8 :=
  foldRangeLoop (fun data curRow =>
    let topBase := (blockRowBase + curRow) * nVecs
    let botBase := topBase + half * nVecs
    vecPairLoop topBase botBase t nVecs 0 data) rem rowIndex data

@[inline] def cosetBlockLoop (values : Array K) (blockBase half nVecs : Nat)
    (rem localBlock : Nat) (data : Array Vec8) : Array Vec8 :=
  foldRangeLoop (fun data curBlock =>
    let t := twiddleFromRow values (blockBase + curBlock)
    let blockRowBase := curBlock * (2 * half)
    rowPairLoop blockRowBase half nVecs t half 0 data) rem localBlock data

def encodeCosetLayerVec8 (table : Array K) (data : Array Vec8)
    (nVecs logRows logInvRate coset step : Nat) : Array Vec8 :=
  let layer := logInvRate + step
  let logD := logRows + logInvRate
  let localBlocks := 1 <<< step
  let half := 1 <<< (logRows - step - 1)
  let values := rowFromEvals table logD (logD - layer - 1)
  let blockBase := coset <<< step
  cosetBlockLoop values blockBase half nVecs localBlocks 0 data

@[inline] def cosetStepLoop (table : Array K) (nVecs logRows logInvRate coset : Nat)
    (rem step : Nat) (data : Array Vec8) : Array Vec8 :=
  foldRangeLoop (fun data curStep =>
    encodeCosetLayerVec8 table data nVecs logRows logInvRate coset curStep) rem step data

def encodeCosetVec8 (table : Array K) (first : Array Vec8)
    (nVecs logRows logInvRate coset : Nat) : Array Vec8 :=
  cosetStepLoop table nVecs logRows logInvRate coset logRows 0 first

end LeanVmXmss.Model.Pcs.Ntt
