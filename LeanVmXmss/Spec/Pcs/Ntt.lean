import Spec.Field.Operations

namespace LeanVmXmss.Spec.Pcs.Ntt

open Spec.Field (K add mul inv)

def basisBit (i : Nat) : K :=
  if i < 64 then UInt64.ofNat (Nat.pow 2 i) else 0

def basis (dim : Nat) : Array K :=
  (Array.range dim).map basisBit

def nextRow (prev : Array K) : Array K :=
  (Array.range (prev.size - 1)).map fun k =>
    let v := prev.getD (k + 1) 0
    mul v (add v (prev.getD 0 0))

def rowList (dim : Nat) : List (Array K) :=
  (List.range (dim - 1)).foldl (fun acc _ =>
    match acc.getLast? with
    | some prev => acc ++ [nextRow prev]
    | none => acc) (if dim == 0 then [] else [basis dim])

def scaleRow (row : Array K) : Array K :=
  let scale := inv (row.getD 0 0)
  row.map (mul scale)

def evals (dim : Nat) : Array K :=
  (rowList dim).foldl (fun acc row => acc ++ scaleRow row) #[]

def rowStart (dim i : Nat) : Nat := i * dim - i * (i - 1) / 2

def row (dim i : Nat) : Array K :=
  let start := rowStart dim i
  (evals dim).extract start (start + dim - i)

def twiddle (dim layer block : Nat) : K :=
  let values := row dim (dim - layer - 1)
  (Array.range (values.size - 1)).foldl (fun acc j =>
    if Nat.testBit block j then add acc (values.getD (j + 1) 0) else acc) 0

def butterfly (top bot t : K) : K × K :=
  let u := add top (mul bot t)
  (u, add bot u)

def encodeLayer (data : Array K) (lanes layer logD : Nat) : Array K :=
  let blocks := 1 <<< layer
  let half := 1 <<< (logD - layer - 1)
  (Array.range blocks).foldl (fun data block =>
    let t := twiddle logD layer block
    (Array.range half).foldl (fun data rowIndex =>
      let top := (block * (2 * half) + rowIndex) * lanes
      let bot := top + half * lanes
      (Array.range lanes).foldl (fun data lane =>
        let pair := butterfly (data.getD (top + lane) 0) (data.getD (bot + lane) 0) t
        (data.setIfInBounds (top + lane) pair.1).setIfInBounds (bot + lane) pair.2) data) data) data

def encode (data : Array K) (lanes startLayer : Nat) : Array K :=
  let logD := (data.size / lanes).log2
  (Array.range (logD - startLayer)).foldl (fun data step =>
    encodeLayer data lanes (startLayer + step) logD) data

end LeanVmXmss.Spec.Pcs.Ntt
