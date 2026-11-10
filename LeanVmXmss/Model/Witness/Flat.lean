import Model.Witness.Scalar

namespace LeanVmXmss.Model.Witness

open Spec.Field (K E)
open Spec.Witness
open Model.Pcs.Ntt (foldRange)

structure PlanarNat where
  bytes : ByteArray
  deriving Inhabited

def planarNatEmpty (n : Nat) : PlanarNat :=
  ⟨ByteArray.emptyWithCapacity (8 * n)⟩

@[noinline]
def pushU64LE (bytes : ByteArray) (w : UInt64) : ByteArray :=
  foldRange 8 (fun acc i => acc.push ((w >>> UInt64.ofNat (8 * i)).toUInt8)) bytes

@[noinline]
def readU64LE (bytes : ByteArray) (index : Nat) : UInt64 :=
  foldRange 8
    (fun acc lane =>
      let b := bytes.data[8 * index + lane]?.getD 0
      acc ||| (b.toUInt64 <<< UInt64.ofNat (8 * lane)))
    0

def planarPush (p : PlanarNat) (n : Nat) : PlanarNat :=
  ⟨pushU64LE p.bytes (UInt64.ofNat n)⟩

def planarGet (p : PlanarNat) (i : Nat) : Nat :=
  (readU64LE p.bytes i).toNat

def decodePlanarNat (p : PlanarNat) : Array Nat :=
  let n := p.bytes.size / 8
  foldRange n (fun acc i => acc.push (planarGet p i)) (Array.emptyWithCapacity n)

def bumpCountsFlat (addresses : Array Nat) (cells : Array Spec.Vm.Cell) : PlanarNat :=
  let n := addresses.size
  let limit :=
    foldRange n (fun m i => max m ((addresses[i]?.getD 0) + 1)) 1
  let (counts, _) := foldRange n
    (fun (acc, seen) index =>
      let address := addresses[index]?.getD 0
      let base := (Model.Vm.cellAt cells address).accesses
      let prior := seen[address]?.getD 0
      (planarPush acc (base + prior), seen.setIfInBounds address (prior + 1)))
    (planarNatEmpty n, Array.replicate limit 0)
  counts

def bumpCounts (addresses : Array Nat) (cells : Array Spec.Vm.Cell) : Array Nat :=
  decodePlanarNat (bumpCountsFlat addresses cells)

theorem bumpCounts_flat_empty :
    bumpCounts #[] #[] = Spec.Witness.bumpCounts #[] #[] := by
  simp [bumpCounts, bumpCountsFlat, decodePlanarNat, Spec.Witness.bumpCounts,
    planarNatEmpty, foldRange, Model.Pcs.Ntt.foldRangeLoop]

end LeanVmXmss.Model.Witness
