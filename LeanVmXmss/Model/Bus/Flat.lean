import Model.Bus.Native
import Model.Witness.Flat

namespace LeanVmXmss.Model.Bus

open Spec.Field (K E zero one)
open Spec.Witness
open Model.Pcs.Ntt (foldRange)
open Model.Field

structure PlanarE where
  c0 : ByteArray
  c1 : ByteArray
  c2 : ByteArray
  deriving Inhabited

def planarEEmpty (n : Nat) : PlanarE :=
  ⟨ByteArray.emptyWithCapacity (8 * n), ByteArray.emptyWithCapacity (8 * n),
   ByteArray.emptyWithCapacity (8 * n)⟩

def planarEPush (p : PlanarE) (x : E) : PlanarE :=
  ⟨Model.Witness.pushU64LE p.c0 x.c0,
   Model.Witness.pushU64LE p.c1 x.c1,
   Model.Witness.pushU64LE p.c2 x.c2⟩

def planarEGet (p : PlanarE) (i : Nat) : E :=
  ⟨Model.Witness.readU64LE p.c0 i,
   Model.Witness.readU64LE p.c1 i,
   Model.Witness.readU64LE p.c2 i⟩

def decodePlanarE (p : PlanarE) : Array E :=
  let n := p.c0.size / 8
  foldRange n (fun acc i => acc.push (planarEGet p i)) (Array.emptyWithCapacity n)

def encodePlanarE (xs : Array E) : PlanarE :=
  foldRange xs.size (fun acc i => planarEPush acc (xs[i]?.getD zero)) (planarEEmpty xs.size)

def eqTableFlat (r : Array E) : PlanarE :=
  encodePlanarE (eqTable r)

def foldTableFlat (state : Array (Array E)) (r : E) (half : Nat) : Array (Array E) :=
  foldTableState state r half

def proveBalanceFlat (gpows : Array K) (lay : Model.Layout.PublicLayout)
    (cols bcCols : Array (Array K)) (ps : ProverState) : BusProof × ProverState :=
  proveBalance gpows lay cols bcCols ps

def proveConstraintsFlat (airs : Array AirTable) (cols : Array (Array K))
    (zeta : Array E) (ps : ProverState) : Array TableClaims × ProverState :=
  proveConstraints airs cols zeta ps

def proveBusAndConstraintsFlat (program : Array Spec.Vm.Op) (iv : ByteArray)
    (publicInput : Array E) (bundle : WitnessBundle) : BusStageOutput :=
  let encoded := encodePlanarE (startTranscript iv publicInput bundle.sized bundle.root).stream
  let _decoded := decodePlanarE encoded
  proveBusAndConstraints program iv publicInput bundle

end LeanVmXmss.Model.Bus
