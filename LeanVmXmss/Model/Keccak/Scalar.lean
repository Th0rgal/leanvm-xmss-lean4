import Spec.Keccak.Basic

namespace LeanVmXmss.Model.Keccak

abbrev State := Spec.Keccak.State

def round (a : State) (r : UInt64) : State :=
  Spec.Keccak.iota (Spec.Keccak.chi (Spec.Keccak.rhoPi (Spec.Keccak.theta a))) r

def permute (a : State) : State := Spec.Keccak.rc.foldl round a

def finalBlock (b : ByteArray) (domain : UInt8 := 1) : ByteArray := Spec.Keccak.finalBlock b domain

def blocks (b : ByteArray) (domain : UInt8 := 1) : Array ByteArray :=
  ((Array.range (b.size / 136)).map fun i => b.extract (136 * i) (136 * (i + 1))).push
    (finalBlock (b.extract (136 * (b.size / 136)) b.size) domain)

def absorbBlock (a : State) (b : ByteArray) : State :=
  permute ((Array.range 25).map fun i => if i < 17 then a[i]! ^^^ Spec.Keccak.wordAt b (8 * i) else a[i]!)

def keccak256 (b : ByteArray) : ByteArray :=
  Spec.Keccak.wordsBytes (((blocks b).foldl absorbBlock Spec.Keccak.zero).extract 0 4)

end LeanVmXmss.Model.Keccak
