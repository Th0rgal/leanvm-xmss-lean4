import Spec.Field.Basic
import Model.Field.Scalar

namespace LeanVmXmss.Spec.Xmss

open Spec.Field (E)

def readLE (bytes : ByteArray) (offset size : Nat) : UInt64 :=
  (List.range size).foldl (fun acc i => acc ||| (bytes[offset+i]!.toUInt64 <<< (8*i).toUInt64)) 0

def writeLE (x : UInt64) (size : Nat) : ByteArray :=
  ⟨(Array.range size).map fun i => if i < 8 then (x >>> (8*i).toUInt64).toUInt8 else 0⟩

def packCell (bytes : ByteArray) (offset : Nat := 0) : E :=
  ⟨readLE bytes offset 8, readLE bytes (offset+8) 8, 0⟩

def cellBytes (x : E) : ByteArray := writeLE x.c0 8 ++ writeLE x.c1 8

def cellsBytes (xs : Array E) : ByteArray := xs.foldl (fun acc x => acc ++ cellBytes x) ByteArray.empty

def gpow : Nat → UInt64 :=
  Nat.rec 1 (fun _ x =>
    (x <<< 1) ^^^ (if x.toNat / 2^63 == 0 then 0 else 0x1b))

def count (n : Nat) : E := ⟨gpow n, 0, 0⟩

def claimGroup : Nat := 17
def bigGroups : Nat := 8

def listSplit (n : Nat) : Array E :=
  #[count (n / (claimGroup * bigGroups)), count (n % (claimGroup * bigGroups) / claimGroup), count (n % claimGroup)]

structure RawSignature where
  publicKey : ByteArray
  message : ByteArray
  signature : ByteArray
  deriving Inhabited

def recordSize : Nat := 2468

def parseRaw (bytes : ByteArray) : Except String (Array RawSignature) := do
  if bytes.size % recordSize != 0 then throw "raw record length is not a multiple of 2468"
  let mut out := #[]
  for i in [:bytes.size / recordSize] do
    let offset := i*recordSize
    let pk := bytes.extract offset (offset+32)
    let msg := bytes.extract (offset+32) (offset+64)
    let sig := bytes.extract (offset+64) (offset+recordSize)
    out := out.push ⟨pk, msg, sig⟩
  return out

def validateProofEnvelope (bytes : ByteArray) : Bool :=
  bytes.size >= 8 && (readLE bytes 0 8).toNat == bytes.size - 8

def claimBytes (raw : RawSignature) : ByteArray := raw.publicKey ++ raw.message

def bytesLT (a b : ByteArray) : Bool :=
  a.data.toList < b.data.toList

def sortedUnique (raw : Array RawSignature) : Array RawSignature := Id.run do
  let sorted := raw.qsort fun a b => bytesLT (claimBytes a) (claimBytes b)
  let mut out := #[]
  for x in sorted do
    if out.back?.map (fun y => claimBytes y == claimBytes x) != some true then
      out := out.push x
  return out

structure Coverage where
  signers : Array RawSignature
  rawSlots : Array Nat
  duplicates : Array RawSignature

def planCoverage (raw : Array RawSignature) : Coverage := Id.run do
  let signers := sortedUnique raw
  let mut claimed := Array.replicate signers.size false
  let mut duplicates := #[]
  let mut slots := #[]
  for x in raw do
    let pos := signers.findIdx? (fun y => claimBytes x == claimBytes y)
    match pos with
    | some p =>
      if !claimed[p]! then
        slots := slots.push p
        claimed := claimed.set! p true
      else
        slots := slots.push (signers.size + duplicates.size)
        duplicates := duplicates.push x
    | none =>
      slots := slots.push (signers.size + duplicates.size)
      duplicates := duplicates.push x
  return ⟨signers, slots, duplicates⟩

end LeanVmXmss.Spec.Xmss
