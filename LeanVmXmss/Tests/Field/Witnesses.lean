import Proofs.Field.Windows

namespace LeanVmXmss.Tests.Field

open Spec.Field (K E)

set_option maxRecDepth 20000
set_option maxHeartbeats 0

def wrongModulus (a b : K) : K :=
  UInt64.ofNat (Spec.Field.remainderSteps 64 (2^64 + 0x1D) 64 (Model.Field.clmul a b).toNat)

def omittedExtensionTerm (a b : E) : E :=
  let good := Model.Field.polynomialMul a b
  ⟨Model.Field.mul a.c0 b.c0, good.c1, good.c2⟩

def reversedShiftSteps (a b : BitVec 64) : Nat → BitVec 128 :=
  Nat.rec 0 (fun n prev => prev ^^^ if b.getLsbD n then a.setWidth 128 >>> n else 0)

def reversedShift (a b : K) : K :=
  Model.Field.reduce (reversedShiftSteps a.toBitVec b.toBitVec 64)

def reversedLimbs (a : E) : UInt64 × UInt64 × UInt64 := (a.c2, a.c1, a.c0)

theorem wrongModulus_rejected :
    wrongModulus 0x8000000000000000 2 ≠ Spec.Field.mul 0x8000000000000000 2 := by
  rw [← Proofs.Field.mul_refines_spec]
  decide

theorem omittedExtensionTerm_rejected :
    omittedExtensionTerm Spec.Field.y ⟨0, 0, 1⟩ ≠
      Spec.Field.emul Spec.Field.y ⟨0, 0, 1⟩ := by
  rw [← Proofs.Field.polynomial_refines_spec]
  decide

theorem reversedShift_rejected : reversedShift 2 2 ≠ Spec.Field.mul 2 2 := by
  rw [← Proofs.Field.mul_refines_spec]
  decide

theorem reversedLimbs_rejected : reversedLimbs ⟨1, 2, 3⟩ ≠ Spec.Field.encode ⟨1, 2, 3⟩ := by decide

structure PosWitness where
  left : E
  right : E
  result : E
  left_high : Spec.Field.bit left.c0 63 = true
  left_cross : left.c1 ≠ 0
  right_cross : right.c2 ≠ 0
  base_reduction : Spec.Field.mul left.c0 right.c0 = 0x1B
  product : Spec.Field.emul left right = result
  output_constant : result.c0 ≠ 0
  output_linear : result.c1 ≠ 0
  output_quadratic : result.c2 ≠ 0

def positiveWitness : PosWitness where
  left := ⟨0x8000000000000000, 1, 0⟩
  right := ⟨2, 0, 1⟩
  result := ⟨0x1A, 3, 0x8000000000000000⟩
  left_high := by decide
  left_cross := by decide
  right_cross := by decide
  base_reduction := by decide
  product := by decide
  output_constant := by decide
  output_linear := by decide
  output_quadratic := by decide

def wrongInverseExponent (a : K) : K := Model.Field.pow a 2

def nonzeroInverseZero (a : K) : K := if a.toNat = 0 then 1 else Model.Field.inv a

def reverseByteOrder (a : K) : ByteArray := ⟨(Model.Field.encodeBytesK a).data.toList.reverse.toArray⟩

def acceptTrailingBytes (b : ByteArray) : Option K :=
  if b.size ≥ 8 then some (Spec.Field.readLimb b 0) else none

theorem wrongInverseExponent_rejected : wrongInverseExponent 2 ≠ Model.Field.inv 2 := by decide

theorem nonzeroInverseZero_rejected : nonzeroInverseZero 0 ≠ Model.Field.inv 0 := by decide

theorem reverseByteOrder_rejected : reverseByteOrder 1 ≠ Model.Field.encodeBytesK 1 := by
  intro h
  have hb := congrArg (fun b : ByteArray => b[0]!) h
  change (0 : UInt8) = 1 at hb
  contradiction

theorem trailingBytes_rejected :
    acceptTrailingBytes ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 0]⟩ ≠
      Model.Field.decodeBytesK? ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 0]⟩ := by decide

structure NegWitness where
  input : K
  exponent : wrongInverseExponent 2 ≠ Model.Field.inv 2
  zeroInverse : nonzeroInverseZero 0 ≠ Model.Field.inv 0
  byteOrder : reverseByteOrder 1 ≠ Model.Field.encodeBytesK 1
  trailing : acceptTrailingBytes ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 0]⟩ ≠
    Model.Field.decodeBytesK? ⟨#[1, 0, 0, 0, 0, 0, 0, 0, 0]⟩

def negWitness : NegWitness := ⟨2, wrongInverseExponent_rejected, nonzeroInverseZero_rejected,
  reverseByteOrder_rejected, trailingBytes_rejected⟩

def posWitness : PosWitness := positiveWitness

end LeanVmXmss.Tests.Field
