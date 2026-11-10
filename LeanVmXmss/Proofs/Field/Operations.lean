import Proofs.Field.Extension
import Model.Field.Operations

namespace LeanVmXmss.Proofs.Field

set_option maxRecDepth 20000
set_option maxHeartbeats 0

open Spec.Field (K E)

theorem pow_refines_spec (a : K) (n : Nat) :
    Model.Field.pow a n = Spec.Field.pow a n := by
  simp only [Model.Field.pow, Spec.Field.pow, funext (fun a => funext (mul_refines_spec a))]

theorem inv_refines_spec (a : K) : Model.Field.inv a = Spec.Field.inv a := by
  simp only [Model.Field.inv, Spec.Field.inv, funext (fun a => funext (mul_refines_spec a)),
    funext square_refines_spec]

theorem epow_refines_spec (a : E) (n : Nat) :
    Model.Field.epow a n = Spec.Field.epow a n := by
  simp only [Model.Field.epow, Spec.Field.epow, funext (fun a => funext (karatsuba_refines_spec a))]

theorem frobenius_refines_spec (a : E) : Model.Field.frobenius a = Spec.Field.frobenius a := rfl

theorem frobenius2_refines_spec (a : E) : Model.Field.frobenius2 a = Spec.Field.frobenius2 a := rfl

theorem norm_refines_spec (a : E) : Model.Field.norm a = Spec.Field.norm a := by
  simp only [Model.Field.norm, Spec.Field.norm, karatsuba_refines_spec,
    frobenius_refines_spec, frobenius2_refines_spec]

theorem einv_refines_spec (a : E) : Model.Field.einv a = Spec.Field.einv a := by
  simp only [Model.Field.einv, Spec.Field.einv, mulBase_refines_spec,
    karatsuba_refines_spec, frobenius_refines_spec, frobenius2_refines_spec,
    inv_refines_spec, norm_refines_spec]

theorem encodeBytesK_refines_spec (a : K) : Model.Field.encodeBytesK a = Spec.Field.encodeBytesK a := by
  simp [Model.Field.encodeBytesK, Spec.Field.encodeBytesK, List.range_succ]

theorem readLimb_refines_spec (b : ByteArray) (offset : Nat) :
    Model.Field.readLimb b offset = Spec.Field.readLimb b offset := by
  simp [Model.Field.readLimb, Spec.Field.readLimb, List.range_succ]

theorem decodeBytesK_refines_spec (b : ByteArray) : Model.Field.decodeBytesK? b = Spec.Field.decodeBytesK? b := by
  simp only [Model.Field.decodeBytesK?, Spec.Field.decodeBytesK?, readLimb_refines_spec]

theorem encodeBytesE_refines_spec (a : E) : Model.Field.encodeBytesE a = Spec.Field.encodeBytesE a := by
  simp only [Model.Field.encodeBytesE, Spec.Field.encodeBytesE, encodeBytesK_refines_spec]

theorem decodeBytesE_refines_spec (b : ByteArray) : Model.Field.decodeBytesE? b = Spec.Field.decodeBytesE? b := by
  simp only [Model.Field.decodeBytesE?, Spec.Field.decodeBytesE?, readLimb_refines_spec]

theorem scaled_refines_spec (a : E) : Model.Field.scaled a = Spec.Field.scaled a := by
  simp only [Model.Field.scaled, Spec.Field.scaled, karatsuba_refines_spec]

theorem scaledMul_refines_spec (s : Model.Field.Scaled) (a : E) :
    Model.Field.scaledMul s a = Spec.Field.scaledMul s a := by
  simp [Model.Field.scaledMul, Model.Field.scaledLimb, Spec.Field.scaledMul,
    List.finRange, Model.Field.eadd, Spec.Field.eadd, Spec.Field.add]
  rfl

theorem decodeBytesK_reject_length (b : ByteArray) (h : b.size ≠ 8) :
    Model.Field.decodeBytesK? b = none := by
  simp [Model.Field.decodeBytesK?, Spec.Field.decodeBytesK?, h]

theorem decodeBytesE_reject_length (b : ByteArray) (h : b.size ≠ 24) :
    Model.Field.decodeBytesE? b = none := by
  simp [Model.Field.decodeBytesE?, Spec.Field.decodeBytesE?, h]

theorem frobenius_order_three (a : E) :
    Model.Field.frobenius (Model.Field.frobenius (Model.Field.frobenius a)) = a := by
  cases a
  simp only [Model.Field.frobenius]
  congr 1 <;> apply UInt64.toBitVec_inj.mp <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp [Bool.xor_comm, Bool.xor_left_comm]

set_option maxRecDepth 20000 in
theorem inv_zero : Model.Field.inv 0 = 0 := by decide

set_option maxRecDepth 20000 in
theorem einv_zero : Model.Field.einv Spec.Field.zero = Spec.Field.zero := by decide

theorem encodeBytesK_length (a : K) : (Model.Field.encodeBytesK a).size = 8 := by
  simp [Model.Field.encodeBytesK, ByteArray.size]

theorem encodeBytesE_length (a : E) : (Model.Field.encodeBytesE a).size = 24 := by
  simp [Model.Field.encodeBytesE, Model.Field.encodeBytesK, ByteArray.size]

theorem mul_basis_one : ∀ i : Fin 64,
    Model.Field.mul 1 (UInt64.ofNat (2^i.val)) = UInt64.ofNat (2^i.val) := by decide

theorem mul_one_left (a : K) : Model.Field.mul 1 a = a := by
  apply UInt64.toBitVec_inj.mp
  exact xorLinear_eq_word (fun a => (Model.Field.mul 1 a).toBitVec) UInt64.toBitVec
    (by simp [mul_zero_right]) (by decide)
    (by intros; simp [mul_xor_right]) (by intros; simp)
    (fun i => congrArg UInt64.toBitVec (mul_basis_one i)) a

theorem emul_one_left (a : E) : Model.Field.karatsubaMul Spec.Field.one a = a := by
  rw [karatsuba_refines_polynomial]
  cases a
  simp [Model.Field.polynomialMul, Spec.Field.one, Spec.Field.embed,
    mul_one_left, mul_zero_left]

theorem emul_comm (a b : E) : Model.Field.karatsubaMul a b = Model.Field.karatsubaMul b a := by
  rw [karatsuba_refines_polynomial, karatsuba_refines_polynomial]
  simp only [Model.Field.polynomialMul]
  rw [mul_comm b.c0 a.c0, mul_comm b.c0 a.c1, mul_comm b.c0 a.c2,
    mul_comm b.c1 a.c0, mul_comm b.c1 a.c1, mul_comm b.c1 a.c2,
    mul_comm b.c2 a.c0, mul_comm b.c2 a.c1, mul_comm b.c2 a.c2]
  congr 1 <;> apply UInt64.toBitVec_inj.mp <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp [Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]

theorem emul_add_right (a b c : E) :
    Model.Field.karatsubaMul a (Model.Field.eadd b c) =
      Model.Field.eadd (Model.Field.karatsubaMul a b) (Model.Field.karatsubaMul a c) := by
  simp only [karatsuba_refines_polynomial, Model.Field.polynomialMul, Model.Field.eadd,
    mul_xor_right]
  congr 1 <;> apply UInt64.toBitVec_inj.mp <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp [Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]

theorem byte_reconstruct (n : Nat) (h : n < 18446744073709551616) :
    n % 256 + n / 256 % 256 * 256 + n / 65536 % 256 * 65536 +
      n / 16777216 % 256 * 16777216 + n / 4294967296 % 256 * 4294967296 +
      n / 1099511627776 % 256 * 1099511627776 +
      n / 281474976710656 % 256 * 281474976710656 +
      n / 72057594037927936 % 256 * 72057594037927936 = n := by
  omega

theorem read_encoded_limb (a : K) :
    Spec.Field.readLimb (Spec.Field.encodeBytesK a) 0 = a := by
  apply UInt64.toNat_inj.mp
  simp [Spec.Field.readLimb, Spec.Field.encodeBytesK, List.range_succ,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, byte_reconstruct,
    UInt64.toNat_lt_size]

theorem decodeBytesK_encodeBytesK (a : K) :
    Model.Field.decodeBytesK? (Model.Field.encodeBytesK a) = some a := by
  simp [decodeBytesK_refines_spec, encodeBytesK_refines_spec,
    Spec.Field.decodeBytesK?, show (Spec.Field.encodeBytesK a).size = 8 from encodeBytesK_length a,
    read_encoded_limb]

theorem read_encoded_extension (a : E) :
    Spec.Field.readLimb (Spec.Field.encodeBytesE a) 0 = a.c0 ∧
    Spec.Field.readLimb (Spec.Field.encodeBytesE a) 8 = a.c1 ∧
    Spec.Field.readLimb (Spec.Field.encodeBytesE a) 16 = a.c2 := by
  simp [Spec.Field.readLimb, Spec.Field.encodeBytesE, Spec.Field.encodeBytesK,
    ByteArray.append, List.range_succ, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    byte_reconstruct, UInt64.toNat_lt_size]

theorem decodeBytesE_encodeBytesE (a : E) :
    Model.Field.decodeBytesE? (Model.Field.encodeBytesE a) = some a := by
  simp only [decodeBytesE_refines_spec, encodeBytesE_refines_spec, Spec.Field.decodeBytesE?,
    show (Spec.Field.encodeBytesE a).size = 24 from encodeBytesE_length a,
    ↓reduceIte, (read_encoded_extension a).1, (read_encoded_extension a).2.1,
    (read_encoded_extension a).2.2]

end LeanVmXmss.Proofs.Field
