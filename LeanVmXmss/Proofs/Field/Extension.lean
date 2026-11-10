import Proofs.Field.Squares
import Proofs.Field.Quotient

namespace LeanVmXmss.Proofs.Field

open Spec.Field (K E)
open Model.Field

set_option maxRecDepth 20000

theorem add_refines_spec (a b : K) : add a b = Spec.Field.add a b := rfl

theorem eadd_refines_spec (a b : E) : eadd a b = Spec.Field.eadd a b := rfl

theorem polynomial_refines_spec (a b : E) : polynomialMul a b = Spec.Field.emul a b := by
  simp [polynomialMul, Spec.Field.emul, Spec.Field.extensionProduct, Spec.Field.extensionRemainder,
    Spec.Field.add, mul_refines_spec]

theorem karatsuba_refines_spec (a b : E) : karatsubaMul a b = Spec.Field.emul a b :=
  (karatsuba_refines_polynomial a b).trans (polynomial_refines_spec a b)

theorem mulBase_refines_polynomial (a : E) (b : K) : mulBase a b = polynomialMul a (Spec.Field.embed b) := by
  simp [mulBase, polynomialMul, Spec.Field.embed, mul_zero_right]

theorem mulBase_refines_spec (a : E) (b : K) : mulBase a b = Spec.Field.mulBase a b :=
  (mulBase_refines_polynomial a b).trans (polynomial_refines_spec a (Spec.Field.embed b))

theorem esquare_refines_polynomial (a : E) : esquare a = polynomialMul a a := by
  simp only [esquare, polynomialMul, square_refines_mul]
  rw [mul_comm a.c1 a.c0, mul_comm a.c2 a.c0, mul_comm a.c2 a.c1]
  congr 1 <;>
    apply UInt64.toBitVec_inj.mp <;>
    apply BitVec.eq_of_getLsbD_eq <;>
    intro i hi <;> simp [Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]

theorem esquare_refines_spec (a : E) : esquare a = Spec.Field.esquare a :=
  (esquare_refines_polynomial a).trans (polynomial_refines_spec a a)

theorem y_cube : Spec.Field.emul (Spec.Field.emul Spec.Field.y Spec.Field.y) Spec.Field.y =
    Spec.Field.eadd Spec.Field.y Spec.Field.one := by
  rw [← karatsuba_refines_spec, ← karatsuba_refines_spec]
  decide

theorem base_modulus_relation : Spec.Field.mul 0x8000000000000000 2 = 0x1B := by
  rw [← mul_refines_spec]
  decide

theorem embed_add (a b : K) :
    Spec.Field.eadd (Spec.Field.embed a) (Spec.Field.embed b) = Spec.Field.embed (Spec.Field.add a b) := by
  simp [Spec.Field.eadd, Spec.Field.embed, Spec.Field.add]

theorem embed_mul (a b : K) :
    Spec.Field.emul (Spec.Field.embed a) (Spec.Field.embed b) = Spec.Field.embed (Spec.Field.mul a b) := by
  rw [← polynomial_refines_spec, ← mul_refines_spec]
  simp [polynomialMul, Spec.Field.embed, mul_zero_left, mul_zero_right]

theorem embedBit_injective (a b : Bool) : Spec.Field.embedBit a = Spec.Field.embedBit b ↔ a = b := by
  cases a <;> cases b <;> decide

theorem embedBit_add (a b : Bool) :
    Spec.Field.add (Spec.Field.embedBit a) (Spec.Field.embedBit b) = Spec.Field.embedBit (a ^^ b) := by
  cases a <;> cases b <;> decide

theorem embedBit_mul (a b : Bool) :
    Spec.Field.mul (Spec.Field.embedBit a) (Spec.Field.embedBit b) = Spec.Field.embedBit (a && b) := by
  rw [← mul_refines_spec]
  cases a <;> cases b <;> decide

theorem modulus_hex : Spec.Field.modulus = 0x1000000000000001B := by decide

end LeanVmXmss.Proofs.Field
