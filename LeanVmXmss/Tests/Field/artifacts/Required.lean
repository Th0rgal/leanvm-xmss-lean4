import Proofs.Field.Windows
open LeanVmXmss.Spec.Field (K E)
theorem required_mul_assoc (a b c : K) : LeanVmXmss.Model.Field.mul (LeanVmXmss.Model.Field.mul a b) c = LeanVmXmss.Model.Field.mul a (LeanVmXmss.Model.Field.mul b c) := by exact LeanVmXmss.Proofs.Field.mul_assoc a b c 
theorem required_emul_assoc (a b c : E) : LeanVmXmss.Model.Field.karatsubaMul (LeanVmXmss.Model.Field.karatsubaMul a b) c = LeanVmXmss.Model.Field.karatsubaMul a (LeanVmXmss.Model.Field.karatsubaMul b c) := by exact LeanVmXmss.Proofs.Field.emul_assoc a b c 
theorem required_mul_one_left (a : K) : LeanVmXmss.Model.Field.mul 1 a = a := by exact LeanVmXmss.Proofs.Field.mul_one_left a 
theorem required_emul_one_left (a : E) : LeanVmXmss.Model.Field.karatsubaMul LeanVmXmss.Spec.Field.one a = a := by exact LeanVmXmss.Proofs.Field.emul_one_left a 
theorem required_emul_comm (a b : E) : LeanVmXmss.Model.Field.karatsubaMul a b = LeanVmXmss.Model.Field.karatsubaMul b a := by exact LeanVmXmss.Proofs.Field.emul_comm a b 
theorem required_emul_add_right (a b c : E) : LeanVmXmss.Model.Field.karatsubaMul a (LeanVmXmss.Model.Field.eadd b c) = LeanVmXmss.Model.Field.eadd (LeanVmXmss.Model.Field.karatsubaMul a b) (LeanVmXmss.Model.Field.karatsubaMul a c) := by exact LeanVmXmss.Proofs.Field.emul_add_right a b c 
theorem required_mul_inv_nonzero (a : K) (h : a ≠ 0) : LeanVmXmss.Model.Field.mul a (LeanVmXmss.Model.Field.inv a) = 1 := by exact LeanVmXmss.Proofs.Field.mul_inv_nonzero a  h 
theorem required_emul_inv_nonzero (a : E) (h : a ≠ LeanVmXmss.Spec.Field.zero) : LeanVmXmss.Model.Field.karatsubaMul a (LeanVmXmss.Model.Field.einv a) = LeanVmXmss.Spec.Field.one := by exact LeanVmXmss.Proofs.Field.emul_inv_nonzero a  h 
theorem required_decodeBytesK_encodeBytesK (a : K) : LeanVmXmss.Model.Field.decodeBytesK? (LeanVmXmss.Model.Field.encodeBytesK a) = some a := by exact LeanVmXmss.Proofs.Field.decodeBytesK_encodeBytesK a 
theorem required_decodeBytesE_encodeBytesE (a : E) : LeanVmXmss.Model.Field.decodeBytesE? (LeanVmXmss.Model.Field.encodeBytesE a) = some a := by exact LeanVmXmss.Proofs.Field.decodeBytesE_encodeBytesE a 
theorem required_encodeBytesK_decodeBytesK (b : ByteArray) (a : K) (h : LeanVmXmss.Model.Field.decodeBytesK? b = some a) : LeanVmXmss.Model.Field.encodeBytesK a = b := by exact LeanVmXmss.Proofs.Field.encodeBytesK_decodeBytesK b  a  h 
theorem required_encodeBytesE_decodeBytesE (b : ByteArray) (a : E) (h : LeanVmXmss.Model.Field.decodeBytesE? b = some a) : LeanVmXmss.Model.Field.encodeBytesE a = b := by exact LeanVmXmss.Proofs.Field.encodeBytesE_decodeBytesE b  a  h 
theorem required_frobenius_eq_pow (a : E) : LeanVmXmss.Model.Field.frobenius a = LeanVmXmss.Model.Field.epow a (2^64) := by exact LeanVmXmss.Proofs.Field.frobenius_eq_pow a 
theorem required_frobenius2_eq_pow (a : E) : LeanVmXmss.Model.Field.frobenius2 a = LeanVmXmss.Model.Field.epow a (2^128) := by exact LeanVmXmss.Proofs.Field.frobenius2_eq_pow a 
theorem required_norm_in_base (a : E) : LeanVmXmss.Model.Field.karatsubaMul a (LeanVmXmss.Model.Field.karatsubaMul (LeanVmXmss.Model.Field.frobenius a) (LeanVmXmss.Model.Field.frobenius2 a)) = LeanVmXmss.Spec.Field.embed (LeanVmXmss.Model.Field.norm a) := by exact LeanVmXmss.Proofs.Field.norm_in_base a 
theorem required_inv_eq_pow (a : K) : LeanVmXmss.Model.Field.inv a = LeanVmXmss.Model.Field.pow a (2^64 - 2) := by exact LeanVmXmss.Proofs.Field.inv_eq_pow a 
theorem required_scaledMul_correct (a b : E) : LeanVmXmss.Model.Field.scaledMul (LeanVmXmss.Model.Field.scaled a) b = LeanVmXmss.Model.Field.karatsubaMul a b := by exact LeanVmXmss.Proofs.Field.scaledMul_correct a b 
