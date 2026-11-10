import Proofs.Field.Frobenius

namespace LeanVmXmss.Proofs.Field

open Spec.Field (K E squareNWith)
open Model.Field

set_option maxRecDepth 20000
set_option maxHeartbeats 200000

def recoverTable : Array K := #[
  1858076378458151938, 9561900855309385444, 9561900855309385446, 11347809597230670838,
  9561900855309385442, 4018460688368531344, 11347809597230670846, 281517943493500,
  9561900855309385458, 3931244771709608444, 4018460688368531376, 1858076305444036428,
  11347809597230670782, 3336501280695469424, 281517943493628, 9580096982618358322,
  9561900855309385714, 4018742189131883772, 3931244771709608956, 12932019878818011918,
  4018460688368530352, 9650468784525026546, 1858076305444034380, 12303816589915979790,
  11347809597230674878, 9563028610608019698, 3336501280695477616, 1427071658708988,
  281517943510012, 12541401399658572814, 9580096982618391090, 9223372039002259470,
  9561900855309451250, 12931737355851385214, 4018742189132014844, 11254603532465727182,
  3931244771709346812, 18546751265078896, 12932019878817487630, 9635927528439764686,
  4018460688367481776, 1863711165003320140, 9650468784527123698, 1841373461176552128,
  1858076305448228684, 339958567963100336, 12303816589907591182, 9241497849131167678,
  11347809597213897662, 1783765537390569292, 9563028610641574130, 12319055597872112254,
  3336501280628368752, 3623343634930477708, 1427071792926716, 13116755630313467918,
  281518211945468, 2165389375334596604, 12541401399121701902, 1012186353053232128,
  9580096983692132914, 0, 9223372036854775822, 13853606100407680462]

def recoverSteps (a : K) : Nat → K :=
  Nat.rec 0 (fun n prev => prev ^^^ if a.toBitVec.getLsbD n then recoverTable[n]! else 0)

@[simp] theorem recoverSteps.zero (a : K) : recoverSteps a 0 = 0 := rfl

@[simp] theorem recoverSteps.succ (a : K) (n : Nat) :
    recoverSteps a (n + 1) = recoverSteps a n ^^^ if a.toBitVec.getLsbD n then recoverTable[n]! else 0 := rfl

theorem recoverSteps_zero (n : Nat) : recoverSteps 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [recoverSteps.succ, ih]

theorem recoverSteps_xor (a b : K) (n : Nat) : recoverSteps (a ^^^ b) n = recoverSteps a n ^^^ recoverSteps b n := by
  induction n with
  | zero => simp only [recoverSteps.zero]; decide
  | succ n ih =>
    simp only [recoverSteps.succ, ih, UInt64.toBitVec_xor, BitVec.getLsbD_xor]
    cases ha : a.toBitVec.getLsbD n <;> cases hb : b.toBitVec.getLsbD n <;>
      simp [kxor_assoc, kxor_comm, kxor_left_comm]

theorem recover_basis : ∀ i : Fin 64,
    recoverSteps (square (UInt64.ofNat (2^i.val)) ^^^ UInt64.ofNat (2^i.val)) 64 =
      UInt64.ofNat (2^i.val) ^^^ (UInt64.ofNat (2^i.val) &&& 1) := by decide

theorem recover_identity (a : K) : recoverSteps (square a ^^^ a) 64 = a ^^^ (a &&& 1) := by
  apply xorLinear_eq_uint64 _ _
    (by simp [square_zero, recoverSteps_zero]) (by decide)
    (by intros; simp only [square_xor, kxor_assoc, kxor_comm, kxor_left_comm, recoverSteps_xor])
    (by
      intro a b
      apply UInt64.toBitVec_inj.mp
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [UInt64.toBitVec_xor, UInt64.toBitVec_and, BitVec.getLsbD_xor, BitVec.getLsbD_and]
      cases a.toBitVec.getLsbD i <;> cases b.toBitVec.getLsbD i <;>
        cases (1 : K).toBitVec.getLsbD i <;> decide)
    recover_basis a

theorem square_fixed (a : K) (h : square a = a) : a = 0 ∨ a = 1 := by
  have hr := recover_identity a
  rw [h] at hr
  have hz : a ^^^ (a &&& 1) = 0 := by simpa [recoverSteps_zero] using hr.symm
  have he : a = a &&& 1 := by
    apply UInt64.toBitVec_inj.mp
    have hb := congrArg UInt64.toBitVec hz
    simpa using (BitVec.xor_eq_zero_iff.mp hb)
  have hn : (a &&& 1).toNat ≤ 1 := by
    change a.toNat &&& 1 ≤ 1
    exact Nat.and_le_right
  have ha : a.toNat ≤ 1 := by simpa [← he] using hn
  have hh : a.toNat = 0 ∨ a.toNat = 1 := by omega
  rcases hh with hh | hh
  · left; exact UInt64.toNat_inj.mp hh
  · right; exact UInt64.toNat_inj.mp hh

theorem pow_double (a : K) (n : Nat) : square (pow a n) = pow a (n + n) := by
  rw [square_refines_mul, ← pow_add]

theorem pow_mod_period (a : K) (n : Nat) :
    pow a (n + (2^64 - 1) + 1) = pow a (n + 1) := by
  have hq : pow a (2^64) = a := by
    have h := squareN_pow_base a 1 64
    simpa only [pow_one, Nat.one_mul, squareN_order] using h.symm
  rw [show n + (2^64 - 1) + 1 = n + 2^64 by omega, pow_add, hq]
  rfl

theorem mul_inv_nonzero (a : K) (h : a ≠ 0) : mul a (inv a) = 1 := by
  let t := pow a (2^64 - 1)
  have ht : square t = t := by
    change square (pow a (2^64 - 1)) = pow a (2^64 - 1)
    rw [pow_double]
    have hp := pow_mod_period a (2^64 - 2 : Nat)
    exact hp
  have ha : mul t a = a := by
    change pow a (2^64 - 1 + 1) = a
    have hh := squareN_pow_base a 1 64
    simpa only [pow_one, Nat.one_mul, squareN_order] using hh.symm
  have ht1 : t = 1 := by
    rcases square_fixed t ht with hz | ho
    · rw [hz, mul_zero_left] at ha
      exact False.elim (h ha.symm)
    · exact ho
  rw [inv_eq_pow, mul_comm]
  change pow a ((2^64 - 2) + 1) = 1
  exact ht1

end LeanVmXmss.Proofs.Field
