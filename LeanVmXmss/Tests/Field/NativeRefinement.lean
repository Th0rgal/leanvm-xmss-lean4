import Tests.Field.Native
import Proofs.Field.NativeKernel

open LeanVmXmss.Model.Field
open LeanVmXmss.Proofs.Field

theorem xor_cancel_mid (a t c s : BitVec 64) :
    (a ^^^ t) ^^^ (c ^^^ (s ^^^ t)) = a ^^^ (c ^^^ s) := by
  rw [BitVec.xor_assoc a t, ← BitVec.xor_assoc t c (s ^^^ t),
    BitVec.xor_comm t c, BitVec.xor_assoc c t (s ^^^ t), ← BitVec.xor_assoc t s t,
    BitVec.xor_comm t s, BitVec.xor_assoc s t t, BitVec.xor_self, BitVec.xor_zero]

theorem step_sel (acc x b sh : UInt64) :
    (if ((b >>> sh) &&& 1) == 1 then acc ^^^ x else acc) =
      acc ^^^ nativeSelect x b sh := by
  apply UInt64.toBitVec_inj.mp
  have h1 : (((b >>> sh) &&& 1).toBitVec == (1 : BitVec 64)) = (((b >>> sh) &&& 1) == 1) := rfl
  rw [← h1]
  simp only [nativeSelect, UInt64.toBitVec_xor, UInt64.toBitVec_and,
    UInt64.toBitVec_sub, UInt64.toBitVec_shiftRight, UInt64.toBitVec_ofNat]
  rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  cases hb : b.toBitVec.getLsbD (sh.toNat % 64) <;> simp [hb]
  exact BitVec.and_allOnes.symm

theorem nat_toUInt64_mod64 (k : Nat) (hlt : k < 64) : k.toUInt64.toNat % 64 = k := by
  have hsize : k < UInt64.size := Nat.lt_trans hlt (by decide)
  simp [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hsize, Nat.mod_eq_of_lt hlt]

theorem clmul64_go_spec (a b : UInt64) :
    ∀ (k : Nat), k ≤ 64 → ∀ (acc : UInt64),
      (clmul64.go a b k acc).toBitVec =
        acc.toBitVec ^^^ ((clmul a b).setWidth 64 ^^^ (clmulSteps a.toBitVec b.toBitVec k).setWidth 64) := by
  intro k hk
  induction hrem : 64 - k generalizing k with
  | zero =>
    intro acc
    have hk64 : k = 64 := by omega
    subst hk64
    rw [clmul64.go]
    simp only [Nat.lt_irrefl, ↓reduceDIte]
    have hc : clmul a b = clmulSteps a.toBitVec b.toBitVec 64 := rfl
    rw [hc, BitVec.xor_self, BitVec.xor_zero]
  | succ m ih =>
    intro acc
    have hlt : k < 64 := by omega
    rw [clmul64.go]
    simp only [hlt, ↓reduceDIte, step_sel]
    have hk1 : k + 1 ≤ 64 := by omega
    have hrem1 : 64 - (k + 1) = m := by omega
    rw [ih (k + 1) hk1 hrem1]
    have hsh_mod : k.toUInt64.toNat % 64 = k := nat_toUInt64_mod64 k hlt
    have hbv_mod : (k.toUInt64.toBitVec % 64).toNat = k := by
      rw [BitVec.toNat_umod]
      exact hsh_mod
    have hshift : (a <<< k.toUInt64).toBitVec = (a.toBitVec.setWidth 128 <<< k).setWidth 64 := by
      simp only [UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq', hbv_mod,
        BitVec.setWidth_shiftLeft_of_le (by decide : 64 ≤ 128),
        BitVec.setWidth_setWidth_of_le a.toBitVec (by decide : 64 ≤ 128), BitVec.setWidth_eq]
    have hresize (p : Bool) (x : BitVec 128) :
        (if p then x else 0).setWidth 64 = if p then x.setWidth 64 else 0 := by
      cases p <;> rfl
    simp only [clmulSteps.succ, UInt64.toBitVec_xor, nativeSelect_toBitVec, hsh_mod, hshift,
      BitVec.setWidth_xor, hresize]
    exact xor_cancel_mid _ _ _ _

theorem clmul64_eq_nativeClmulLo (a b : UInt64) :
    clmul64 a b = nativeClmulLo a b := by
  apply UInt64.toBitVec_inj.mp
  unfold clmul64
  rw [clmul64_go_spec a b 0 (by omega) 0, nativeClmulLo_correct]
  simp [clmulSteps.zero]

theorem clmul64Hi_go_spec (a b : UInt64) :
    ∀ (k : Nat), 1 ≤ k → k ≤ 64 → ∀ (acc : UInt64),
      (clmul64Hi.go a b k acc).toBitVec =
        acc.toBitVec ^^^ (((clmul a b >>> 64).setWidth 64) ^^^ ((clmulSteps a.toBitVec b.toBitVec k >>> 64).setWidth 64)) := by
  intro k hk0 hk
  induction hrem : 64 - k generalizing k with
  | zero =>
    intro acc
    have hk64 : k = 64 := by omega
    subst hk64
    rw [clmul64Hi.go]
    simp only [Nat.lt_irrefl, ↓reduceDIte]
    have hc : clmul a b = clmulSteps a.toBitVec b.toBitVec 64 := rfl
    rw [hc, BitVec.xor_self, BitVec.xor_zero]
  | succ m ih =>
    intro acc
    have hlt : k < 64 := by omega
    rw [clmul64Hi.go]
    simp only [hlt, ↓reduceDIte, step_sel]
    have hk1_0 : 1 ≤ k + 1 := by omega
    have hk1 : k + 1 ≤ 64 := by omega
    have hrem1 : 64 - (k + 1) = m := by omega
    rw [ih (k + 1) hk1_0 hk1 hrem1]
    have hsh_mod : k.toUInt64.toNat % 64 = k := nat_toUInt64_mod64 k hlt
    have hsub_mod : ((64 : UInt64) - k.toUInt64).toNat % 64 = 64 - k := by
      have hf : ∀ j : Fin 64, 1 ≤ j.val → ((64 : UInt64) - j.val.toUInt64).toNat % 64 = 64 - j.val := by decide
      exact hf ⟨k, hlt⟩ hk0
    have hbv_sub_mod : (((64 : UInt64) - k.toUInt64).toBitVec % 64).toNat = 64 - k := by
      rw [BitVec.toNat_umod]
      exact hsub_mod
    have hshift : (a >>> ((64 : UInt64) - k.toUInt64)).toBitVec =
        ((a.toBitVec.setWidth 128 <<< k) >>> 64).setWidth 64 := by
      have high := nativeHighShift a.toBitVec ⟨k, hlt⟩
      have hk_ne : k ≠ 0 := by omega
      simp only [hk_ne, ↓reduceIte] at high
      rw [high]
      simp only [UInt64.toBitVec_shiftRight, BitVec.ushiftRight_eq', hbv_sub_mod]
    have hright (p : Bool) (x : BitVec 128) :
        ((if p then x else 0) >>> 64).setWidth 64 = if p then (x >>> 64).setWidth 64 else 0 := by
      cases p
      · exact (show ((0 : BitVec 128) >>> 64).setWidth 64 = 0 by decide)
      · rfl
    simp only [clmulSteps.succ, BitVec.ushiftRight_xor_distrib, UInt64.toBitVec_xor,
      nativeSelect_toBitVec, hsh_mod, hshift, BitVec.setWidth_xor, hright]
    exact xor_cancel_mid _ _ _ _

theorem clmul64Hi_eq_nativeClmulHi (a b : UInt64) :
    clmul64Hi a b = nativeClmulHi a b := by
  apply UInt64.toBitVec_inj.mp
  unfold clmul64Hi
  rw [clmul64Hi_go_spec a b 1 (by omega) (by omega) 0, nativeClmulHi_correct]
  have h1 : ((clmulSteps a.toBitVec b.toBitVec 1 >>> 64).setWidth 64) = 0 := by
    have high := nativeHighShift a.toBitVec ⟨0, by decide⟩
    simp only [↓reduceIte, BitVec.shiftLeft_zero] at high
    rw [clmulSteps.succ, clmulSteps.zero]
    cases b.toBitVec.getLsbD 0
    · exact (show (((0 : BitVec 128) ^^^ 0) >>> 64).setWidth 64 = 0 by decide)
    · simp only [↓reduceIte, BitVec.shiftLeft_zero]
      have hz : (0 : BitVec 128) ^^^ BitVec.setWidth 128 a.toBitVec = BitVec.setWidth 128 a.toBitVec := BitVec.zero_xor
      rw [hz]
      exact high
  rw [h1]
  simp

theorem nativeTestMul_correct (a b : UInt64) :
    nativeTestMul a b = LeanVmXmss.Model.Field.nativeMul a b := by
  simp only [nativeTestMul, nativeTestReduce, LeanVmXmss.Model.Field.nativeMul,
    LeanVmXmss.Model.Field.nativeReduce, clmul64_eq_nativeClmulLo, clmul64Hi_eq_nativeClmulHi]

theorem nativeTestSquare_correct (a : UInt64) :
    nativeTestSquare a = LeanVmXmss.Model.Field.nativeSquare a := by
  simp only [nativeTestSquare, LeanVmXmss.Model.Field.nativeSquare, nativeTestMul_correct]

theorem nativeMulHop5_correct (a b : UInt64) :
    nativeMulHop5 a b = LeanVmXmss.Model.Field.nativeMul a b := by
  unfold nativeMulHop5 nativeMulHop4 nativeMulHop3 nativeMulHop2 nativeMulHop1
  exact nativeTestMul_correct a b

theorem nativeSqHop_correct (a : UInt64) :
    nativeSqHop a = LeanVmXmss.Model.Field.nativeSquare a := by
  unfold nativeSqHop LeanVmXmss.Model.Field.nativeSquare
  exact nativeMulHop5_correct a a

theorem nativeTestSquare3_correct (a : UInt64) :
    nativeTestSquare3 a = LeanVmXmss.Model.Field.nativeSquare3 a := by
  simp only [nativeTestSquare3, LeanVmXmss.Model.Field.nativeSquare3, nativeSqHop_correct]

theorem nativeTestSquare6_correct (a : UInt64) :
    nativeTestSquare6 a = LeanVmXmss.Model.Field.nativeSquare6 a := by
  simp only [nativeTestSquare6, LeanVmXmss.Model.Field.nativeSquare6, nativeTestSquare3_correct]

theorem nativeTestSquare12_correct (a : UInt64) :
    nativeTestSquare12 a = LeanVmXmss.Model.Field.nativeSquare12 a := by
  simp only [nativeTestSquare12, LeanVmXmss.Model.Field.nativeSquare12, nativeTestSquare6_correct]

theorem nativeTestSquare24_correct (a : UInt64) :
    nativeTestSquare24 a = LeanVmXmss.Model.Field.nativeSquare24 a := by
  simp only [nativeTestSquare24, LeanVmXmss.Model.Field.nativeSquare24, nativeTestSquare12_correct]

theorem nativeTestInv_correct (a : UInt64) :
    nativeTestInv a = LeanVmXmss.Model.Field.nativeInv a := by
  simp only [nativeTestInv, LeanVmXmss.Model.Field.nativeInv,
    LeanVmXmss.Model.Field.nativeInv63, LeanVmXmss.Model.Field.nativeInv60,
    LeanVmXmss.Model.Field.nativeInv48, LeanVmXmss.Model.Field.nativeInv24,
    LeanVmXmss.Model.Field.nativeInv12, LeanVmXmss.Model.Field.nativeInv6,
    LeanVmXmss.Model.Field.nativeInv3, nativeTestSquare24_correct,
    nativeTestSquare12_correct, nativeTestSquare6_correct, nativeTestSquare3_correct,
    nativeSqHop_correct, nativeMulHop5_correct]

theorem nativeTestKaratsuba0_correct (a0 a1 a2 b0 b1 b2 : UInt64) :
    nativeTestKaratsuba0 a0 a1 a2 b0 b1 b2 =
      LeanVmXmss.Model.Field.nativeKaratsuba0 a0 a1 a2 b0 b1 b2 := by
  simp only [nativeTestKaratsuba0, LeanVmXmss.Model.Field.nativeKaratsuba0, nativeMulHop5_correct]

theorem nativeTestKaratsuba1_correct (a0 a1 a2 b0 b1 b2 : UInt64) :
    nativeTestKaratsuba1 a0 a1 a2 b0 b1 b2 =
      LeanVmXmss.Model.Field.nativeKaratsuba1 a0 a1 a2 b0 b1 b2 := by
  simp only [nativeTestKaratsuba1, LeanVmXmss.Model.Field.nativeKaratsuba1, nativeMulHop5_correct]

theorem nativeTestKaratsuba2_correct (a0 a1 a2 b0 b1 b2 : UInt64) :
    nativeTestKaratsuba2 a0 a1 a2 b0 b1 b2 =
      LeanVmXmss.Model.Field.nativeKaratsuba2 a0 a1 a2 b0 b1 b2 := by
  simp only [nativeTestKaratsuba2, LeanVmXmss.Model.Field.nativeKaratsuba2, nativeMulHop5_correct]
