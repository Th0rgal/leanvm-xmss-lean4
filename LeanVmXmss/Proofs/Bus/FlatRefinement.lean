import Model.Bus.Flat
import Proofs.Bus.Refinement

namespace LeanVmXmss.Proofs.Bus

open Spec.Field (K E zero one)
open Spec.Layout
open Spec.Witness
open LeanVmXmss.Model.Bus
open LeanVmXmss.Model.Field
open LeanVmXmss.Model.Pcs.Ntt (foldRange foldRangeLoop)

set_option maxRecDepth 20000
set_option maxHeartbeats 400000

theorem planarEadd_refines (a b : E) : planarEadd a b = Model.Field.eadd a b := by
  simp only [planarEadd, planarEadd0, planarEadd1, planarEadd2, Model.Field.eadd]

private theorem uint64_xor_comm_local (x y : UInt64) : x ^^^ y = y ^^^ x := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp [Bool.xor_comm]

private theorem uint64_xor_left_comm_local (x y z : UInt64) :
    x ^^^ (y ^^^ z) = y ^^^ (x ^^^ z) := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp [Bool.xor_left_comm]

private theorem uint64_xor_assoc_local (x y z : UInt64) :
    (x ^^^ y) ^^^ z = x ^^^ (y ^^^ z) := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp

private theorem uint64_xor_cancel_left_local (x y : UInt64) : x ^^^ (x ^^^ y) = y := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp

private theorem uint64_xor_zero_right_local (x : UInt64) : x ^^^ 0 = x := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp

private theorem uint64_xor_zero_left_local (x : UInt64) : 0 ^^^ x = x := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp

theorem planarEmul_refines (a b : E) : planarEmul a b = nativeKaratsuba a b := by
  simp only [planarEmul, nativeKaratsuba, nativeKaratsuba0, nativeKaratsuba1, nativeKaratsuba2,
    uint64_xor_assoc_local, uint64_xor_comm_local, uint64_xor_left_comm_local,
    uint64_xor_cancel_left_local]

theorem planarMulBase_refines (a : E) (k : K) :
    planarMulBase a k = nativeMulBase a k := by
  simp only [planarMulBase, planarMulBase0, planarMulBase1, planarMulBase2, nativeMulBase]

theorem decode_encode_planar_empty :
    decodePlanarE (encodePlanarE (#[] : Array E)) = #[] := by
  simp [decodePlanarE, encodePlanarE, planarEEmpty, foldRange, foldRangeLoop]

theorem eqTable_flat_refines_empty :
    decodePlanarE (eqTableFlat (#[] : Array E)) = eqTable #[] := rfl

private theorem planarEadd_eq : planarEadd = Model.Field.eadd := by
  funext a b
  exact planarEadd_refines a b

private theorem planarEmul_eq : planarEmul = nativeKaratsuba := by
  funext a b
  exact planarEmul_refines a b

private theorem planarMulBase_eq : planarMulBase = nativeMulBase := by
  funext a k
  exact planarMulBase_refines a k

private theorem eadd_eq_spec_bus : Model.Field.eadd = Spec.Field.eadd := rfl

private theorem eadd_assoc_model (a b c : E) :
    Model.Field.eadd (Model.Field.eadd a b) c = Model.Field.eadd a (Model.Field.eadd b c) := by
  simp only [Model.Field.eadd, uint64_xor_assoc_local]

private theorem eadd_zero_right_model (a : E) : Model.Field.eadd a zero = a := by
  cases a
  simp only [Model.Field.eadd, zero, uint64_xor_zero_right_local]

private theorem eadd_zero_left_model (a : E) : Model.Field.eadd zero a = a := by
  cases a
  simp only [Model.Field.eadd, zero, uint64_xor_zero_left_local]

private theorem addMsg4_assoc (a b c : E × E × E × E) :
    addMsg4 (addMsg4 a b) c = addMsg4 a (addMsg4 b c) := by
  rcases a with ⟨a1, a2, a3, a4⟩
  rcases b with ⟨b1, b2, b3, b4⟩
  rcases c with ⟨c1, c2, c3, c4⟩
  unfold addMsg4 Spec.Bus.addMsg4
  simp only [← eadd_eq_spec_bus, eadd_assoc_model]

private theorem addMsg4_zero_right (a : E × E × E × E) :
    addMsg4 a (zero, zero, zero, zero) = a := by
  rcases a with ⟨a1, a2, a3, a4⟩
  unfold addMsg4 Spec.Bus.addMsg4
  simp only [← eadd_eq_spec_bus, eadd_zero_right_model]

private theorem pair_eadd_assoc (a b c : E × E) :
    (Model.Field.eadd (Model.Field.eadd a.1 b.1) c.1,
      Model.Field.eadd (Model.Field.eadd a.2 b.2) c.2) =
    (Model.Field.eadd a.1 (Model.Field.eadd b.1 c.1),
      Model.Field.eadd a.2 (Model.Field.eadd b.2 c.2)) := by
  simp only [eadd_assoc_model]

private theorem pair_eadd_zero_right (a : E × E) :
    (Model.Field.eadd a.1 zero, Model.Field.eadd a.2 zero) = a := by
  rcases a with ⟨a1, a2⟩
  simp only [eadd_zero_right_model]

private theorem task_spawn_get {α : Type} (f : Unit → α) :
    (Task.spawn f).get = f () := rfl

private theorem foldRangeLoop_split {α : Type} (f : α → Nat → α) (a b base : Nat) (init : α) :
    foldRangeLoop f (a + b) base init =
      foldRangeLoop f b (base + a) (foldRangeLoop f a base init) := by
  simp only [foldRangeLoop, Fin.foldl_add]
  congr 1
  funext acc k
  simp [Fin.val_natAdd, Nat.add_assoc]

private theorem foldRangeLoop_monoid {α : Type} (op : α → α → α) (z : α)
    (hassoc : ∀ x y w, op (op x y) w = op x (op y w))
    (hzero : ∀ x, op x z = x)
    (g : Nat → α) (acc : α) (b l : Nat) :
    op acc (foldRangeLoop (fun s i => op s (g i)) l b z) =
      foldRangeLoop (fun s i => op s (g i)) l b acc := by
  induction l generalizing acc with
  | zero =>
    simp [foldRangeLoop, hzero]
  | succ k ih =>
    unfold foldRangeLoop at ih ⊢
    simp only [Fin.foldl_succ_last, Fin.val_castSucc, ← hassoc, ih acc]

private theorem parTreeReduce_monoid {α : Type} (op : α → α → α) (z : α)
    (hassoc : ∀ x y w, op (op x y) w = op x (op y w))
    (hzero : ∀ x, op x z = x)
    (g : Nat → α) (depth minChunk base len : Nat) :
    parTreeReduce depth minChunk base len
      (fun b l => foldRangeLoop (fun s i => op s (g i)) l b z)
      op =
    foldRangeLoop (fun s i => op s (g i)) len base z := by
  induction depth generalizing base len with
  | zero => rfl
  | succ d ih =>
    change (if len < minChunk then _ else _) = _
    split
    · rfl
    · dsimp only []
      change op (parTreeReduce d minChunk base (len / 2) _ op)
        (parTreeReduce d minChunk (base + len / 2) (len - len / 2) _ op) = _
      rw [ih, ih, foldRangeLoop_monoid op z hassoc hzero,
        ← foldRangeLoop_split, Nat.add_sub_of_le (Nat.div_le_self len 2)]

private theorem foldRangeLoop_push_empty {α : Type} (g : Nat → α) (b l cap1 cap2 : Nat) :
    foldRangeLoop (fun out i => out.push (g i)) l b (Array.emptyWithCapacity cap1) =
      foldRangeLoop (fun out i => out.push (g i)) l b (Array.emptyWithCapacity cap2) := rfl

private theorem foldRangeLoop_push_append {α : Type} (g : Nat → α) (acc : Array α) (b l cap : Nat) :
    acc ++ foldRangeLoop (fun out i => out.push (g i)) l b (Array.emptyWithCapacity cap) =
      foldRangeLoop (fun out i => out.push (g i)) l b acc := by
  induction l generalizing acc with
  | zero =>
    simp [foldRangeLoop]
  | succ k ih =>
    simp only [foldRangeLoop, Fin.foldl_succ_last, Array.append_push]
    congr 1
    exact ih acc

private theorem parTreeReduce_push_eq {α : Type} (g : Nat → α) (depth minChunk base len : Nat) :
    parTreeReduce depth minChunk base len
      (fun b l => foldRangeLoop (fun out i => out.push (g i)) l b (Array.emptyWithCapacity l))
      Array.append =
    foldRangeLoop (fun out i => out.push (g i)) len base (Array.emptyWithCapacity len) := by
  induction depth generalizing base len with
  | zero => rfl
  | succ d ih =>
    change (if len < minChunk then _ else _) = _
    split
    · rfl
    · dsimp only []
      change HAppend.hAppend (parTreeReduce d minChunk base (len / 2) _ Array.append)
        (parTreeReduce d minChunk (base + len / 2) (len - len / 2) _ Array.append) = _
      rw [ih, ih, foldRangeLoop_push_append, foldRangeLoop_push_empty _ base (len / 2) (len / 2) len,
        ← foldRangeLoop_split, Nat.add_sub_of_le (Nat.div_le_self len 2)]

private theorem foldRangeLoop_push4_empty {α : Type} (g0 g1 g2 g3 : Nat → α)
    (b l cap1 cap2 : Nat) :
    foldRangeLoop (fun out i => (((out.push (g0 i)).push (g1 i)).push (g2 i)).push (g3 i))
      l b (Array.emptyWithCapacity cap1) =
    foldRangeLoop (fun out i => (((out.push (g0 i)).push (g1 i)).push (g2 i)).push (g3 i))
      l b (Array.emptyWithCapacity cap2) := rfl

private theorem foldRangeLoop_push4_append {α : Type} (g0 g1 g2 g3 : Nat → α)
    (acc : Array α) (b l cap : Nat) :
    acc ++ foldRangeLoop (fun out i => (((out.push (g0 i)).push (g1 i)).push (g2 i)).push (g3 i))
      l b (Array.emptyWithCapacity cap) =
    foldRangeLoop (fun out i => (((out.push (g0 i)).push (g1 i)).push (g2 i)).push (g3 i))
      l b acc := by
  induction l generalizing acc with
  | zero =>
    simp [foldRangeLoop]
  | succ k ih =>
    simp only [foldRangeLoop, Fin.foldl_succ_last, Array.append_push]
    congr 4
    exact ih acc

private theorem parTreeReduce_push4_eq {α : Type} (g0 g1 g2 g3 : Nat → α)
    (depth minChunk base len : Nat) :
    parTreeReduce depth minChunk base len
      (fun b l =>
        foldRangeLoop (fun out i => (((out.push (g0 i)).push (g1 i)).push (g2 i)).push (g3 i))
          l b (Array.emptyWithCapacity (4 * l)))
      Array.append =
    foldRangeLoop (fun out i => (((out.push (g0 i)).push (g1 i)).push (g2 i)).push (g3 i))
      len base (Array.emptyWithCapacity (4 * len)) := by
  induction depth generalizing base len with
  | zero => rfl
  | succ d ih =>
    change (if len < minChunk then _ else _) = _
    split
    · rfl
    · dsimp only []
      change HAppend.hAppend (parTreeReduce d minChunk base (len / 2) _ Array.append)
        (parTreeReduce d minChunk (base + len / 2) (len - len / 2) _ Array.append) = _
      rw [ih, ih, foldRangeLoop_push4_append,
        foldRangeLoop_push4_empty g0 g1 g2 g3 base (len / 2) (4 * (len / 2)) (4 * len),
        ← foldRangeLoop_split, Nat.add_sub_of_le (Nat.div_le_self len 2)]

private theorem foldRangeLoop_push_size {α : Type} (g : Nat → α) (b l : Nat) (acc : Array α) :
    (foldRangeLoop (fun out i => out.push (g i)) l b acc).size = acc.size + l := by
  induction l generalizing acc with
  | zero => simp [foldRangeLoop]
  | succ k ih =>
    unfold foldRangeLoop at ih ⊢
    simp only [Fin.foldl_succ_last, Fin.val_castSucc, Array.size_push, ih acc]
    omega

private theorem foldRangeLoop_push_getElem {α : Type} (g : Nat → α) (b l : Nat) (acc : Array α)
    (j : Nat) (hj : j < acc.size + l) :
    (foldRangeLoop (fun out i => out.push (g i)) l b acc)[j]'(by
      rw [foldRangeLoop_push_size]
      exact hj) =
      if hlt : j < acc.size then acc[j] else g (b + (j - acc.size)) := by
  induction l generalizing acc with
  | zero =>
    have hlt : j < acc.size := by omega
    simp [foldRangeLoop, hlt]
  | succ k ih =>
    unfold foldRangeLoop at ih ⊢
    simp only [Fin.foldl_succ_last, Fin.val_castSucc, Fin.val_last]
    have hsz : (Fin.foldl k (fun x1 (x2 : Fin k) => x1.push (g (b + ↑x2))) acc).size =
        acc.size + k :=
      foldRangeLoop_push_size g b k acc
    rw [Array.getElem_push]
    split
    · next hlt_k =>
      exact ih acc (by omega)
    · next hnlt_k =>
      have heq : j = acc.size + k := by omega
      subst heq
      have hnlt : ¬ acc.size + k < acc.size := by omega
      simp [hnlt]

private theorem precomputed_array_getD {α : Type} (g : Nat → α) (d : α) (n z : Nat) (hz : z < n) :
    ((foldRangeLoop (fun out i => out.push (g i)) n 0 (Array.emptyWithCapacity n))[z]?.getD d) =
      g z := by
  have hsz :
      (foldRangeLoop (fun out i => out.push (g i)) n 0 (Array.emptyWithCapacity n)).size = n := by
    simpa using foldRangeLoop_push_size g 0 n (Array.emptyWithCapacity n)
  rw [Array.getElem?_eq_getElem (by omega), Option.getD_some]
  have heq :=
    foldRangeLoop_push_getElem g 0 n (Array.emptyWithCapacity n) z (by simpa using hz)
  simpa using heq

private theorem foldRangeLoop_congr_lt {α : Type} (f1 f2 : α → Nat → α) (n : Nat) (acc : α)
    (hf : ∀ s z, z < n → f1 s z = f2 s z) :
    foldRangeLoop f1 n 0 acc = foldRangeLoop f2 n 0 acc := by
  simp only [foldRangeLoop, Nat.zero_add]
  congr 1
  funext s k
  exact hf s k.val k.isLt

private theorem interpFlat_eq (lo hi t : E) : interpFlat lo hi t = Model.Bus.interp lo hi t := by
  simp only [interpFlat, Model.Bus.interp, planarEadd_refines, planarEmul_refines]

private theorem interpFlat_fun_eq : interpFlat = Model.Bus.interp := by
  funext lo hi t
  exact interpFlat_eq lo hi t

private theorem interpKFlat_eq (lo hi : K) (t : E) :
    interpKFlat lo hi t = Model.Bus.interpK lo hi t := by
  simp only [interpKFlat, Model.Bus.interpK, planarEadd_refines, planarMulBase_refines]

private theorem shrinkEqHighFlat_eq (eqr : Array E) :
    shrinkEqHighFlat eqr = shrinkEqHigh eqr := by
  simp only [shrinkEqHighFlat, shrinkEqHigh, Spec.Bus.shrinkEqHigh, parReduce16,
    planarEadd_refines, eadd_eq_spec_bus]
  exact parTreeReduce_push_eq
    (fun i => Spec.Field.eadd (eqr[i]?.getD zero) (eqr[i + eqr.size / 2]?.getD zero))
    4 2048 0 (eqr.size / 2)

private theorem shrinkEqLowFlat_eq (eqr : Array E) :
    shrinkEqLowFlat eqr = shrinkEqLow eqr := by
  simp only [shrinkEqLowFlat, shrinkEqLow, Spec.Bus.shrinkEqLow, parReduce16,
    planarEadd_refines, eadd_eq_spec_bus]
  exact parTreeReduce_push_eq
    (fun i => Spec.Field.eadd (eqr[2 * i]?.getD zero) (eqr[2 * i + 1]?.getD zero))
    4 2048 0 (eqr.size / 2)

private theorem shiftLeft_succ_two (i : Nat) : 1 <<< (i + 1) = 2 * (1 <<< i) := by
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, Nat.one_mul, Nat.pow_succ]
  omega

private theorem shiftLeft_le_shiftLeft {a b : Nat} (h : a ≤ b) : (1 <<< a) ≤ (1 <<< b) := by
  simp only [Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.pow_le_pow_right (by omega) h

private theorem array_getElem_congr_coll {α : Type} {a b : Array α} (h : a = b) (i : Nat)
    (hi : i < a.size) :
    a[i]'hi = b[i]'(by
      rw [← h]
      exact hi) := by
  subst h
  rfl

private theorem array_getElem_setIfInBounds_eq {α : Type} (xs : Array α) (i : Nat) (v : α)
    (hi : i < (xs.setIfInBounds i v).size) :
    (xs.setIfInBounds i v)[i]'hi = v := by
  simp

private theorem array_getElem_setIfInBounds_ne {α : Type} (xs : Array α) (i j : Nat) (v : α)
    (hne : i ≠ j) (hj : j < (xs.setIfInBounds i v).size) :
    (xs.setIfInBounds i v)[j]'hj = xs[j]'(by simpa [Array.size_setIfInBounds] using hj) := by
  have hj' : j < xs.size := by simpa [Array.size_setIfInBounds] using hj
  rw [Array.getElem_setIfInBounds]
  exact dite_eq_right_iff.mpr (fun heq => False.elim (hne heq))

private theorem foldRangeLoop_succ_last {α : Type} (f : α → Nat → α) (m : Nat) (init : α) :
    foldRangeLoop f (m + 1) 0 init = f (foldRangeLoop f m 0 init) m := by
  unfold foldRangeLoop
  rw [Fin.foldl_succ_last]
  simp only [Fin.val_last, Nat.zero_add]
  congr 1

private def eqScalarStep (rk : E) (half : Nat) (cur : Array E) (j : Nat) : Array E :=
  let lo := cur[j]?.getD zero
  let p := nativeKaratsuba lo rk
  let cur1 := cur.setIfInBounds (half + j) p
  cur1.setIfInBounds j (Model.Field.eadd lo p)

private theorem eqScalarInner_size (out : Array E) (rk : E) (half k : Nat) :
    (foldRangeLoop (eqScalarStep rk half) k 0 out).size = out.size := by
  induction k with
  | zero => rfl
  | succ m ih =>
    rw [foldRangeLoop_succ_last]
    simp [eqScalarStep, Array.size_setIfInBounds, ih]

private theorem eqScalarInner_getElem (out : Array E) (rk : E) (half total k : Nat)
    (hk : k ≤ half) (h2 : 2 * half ≤ total) (hsz : out.size = total)
    (idx : Nat) (hidx : idx < total) :
    (foldRangeLoop (eqScalarStep rk half) k 0 out)[idx]'(by
      rw [eqScalarInner_size, hsz]
      exact hidx) =
      if idx < k then
        let lo := out[idx]?.getD zero
        Model.Field.eadd lo (nativeKaratsuba lo rk)
      else if idx < half then
        out[idx]'(by omega)
      else if idx < half + k then
        let lo := out[idx - half]?.getD zero
        nativeKaratsuba lo rk
      else
        out[idx]'(by omega) := by
  induction k generalizing idx with
  | zero =>
    have hnot1 : ¬ idx < 0 := by omega
    simp only [foldRangeLoop, Fin.foldl_zero, hnot1, ite_false]
    by_cases hh : idx < half
    · simp [hh]
    · simp [hh]
  | succ m ih =>
    let prev := foldRangeLoop (eqScalarStep rk half) m 0 out
    let lo := prev[m]?.getD zero
    let p := nativeKaratsuba lo rk
    let cur1 := prev.setIfInBounds (half + m) p
    let cur2 := cur1.setIfInBounds m (Model.Field.eadd lo p)
    have hstep_eq : foldRangeLoop (eqScalarStep rk half) (m + 1) 0 out = cur2 :=
      foldRangeLoop_succ_last (eqScalarStep rk half) m out
    have hm_lt_total : m < total := by omega
    have hsz_prev : prev.size = total := by
      dsimp only [prev]
      rw [eqScalarInner_size, hsz]
    have hprev_m : lo = out[m]?.getD zero := by
      dsimp only [lo]
      have hn1 : ¬ m < m := by omega
      have hlt2 : m < half := by omega
      have hm_prev : m < prev.size := by omega
      have hm_out : m < out.size := by omega
      rw [Array.getElem?_eq_getElem hm_prev, Array.getElem?_eq_getElem hm_out]
      simp only [Option.getD_some]
      have hp_m := ih (by omega) m hm_lt_total
      simpa [prev, hn1, hlt2] using hp_m
    have hlhs : (foldRangeLoop (eqScalarStep rk half) (m + 1) 0 out)[idx]'(by
        rw [eqScalarInner_size, hsz]
        exact hidx) =
      cur2[idx]'(by
        dsimp only [cur2, cur1]
        rw [Array.size_setIfInBounds, Array.size_setIfInBounds, hsz_prev]
        exact hidx) :=
      array_getElem_congr_coll hstep_eq idx _
    rw [hlhs]
    by_cases h1 : idx = m
    · subst h1
      rw [array_getElem_setIfInBounds_eq cur1 idx (Model.Field.eadd lo p)]
      simp [p, hprev_m]
    · rw [array_getElem_setIfInBounds_ne cur1 m idx _ (Ne.symm h1)]
      by_cases h2_eq : idx = half + m
      · subst h2_eq
        rw [array_getElem_setIfInBounds_eq prev (half + m) p]
        have hn_lt1 : ¬ half + m < m + 1 := by omega
        have hn_lt2 : ¬ half + m < half := by omega
        have h_lt3 : half + m < half + (m + 1) := by omega
        have hsub : half + m - half = m := by omega
        simp [p, hprev_m, hn_lt1, hn_lt2, h_lt3, hsub]
      · rw [array_getElem_setIfInBounds_ne prev (half + m) idx _ (Ne.symm h2_eq)]
        have hp := ih (by omega) idx hidx
        by_cases hlt_m : idx < m
        · have hlt_m1 : idx < m + 1 := by omega
          simpa [prev, hlt_m, hlt_m1] using hp
        · have hn_m1 : ¬ idx < m + 1 := by omega
          by_cases hlt_h : idx < half
          · simpa [prev, hlt_m, hn_m1, hlt_h] using hp
          · by_cases hlt_hm : idx < half + m
            · have hlt_hm1 : idx < half + (m + 1) := by omega
              simpa [prev, hlt_m, hn_m1, hlt_h, hlt_hm, hlt_hm1] using hp
            · have hn_hm1 : ¬ idx < half + (m + 1) := by omega
              simpa [prev, hlt_m, hn_m1, hlt_h, hlt_hm, hn_hm1] using hp

private theorem eqTableExpandArray_size (cur : Array E) (rk : E) (half : Nat) :
    (eqTableExpandArray cur rk half).size = 2 * half := by
  unfold eqTableExpandArray parReduce16
  rw [parTreeReduce_push_eq, parTreeReduce_push_eq, Array.size_append,
    foldRangeLoop_push_size, foldRangeLoop_push_size]
  simp [Nat.two_mul]

private theorem eqTableExpandArray_getElem (cur : Array E) (rk : E) (half idx : Nat)
    (hidx : idx < 2 * half) :
    (eqTableExpandArray cur rk half)[idx]'(by
      rw [eqTableExpandArray_size]
      exact hidx) =
      if idx < half then
        let lo := cur[idx]?.getD zero
        Model.Field.eadd lo (nativeKaratsuba lo rk)
      else
        let lo := cur[idx - half]?.getD zero
        nativeKaratsuba lo rk := by
  unfold eqTableExpandArray parReduce16
  simp only [planarEadd_refines, planarEmul_refines]
  have hlo_eq := parTreeReduce_push_eq
    (fun j => Model.Field.eadd (cur[j]?.getD zero) (nativeKaratsuba (cur[j]?.getD zero) rk))
    4 2048 0 half
  have hhi_eq := parTreeReduce_push_eq
    (fun j => nativeKaratsuba (cur[j]?.getD zero) rk)
    4 2048 0 half
  simp only [hlo_eq, hhi_eq]
  have hsz_lo : (foldRangeLoop
      (fun out j => out.push (Model.Field.eadd (cur[j]?.getD zero)
        (nativeKaratsuba (cur[j]?.getD zero) rk)))
      half 0 (Array.emptyWithCapacity half)).size = half := by
    simpa using foldRangeLoop_push_size
      (fun j => Model.Field.eadd (cur[j]?.getD zero) (nativeKaratsuba (cur[j]?.getD zero) rk))
      0 half (Array.emptyWithCapacity half)
  rw [Array.getElem_append]
  split
  · next hlt =>
    have hlt' : idx < half := by omega
    simp only [hlt', ite_true]
    have hg := foldRangeLoop_push_getElem
      (fun j => Model.Field.eadd (cur[j]?.getD zero) (nativeKaratsuba (cur[j]?.getD zero) rk))
      0 half (Array.emptyWithCapacity half) idx (by simpa using hlt')
    simpa using hg
  · next hge =>
    have hnlt : ¬ idx < half := by omega
    have hsub_lt : idx - half < half := by omega
    simp only [hnlt, ite_false, hsz_lo]
    have hg := foldRangeLoop_push_getElem
      (fun j => nativeKaratsuba (cur[j]?.getD zero) rk)
      0 half (Array.emptyWithCapacity half) (idx - half) (by simpa using hsub_lt)
    simpa using hg

private theorem eqTableScalar_outer_size (r : Array E) (k : Nat) (init : Array E) :
    (foldRangeLoop
      (fun out i =>
        let rk := r[i]?.getD zero
        let half := 1 <<< i
        foldRange half (eqScalarStep rk half) out)
      k 0 init).size = init.size := by
  induction k with
  | zero => rfl
  | succ m ih =>
    rw [foldRangeLoop_succ_last]
    change (foldRangeLoop (eqScalarStep (r[m]?.getD zero) (1 <<< m)) (1 <<< m) 0 _).size = init.size
    rw [eqScalarInner_size, ih]

private theorem eqTableFlat_outer_size (r : Array E) (k : Nat) :
    (foldRangeLoop
      (fun cur i => eqTableExpandArray cur (r[i]?.getD zero) (1 <<< i))
      k 0 #[one]).size = (1 <<< k) := by
  induction k with
  | zero => rfl
  | succ m ih =>
    rw [foldRangeLoop_succ_last, eqTableExpandArray_size, shiftLeft_succ_two]

private theorem eqTable_loop_inv (r : Array E) (k : Nat) (hk : k ≤ r.size) :
    let total := 1 <<< r.size
    let init := (Array.replicate total zero).setIfInBounds 0 one
    let scalarOut := foldRangeLoop
      (fun out i =>
        let rk := r[i]?.getD zero
        let half := 1 <<< i
        foldRange half (eqScalarStep rk half) out)
      k 0 init
    let flatOut := foldRangeLoop
      (fun cur i => eqTableExpandArray cur (r[i]?.getD zero) (1 <<< i))
      k 0 #[one]
    (∀ idx (hlt : idx < (1 <<< k)),
      scalarOut[idx]'(by
        rw [eqTableScalar_outer_size, Array.size_setIfInBounds, Array.size_replicate]
        have := shiftLeft_le_shiftLeft hk
        omega) =
      flatOut[idx]'(by
        rw [eqTableFlat_outer_size]
        exact hlt)) ∧
    (∀ idx, (1 <<< k) ≤ idx → (hlt : idx < total) →
      scalarOut[idx]'(by
        rw [eqTableScalar_outer_size, Array.size_setIfInBounds, Array.size_replicate]
        exact hlt) = zero) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro idx hidx
      have h0 : idx = 0 := by
        have h1 : 1 <<< 0 = 1 := rfl
        omega
      subst h0
      simp only [foldRangeLoop, Fin.foldl_zero]
      rw [array_getElem_setIfInBounds_eq]
      rfl
    · intro idx hge hlt
      have hne : 0 ≠ idx := by
        have h1 : 1 <<< 0 = 1 := rfl
        omega
      simp only [foldRangeLoop, Fin.foldl_zero]
      rw [array_getElem_setIfInBounds_ne _ 0 idx _ hne]
      simp [Array.getElem_replicate]
  | succ m ih =>
    have hm_le : m ≤ r.size := by omega
    obtain ⟨heq_pre, hzero_post⟩ := ih hm_le
    let total := 1 <<< r.size
    let init := (Array.replicate total zero).setIfInBounds 0 one
    let prevS := foldRangeLoop
      (fun out i =>
        let rk := r[i]?.getD zero
        let half := 1 <<< i
        foldRange half (eqScalarStep rk half) out)
      m 0 init
    let prevF := foldRangeLoop
      (fun cur i => eqTableExpandArray cur (r[i]?.getD zero) (1 <<< i))
      m 0 #[one]
    let rk := r[m]?.getD zero
    let half := 1 <<< m
    have hsz_prevS : prevS.size = total := by
      dsimp only [prevS, init]
      rw [eqTableScalar_outer_size, Array.size_setIfInBounds, Array.size_replicate]
    have hsz_prevF : prevF.size = half := eqTableFlat_outer_size r m
    have hstepS : foldRangeLoop
        (fun out i =>
          let rk := r[i]?.getD zero
          let half := 1 <<< i
          foldRange half (eqScalarStep rk half) out)
        (m + 1) 0 init = foldRangeLoop (eqScalarStep rk half) half 0 prevS :=
      foldRangeLoop_succ_last
        (fun out i =>
          let rk := r[i]?.getD zero
          let half := 1 <<< i
          foldRange half (eqScalarStep rk half) out)
        m init
    have hstepF : foldRangeLoop
        (fun cur i => eqTableExpandArray cur (r[i]?.getD zero) (1 <<< i))
        (m + 1) 0 #[one] = eqTableExpandArray prevF rk half :=
      foldRangeLoop_succ_last
        (fun cur i => eqTableExpandArray cur (r[i]?.getD zero) (1 <<< i))
        m #[one]
    have h2half_eq : 1 <<< (m + 1) = 2 * half := shiftLeft_succ_two m
    have h2half_le : 2 * half ≤ total := by
      rw [← h2half_eq]
      exact shiftLeft_le_shiftLeft hk
    have hgetD_eq : ∀ j < half, prevS[j]?.getD zero = prevF[j]?.getD zero := by
      intro j hj
      rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem (by omega)]
      simpa using heq_pre j hj
    refine ⟨?_, ?_⟩
    · intro idx hidx
      have hidx_tot : idx < total := by omega
      have hs := eqScalarInner_getElem prevS rk half total half (Nat.le_refl half)
        h2half_le hsz_prevS idx hidx_tot
      have hf := eqTableExpandArray_getElem prevF rk half idx (by omega)
      have h_lhs : (foldRangeLoop
          (fun out i =>
            let rk := r[i]?.getD zero
            let half := 1 <<< i
            foldRange half (eqScalarStep rk half) out)
          (m + 1) 0 init)[idx]'(by
            rw [eqTableScalar_outer_size, Array.size_setIfInBounds, Array.size_replicate]
            exact hidx_tot) =
          (foldRangeLoop (eqScalarStep rk half) half 0 prevS)[idx]'(by
            rw [eqScalarInner_size, hsz_prevS]
            exact hidx_tot) :=
        array_getElem_congr_coll hstepS idx _
      have h_rhs : (foldRangeLoop
          (fun cur i => eqTableExpandArray cur (r[i]?.getD zero) (1 <<< i))
          (m + 1) 0 #[one])[idx]'(by
            rw [eqTableFlat_outer_size]
            exact hidx) =
          (eqTableExpandArray prevF rk half)[idx]'(by
            rw [eqTableExpandArray_size]
            omega) :=
        array_getElem_congr_coll hstepF idx _
      rw [h_lhs, h_rhs, hs, hf]
      by_cases hlt : idx < half
      · simp [hlt, hgetD_eq idx hlt]
      · have hlt2 : idx < half + half := by omega
        have hsub : idx - half < half := by omega
        simp [hlt, hlt2, hgetD_eq (idx - half) hsub]
    · intro idx hge hlt_tot
      have hs := eqScalarInner_getElem prevS rk half total half (Nat.le_refl half)
        h2half_le hsz_prevS idx hlt_tot
      have h_lhs : (foldRangeLoop
          (fun out i =>
            let rk := r[i]?.getD zero
            let half := 1 <<< i
            foldRange half (eqScalarStep rk half) out)
          (m + 1) 0 init)[idx]'(by
            rw [eqTableScalar_outer_size, Array.size_setIfInBounds, Array.size_replicate]
            exact hlt_tot) =
          (foldRangeLoop (eqScalarStep rk half) half 0 prevS)[idx]'(by
            rw [eqScalarInner_size, hsz_prevS]
            exact hlt_tot) :=
        array_getElem_congr_coll hstepS idx _
      have hn1 : ¬ idx < half := by omega
      have hn2 : ¬ idx < half + half := by omega
      rw [h_lhs, hs]
      simp only [hn1, hn2, ite_false]
      exact hzero_post idx (by omega) hlt_tot

private theorem eqTableArrayFlat_eq (r : Array E) : eqTableArrayFlat r = eqTable r := by
  obtain ⟨heq_pre, _⟩ := eqTable_loop_inv r r.size (Nat.le_refl r.size)
  have hscalar_eq : eqTable r =
      foldRangeLoop
        (fun out i =>
          let rk := r[i]?.getD zero
          let half := 1 <<< i
          foldRange half (eqScalarStep rk half) out)
        r.size 0 ((Array.replicate (1 <<< r.size) zero).setIfInBounds 0 one) := rfl
  have hflat_eq : eqTableArrayFlat r =
      foldRangeLoop
        (fun cur i => eqTableExpandArray cur (r[i]?.getD zero) (1 <<< i))
        r.size 0 #[one] := rfl
  rw [hflat_eq, hscalar_eq]
  apply Array.ext
  · rw [eqTableFlat_outer_size, eqTableScalar_outer_size,
      Array.size_setIfInBounds, Array.size_replicate]
  · intro idx h1 h2
    rw [eqTableFlat_outer_size] at h1
    exact (heq_pre idx h1).symm

private theorem mleEvalWithEqFlat_eq_table (table : Array K) (point : Array E) :
    mleEvalWithEqFlat table (eqTable point) = mleEval table point := by
  unfold mleEvalWithEqFlat mleEval parReduce16 foldRange
  simp only [planarEadd_eq, planarMulBase_eq]
  exact parTreeReduce_monoid Model.Field.eadd zero eadd_assoc_model eadd_zero_right_model
    (fun z => nativeMulBase ((eqTable point)[z]?.getD zero) (table[z]?.getD 0))
    4 2048 0 (eqTable point).size

private theorem mleEvalWithEqFlat_eq (table : Array K) (point : Array E) :
    mleEvalWithEqFlat table (eqTableArrayFlat point) = mleEval table point := by
  rw [eqTableArrayFlat_eq]
  exact mleEvalWithEqFlat_eq_table table point

private theorem buildSideLeavesFlat_eq (gpows : Array K) (blocks : Array Block) (lay : BusLayout)
    (cols bcCols : Array (Array K)) (w : Array E) (beta : E) :
    buildSideLeavesFlat gpows blocks lay cols bcCols w beta =
      buildSideLeaves gpows blocks lay cols bcCols w beta := by
  unfold buildSideLeavesFlat buildSideLeaves
  simp only [planarEadd_eq, planarMulBase_eq, parReduce16]
  congr 1
  funext leaves b
  cases blocks[b]? with
  | none => rfl
  | some blk =>
    dsimp only []
    let rowVal (z : Nat) : E :=
      foldRange blk.coords.size
        (fun acc i =>
          let c := blk.coords[i]?.getD (cConst 0)
          let wi := w[i]?.getD zero
          Model.Field.eadd acc (nativeMulBase wi (evalCoord gpows cols bcCols z c)))
        beta
    have hbv : parTreeReduce 4 1024 0 blk.rows
        (fun base len =>
          foldRangeLoop (fun out z => out.push (rowVal z)) len base (Array.emptyWithCapacity len))
        Array.append =
        foldRangeLoop (fun out z => out.push (rowVal z))
          blk.rows 0 (Array.emptyWithCapacity blk.rows) :=
      parTreeReduce_push_eq rowVal 4 1024 0 blk.rows
    change foldRange blk.rows
        (fun cur z => cur.setIfInBounds ((lay.offsets[b]?.getD 0) + z)
          ((parTreeReduce 4 1024 0 blk.rows
            (fun base len =>
              foldRangeLoop (fun out z => out.push (rowVal z))
                len base (Array.emptyWithCapacity len))
            Array.append)[z]?.getD one))
        leaves =
      foldRange blk.rows
        (fun cur z => cur.setIfInBounds ((lay.offsets[b]?.getD 0) + z) (rowVal z))
        leaves
    rw [hbv]
    unfold foldRange
    apply foldRangeLoop_congr_lt
    intro cur z hz
    rw [precomputed_array_getD rowVal one blk.rows z hz]

private theorem nextLevelFlat_eq (current : Array E) :
    nextLevelFlat current = nextLevel current := by
  unfold nextLevelFlat nextLevel parReduce16 foldRange
  simp only [planarEmul_eq]
  have hp := parTreeReduce_push_eq
    (fun row =>
      nativeKaratsuba
        (nativeKaratsuba (current[4 * row]?.getD one) (current[4 * row + 1]?.getD one))
        (nativeKaratsuba (current[4 * row + 2]?.getD one) (current[4 * row + 3]?.getD one)))
    4 1024 0 (current.size / 4)
  have hemp := foldRangeLoop_push_empty
    (fun row =>
      nativeKaratsuba
        (nativeKaratsuba (current[4 * row]?.getD one) (current[4 * row + 1]?.getD one))
        (nativeKaratsuba (current[4 * row + 2]?.getD one) (current[4 * row + 3]?.getD one)))
    0 (current.size / 4) (current.size / 4) ((current.size + 3) / 4)
  rw [hp, hemp]

private theorem buildLayersFlat_eq (leaves : Array E) (mu : Nat) :
    buildLayersFlat leaves mu = buildLayers leaves mu := by
  simp only [buildLayersFlat, buildLayers, funext nextLevelFlat_eq, planarEmul_eq]

private theorem quarticSummandFlat_eq (g0 s0 g1 s1 g2 s2 g3 s3 eqWeight : E) :
    quarticSummandFlat g0 s0 g1 s1 g2 s2 g3 s3 eqWeight =
      quarticSummand g0 s0 g1 s1 g2 s2 g3 s3 eqWeight := by
  simp only [quarticSummandFlat, quarticSummand, planarEadd_eq, planarEmul_eq]

private theorem addMsg4Flat_eq : addMsg4Flat = addMsg4 := by
  funext a b
  rcases a with ⟨a1, a2, a3, a4⟩
  rcases b with ⟨b1, b2, b3, b4⟩
  simp only [addMsg4Flat, addMsg4, Spec.Bus.addMsg4, planarEadd_refines, eadd_eq_spec_bus]

private theorem treeRoundMessageFlat_eq (values eqWeights : Array E) :
    treeRoundMessageFlat values eqWeights = treeRoundMessage values eqWeights := by
  unfold treeRoundMessageFlat treeRoundMessage parReduce16 foldRange
  simp only [planarEadd_eq, quarticSummandFlat_eq, addMsg4Flat_eq]
  rw [parTreeReduce_monoid addMsg4 (zero, zero, zero, zero) addMsg4_assoc addMsg4_zero_right]

private theorem foldTreeFlat_eq (values : Array E) (challenge : E) :
    foldTreeFlat values challenge = foldTreeScalar values challenge := by
  unfold foldTreeFlat foldTreeScalar parReduce16 foldRange
  simp only [interpFlat_fun_eq]
  let g0 (row : Nat) := Model.Bus.interp (values[8 * row]?.getD one)
    (values[8 * row + 4]?.getD one) challenge
  let g1 (row : Nat) := Model.Bus.interp (values[8 * row + 1]?.getD one)
    (values[8 * row + 5]?.getD one) challenge
  let g2 (row : Nat) := Model.Bus.interp (values[8 * row + 2]?.getD one)
    (values[8 * row + 6]?.getD one) challenge
  let g3 (row : Nat) := Model.Bus.interp (values[8 * row + 3]?.getD one)
    (values[8 * row + 7]?.getD one) challenge
  have hp := parTreeReduce_push4_eq g0 g1 g2 g3 4 512 0 (values.size / 4 / 2)
  have hemp := foldRangeLoop_push4_empty g0 g1 g2 g3 0 (values.size / 4 / 2)
    (4 * (values.size / 4 / 2)) (4 * ((values.size / 4 + 1) / 2))
  rw [hp, hemp]

private theorem combineMsg4Flat_eq (lambda : E) (m0 m1 m2 : E × E × E × E) :
    combineMsg4Flat lambda m0 m1 m2 = combineMsg4 lambda m0 m1 m2 := by
  simp only [combineMsg4Flat, combineMsg4, planarEadd_eq, planarEmul_eq]

private theorem treeRoundFoldFlat_eq (lambda : E) (point : Array E) (roundCount : Nat)
    (t0 t1 t2 : Array E) (curPs : ProverState) :
    treeRoundFoldFlat lambda point roundCount t0 t1 t2 curPs =
      treeRoundFold lambda point roundCount t0 t1 t2 curPs := by
  simp only [treeRoundFoldFlat, treeRoundFold, eqTableArrayFlat_eq,
    treeRoundMessageFlat_eq, combineMsg4Flat_eq, shrinkEqLowFlat_eq, foldTreeFlat_eq]

private theorem proveProductTripleFlat_eq (leaves0 leaves1 leaves2 : Array E) (mu : Nat)
    (ps : ProverState) :
    proveProductTripleFlat leaves0 leaves1 leaves2 mu ps =
      proveProductTriple leaves0 leaves1 leaves2 mu ps := by
  unfold proveProductTripleFlat proveProductTriple
  simp only [task_spawn_get, buildLayersFlat_eq, interpFlat_fun_eq, treeRoundFoldFlat_eq]

private theorem decomposeNoneCoordsFlat_eq (gpows : Array K) (blk : Block)
    (cols bcCols : Array (Array K)) (zetaLo w : Array E)
    (curClaims : Array ColumnClaim) (curPs : ProverState) :
    decomposeNoneCoordsFlat gpows blk cols bcCols zetaLo w (eqTableArrayFlat zetaLo)
      curClaims curPs =
    decomposeNoneCoords gpows blk cols bcCols zetaLo w curClaims curPs := by
  unfold decomposeNoneCoordsFlat decomposeNoneCoords
  simp only [planarEadd_eq, planarEmul_eq, planarMulBase_eq, mleEvalWithEqFlat_eq]
  rfl

private theorem decomposeSideFoldFlat_eq (gpows : Array K) (blocks : Array Block) (lay : BusLayout)
    (cols bcCols : Array (Array K)) (zeta w : Array E) (beta : E)
    (forms : Array BusForm) (claims : Array ColumnClaim) (ps : ProverState) :
    decomposeSideFoldFlat gpows blocks lay cols bcCols zeta w beta forms claims ps =
      decomposeSideFold gpows blocks lay cols bcCols zeta w beta forms claims ps := by
  unfold decomposeSideFoldFlat decomposeSideFold
  simp only [planarEadd_eq, planarEmul_eq, planarMulBase_eq, decomposeNoneCoordsFlat_eq]
  rfl

private theorem decomposeSideFlat_eq (gpows : Array K) (blocks : Array Block) (lay : BusLayout)
    (cols bcCols : Array (Array K)) (zeta w : Array E) (beta : E)
    (forms : Array BusForm) (claims : Array ColumnClaim) (ps : ProverState) :
    decomposeSideFlat gpows blocks lay cols bcCols zeta w beta forms claims ps =
      decomposeSide gpows blocks lay cols bcCols zeta w beta forms claims ps := by
  simp only [decomposeSideFlat, decomposeSide, decomposeSideFoldFlat_eq, planarEadd_eq]

private theorem foldRange_pair_push_eq {γ : Type} (pairs : Array (Nat × Nat))
    (f : Nat → Nat → γ) :
    parReduce16 2 pairs.size
      (fun b l =>
        foldRangeLoop
          (fun acc idx =>
            match pairs[idx]? with
            | none => acc
            | some (a, bCol) => acc.push (f a bCol))
          l b (Array.emptyWithCapacity l))
      Array.append =
    foldRangeLoop
      (fun acc idx =>
        match pairs[idx]? with
        | none => acc
        | some (a, bCol) => acc.push (f a bCol))
      pairs.size 0 (Array.emptyWithCapacity pairs.size) := by
  by_cases h0 : pairs.size = 0
  · rw [h0]
    rfl
  · have hpos : 0 < pairs.size := by omega
    let x0 : Nat × Nat := pairs[0]'hpos
    let g (idx : Nat) : γ :=
      let ab := pairs[idx]?.getD x0
      f ab.1 ab.2
    have hleaf : ∀ b l, b + l ≤ pairs.size →
        foldRangeLoop
          (fun acc idx =>
            match pairs[idx]? with
            | none => acc
            | some (a, bCol) => acc.push (f a bCol))
          l b (Array.emptyWithCapacity l) =
        foldRangeLoop (fun acc idx => acc.push (g idx)) l b (Array.emptyWithCapacity l) := by
      intro b l hbl
      simp only [foldRangeLoop]
      congr 1
      funext acc k
      have hlt : b + k.val < pairs.size := by omega
      rcases hval : pairs[b + k.val]'hlt with ⟨a, bCol⟩
      simp [Array.getElem?_eq_getElem hlt, hval, g]
    have hpar_g : ∀ d b l, b + l ≤ pairs.size →
        parTreeReduce d 2 b l
          (fun b' l' =>
            foldRangeLoop
              (fun acc idx =>
                match pairs[idx]? with
                | none => acc
                | some (a, bCol) => acc.push (f a bCol))
              l' b' (Array.emptyWithCapacity l'))
          Array.append =
        foldRangeLoop (fun acc idx => acc.push (g idx)) l b (Array.emptyWithCapacity l) := by
      intro d
      induction d with
      | zero =>
        intro b l hbl
        exact hleaf b l hbl
      | succ d' ih =>
        intro b l hbl
        change (if l < 2 then _ else _) = _
        split
        · exact hleaf b l hbl
        · dsimp only []
          change HAppend.hAppend (parTreeReduce d' 2 b (l / 2) _ Array.append)
            (parTreeReduce d' 2 (b + l / 2) (l - l / 2) _ Array.append) = _
          rw [ih b (l / 2) (by omega), ih (b + l / 2) (l - l / 2) (by omega),
            foldRangeLoop_push_append, foldRangeLoop_push_empty g b (l / 2) (l / 2) l,
            ← foldRangeLoop_split, Nat.add_sub_of_le (Nat.div_le_self l 2)]
    unfold parReduce16
    rw [hpar_g 4 0 pairs.size (by omega)]
    exact (hleaf 0 pairs.size (by omega)).symm

private theorem computeTableSigmas_table_eq (cols : Array (Array K)) (base nCols : Nat)
    (zetaTau : Array E) (f0 f1 f2 : BusForm) (s0 s1 s2 : Array E) :
    (let eqs := eqTableArrayFlat zetaTau
      let colEvals := parReduce16 2 nCols
        (fun b l =>
          foldRangeLoop
            (fun acc c => acc.push (mleEvalWithEqFlat (cols[base + c]?.getD #[]) eqs))
            l b (Array.emptyWithCapacity l))
        Array.append
      let collectPairs (pairs : Array (Nat × Nat)) (f : BusForm) : Array (Nat × Nat) :=
        foldRange f.prods.size
          (fun cur idx =>
            match f.prods[idx]? with
            | none => cur
            | some p => if hasPair cur p.colA p.colB then cur else cur.push (p.colA, p.colB))
          pairs
      let pairs := collectPairs (collectPairs (collectPairs #[] f0) f1) f2
      let prodSums := parReduce16 2 pairs.size
        (fun b l =>
          foldRangeLoop
            (fun acc idx =>
              match pairs[idx]? with
              | none => acc
              | some (a, bCol) =>
                let colA := cols[base + a]?.getD #[]
                let colB := cols[base + bCol]?.getD #[]
                let sum := parReduce16 2048 eqs.size
                  (fun zb zl =>
                    foldRangeLoop
                      (fun s z =>
                        let prodK := nativeMul (colA[z]?.getD 0) (colB[z]?.getD 0)
                        planarEadd s (planarMulBase (eqs[z]?.getD zero) prodK))
                      zl zb zero)
                  planarEadd
                acc.push (a, bCol, sum))
            l b (Array.emptyWithCapacity l))
        Array.append
      (s0.push (evalBusFormSigma f0 colEvals prodSums),
        s1.push (evalBusFormSigma f1 colEvals prodSums),
        s2.push (evalBusFormSigma f2 colEvals prodSums))) =
    (let eqs := eqTable zetaTau
      let colEvals := foldRange nCols
        (fun acc c =>
          let col := cols[base + c]?.getD #[]
          let sum := foldRange eqs.size
            (fun s z => Model.Field.eadd s (nativeMulBase (eqs[z]?.getD zero) (col[z]?.getD 0)))
            zero
          acc.push sum)
        (Array.emptyWithCapacity nCols)
      let collectPairs (pairs : Array (Nat × Nat)) (f : BusForm) : Array (Nat × Nat) :=
        foldRange f.prods.size
          (fun cur idx =>
            match f.prods[idx]? with
            | none => cur
            | some p => if hasPair cur p.colA p.colB then cur else cur.push (p.colA, p.colB))
          pairs
      let pairs := collectPairs (collectPairs (collectPairs #[] f0) f1) f2
      let prodSums := foldRange pairs.size
        (fun acc idx =>
          match pairs[idx]? with
          | none => acc
          | some (a, b) =>
            let colA := cols[base + a]?.getD #[]
            let colB := cols[base + b]?.getD #[]
            let sum := foldRange eqs.size
              (fun s z =>
                let prodK := nativeMul (colA[z]?.getD 0) (colB[z]?.getD 0)
                Model.Field.eadd s (nativeMulBase (eqs[z]?.getD zero) prodK))
              zero
            acc.push (a, b, sum))
        (Array.emptyWithCapacity pairs.size)
      (s0.push (evalBusFormSigma f0 colEvals prodSums),
        s1.push (evalBusFormSigma f1 colEvals prodSums),
        s2.push (evalBusFormSigma f2 colEvals prodSums))) := by
  dsimp only []
  have hcol : parReduce16 2 nCols
      (fun b l =>
        foldRangeLoop
          (fun acc c =>
            acc.push (mleEvalWithEqFlat (cols[base + c]?.getD #[]) (eqTableArrayFlat zetaTau)))
          l b (Array.emptyWithCapacity l))
      Array.append =
    foldRange nCols
      (fun acc c =>
        let col := cols[base + c]?.getD #[]
        let sum := foldRange (eqTable zetaTau).size
          (fun s z =>
            Model.Field.eadd s
              (nativeMulBase ((eqTable zetaTau)[z]?.getD zero) (col[z]?.getD 0)))
          zero
        acc.push sum)
      (Array.emptyWithCapacity nCols) := by
    simp only [mleEvalWithEqFlat_eq, mleEval]
    unfold parReduce16 foldRange
    exact parTreeReduce_push_eq _ 4 2 0 nCols
  have hsum : ∀ (a bCol : Nat),
      parReduce16 2048 (eqTableArrayFlat zetaTau).size
        (fun zb zl =>
          foldRangeLoop
            (fun s z =>
              let prodK := nativeMul
                ((cols[base + a]?.getD #[])[z]?.getD 0)
                ((cols[base + bCol]?.getD #[])[z]?.getD 0)
              planarEadd s (planarMulBase ((eqTableArrayFlat zetaTau)[z]?.getD zero) prodK))
            zl zb zero)
        planarEadd =
      foldRange (eqTable zetaTau).size
        (fun s z =>
          let prodK := nativeMul
            ((cols[base + a]?.getD #[])[z]?.getD 0)
            ((cols[base + bCol]?.getD #[])[z]?.getD 0)
          Model.Field.eadd s (nativeMulBase ((eqTable zetaTau)[z]?.getD zero) prodK))
        zero := by
    intro a bCol
    rw [eqTableArrayFlat_eq]
    unfold parReduce16 foldRange
    simp only [planarEadd_eq, planarMulBase_eq]
    exact parTreeReduce_monoid Model.Field.eadd zero eadd_assoc_model eadd_zero_right_model
      _ 4 2048 0 _
  have hprod : ∀ (pairs : Array (Nat × Nat)),
      parReduce16 2 pairs.size
        (fun b l =>
          foldRangeLoop
            (fun acc idx =>
              match pairs[idx]? with
              | none => acc
              | some (a, bCol) =>
                let colA := cols[base + a]?.getD #[]
                let colB := cols[base + bCol]?.getD #[]
                let sum := parReduce16 2048 (eqTableArrayFlat zetaTau).size
                  (fun zb zl =>
                    foldRangeLoop
                      (fun s z =>
                        let prodK := nativeMul (colA[z]?.getD 0) (colB[z]?.getD 0)
                        planarEadd s (planarMulBase
                          ((eqTableArrayFlat zetaTau)[z]?.getD zero) prodK))
                      zl zb zero)
                  planarEadd
                acc.push (a, bCol, sum))
            l b (Array.emptyWithCapacity l))
        Array.append =
      foldRange pairs.size
        (fun acc idx =>
          match pairs[idx]? with
          | none => acc
          | some (a, b) =>
            let colA := cols[base + a]?.getD #[]
            let colB := cols[base + b]?.getD #[]
            let sum := foldRange (eqTable zetaTau).size
              (fun s z =>
                let prodK := nativeMul (colA[z]?.getD 0) (colB[z]?.getD 0)
                Model.Field.eadd s (nativeMulBase ((eqTable zetaTau)[z]?.getD zero) prodK))
              zero
            acc.push (a, b, sum))
        (Array.emptyWithCapacity pairs.size) := by
    intro pairs
    unfold foldRange
    simp only [hsum]
    exact foldRange_pair_push_eq pairs (fun a bCol =>
      (a, bCol,
        foldRangeLoop
          (fun s z =>
            Model.Field.eadd s (nativeMulBase ((eqTable zetaTau)[z]?.getD zero)
              (nativeMul ((cols[base + a]?.getD #[])[z]?.getD 0)
                ((cols[base + bCol]?.getD #[])[z]?.getD 0))))
          (eqTable zetaTau).size 0 zero))
  rw [hcol, hprod]

private theorem computeTableSigmasFlat_eq (cols : Array (Array K)) (taus : Array Nat)
    (forms0 forms1 forms2 : Array BusForm) (zeta : Array E) :
    computeTableSigmasFlat cols taus forms0 forms1 forms2 zeta =
      computeTableSigmas cols taus forms0 forms1 forms2 zeta := by
  unfold computeTableSigmasFlat computeTableSigmas
  apply foldRangeLoop_congr_lt
  intro ⟨s0, s1, s2⟩ t h
  dsimp only []
  simp only [h, dite_true]
  exact computeTableSigmas_table_eq cols (tableBase ⟨t, h⟩) (tableWidth ⟨t, h⟩)
    (zeta.extract 0 (taus[t]?.getD 0))
    (forms0[t]?.getD (emptyBusForm (tableWidth ⟨t, h⟩)))
    (forms1[t]?.getD (emptyBusForm (tableWidth ⟨t, h⟩)))
    (forms2[t]?.getD (emptyBusForm (tableWidth ⟨t, h⟩)))
    s0 s1 s2

theorem proveBalance_flat_refines (gpows : Array K) (lay : Model.Layout.PublicLayout)
    (cols bcCols : Array (Array K)) (ps : ProverState) :
    proveBalanceFlat gpows lay cols bcCols ps = proveBalance gpows lay cols bcCols ps := by
  unfold proveBalanceFlat proveBalance
  simp only [task_spawn_get, buildSideLeavesFlat_eq, proveProductTripleFlat_eq,
    decomposeSideFlat_eq, computeTableSigmasFlat_eq]

private theorem evalLinKFlat_eq (terms : Array (Nat × E)) (cols : Array (Array K))
    (base row : Nat) :
    evalLinKFlat terms cols base row = evalLinK terms cols base row := by
  simp only [evalLinKFlat, evalLinK, planarEadd_eq, planarMulBase_eq]
  rfl

private theorem evalLinSumKFlat_eq (terms : Array (Nat × E)) (cols : Array (Array K))
    (base i half : Nat) :
    evalLinSumKFlat terms cols base i half = evalLinSumK terms cols base i half := by
  simp only [evalLinSumKFlat, evalLinSumK, planarEadd_eq, planarMulBase_eq]
  rfl

private theorem tableMessageKFlat_eq (gf : GroupedForm) (cols : Array (Array K))
    (base : Nat) (eqr : Array E) (half : Nat) (atOne : Bool) :
    tableMessageKFlat gf cols base eqr half atOne =
      tableMessageK gf cols base eqr half atOne := by
  unfold tableMessageKFlat tableMessageK parReduce16 foldRange
  simp only [planarEadd_eq, planarEmul_eq, planarMulBase_eq,
    evalLinKFlat_eq, evalLinSumKFlat_eq]
  let pairOp (a b : E × E) : E × E := (Model.Field.eadd a.1 b.1, Model.Field.eadd a.2 b.2)
  let rowFn (i : Nat) : E × E :=
    let endIdx := if atOne then i + half else i
    let linEnd := evalLinK gf.lin cols base endIdx
    let (ep, sl) := foldRangeLoop
      (fun (epG, slG) g =>
        match gf.groups[g]? with
        | none => (epG, slG)
        | some (left, right) =>
          let leftCol := cols[base + left]?.getD #[]
          let leftEnd := leftCol[endIdx]?.getD 0
          let leftSum := Model.Field.add (leftCol[i]?.getD 0) (leftCol[i + half]?.getD 0)
          let rightEnd := evalLinK right cols base endIdx
          let rightSum := evalLinSumK right cols base i half
          (Model.Field.eadd epG (nativeMulBase rightEnd leftEnd),
            Model.Field.eadd slG (nativeMulBase rightSum leftSum)))
      gf.groups.size 0 (linEnd, zero)
    let eqw := eqr[i]?.getD zero
    (nativeKaratsuba eqw ep, nativeKaratsuba eqw sl)
  have hpar := parTreeReduce_monoid pairOp (zero, zero)
    (fun a b c => pair_eadd_assoc a b c) pair_eadd_zero_right rowFn 4 512 0 half
  exact congrArg (fun p : E × E => (Model.Field.eadd p.1 gf.constant, p.2)) hpar

private theorem joinTableStateFlat_eq (gf : GroupedForm) (cols : Array (Array K))
    (base : Nat) (r : E) (half : Nat) :
    joinTableStateFlat gf cols base r half = joinTableState gf cols base r half := by
  unfold joinTableStateFlat joinTableState
  have hlin : ∀ (terms : Array (Nat × E)),
      parReduce16 512 half
        (fun rowBase rowLen =>
          foldRangeLoop
            (fun col i =>
              let v := foldRange terms.size
                (fun acc idx =>
                  match terms[idx]? with
                  | none => acc
                  | some (c, w) =>
                    let kc := cols[base + c]?.getD #[]
                    let lo := kc[i]?.getD 0
                    let hi := kc[i + half]?.getD 0
                    let wr := planarEmul w r
                    planarEadd acc
                      (planarEadd (planarMulBase w lo)
                        (planarMulBase wr (Model.Field.add lo hi))))
                zero
              col.push v)
            rowLen rowBase (Array.emptyWithCapacity rowLen))
        Array.append =
      foldRange half
        (fun col i =>
          let v := foldRange terms.size
            (fun acc idx =>
              match terms[idx]? with
              | none => acc
              | some (c, w) =>
                let kc := cols[base + c]?.getD #[]
                let lo := kc[i]?.getD 0
                let hi := kc[i + half]?.getD 0
                let wr := nativeKaratsuba w r
                Model.Field.eadd acc
                  (Model.Field.eadd (nativeMulBase w lo)
                    (nativeMulBase wr (Model.Field.add lo hi))))
            zero
          col.push v)
        (Array.emptyWithCapacity half) := by
    intro terms
    unfold parReduce16 foldRange
    simp only [planarEadd_eq, planarEmul_eq, planarMulBase_eq]
    exact parTreeReduce_push_eq _ 4 512 0 half
  have hinit : #[parReduce16 512 half
      (fun rowBase rowLen =>
        foldRangeLoop
          (fun col i =>
            let v := foldRange gf.lin.size
              (fun acc idx =>
                match gf.lin[idx]? with
                | none => acc
                | some (c, w) =>
                  let kc := cols[base + c]?.getD #[]
                  let lo := kc[i]?.getD 0
                  let hi := kc[i + half]?.getD 0
                  let wr := planarEmul w r
                  planarEadd acc
                    (planarEadd (planarMulBase w lo)
                      (planarMulBase wr (Model.Field.add lo hi))))
              zero
            col.push v)
          rowLen rowBase (Array.emptyWithCapacity rowLen))
      Array.append] =
    #[foldRange half
      (fun col i =>
        let v := foldRange gf.lin.size
          (fun acc idx =>
            match gf.lin[idx]? with
            | none => acc
            | some (c, w) =>
              let kc := cols[base + c]?.getD #[]
              let lo := kc[i]?.getD 0
              let hi := kc[i + half]?.getD 0
              let wr := nativeKaratsuba w r
              Model.Field.eadd acc
                (Model.Field.eadd (nativeMulBase w lo)
                  (nativeMulBase wr (Model.Field.add lo hi))))
          zero
        col.push v)
      (Array.emptyWithCapacity half)] :=
    congrArg (fun c => #[c]) (hlin gf.lin)
  have hstep : (fun (stateCols : Array (Array E)) (g : Nat) =>
      match gf.groups[g]? with
      | none => stateCols
      | some (left, right) =>
        let kc := cols[base + left]?.getD #[]
        let leftCol := parReduce16 512 half
          (fun rowBase rowLen =>
            foldRangeLoop
              (fun (col : Array E) i => col.push (interpKFlat (kc[i]?.getD 0) (kc[i + half]?.getD 0) r))
              rowLen rowBase (Array.emptyWithCapacity rowLen))
          Array.append
        let rightCol := parReduce16 512 half
          (fun rowBase rowLen =>
            foldRangeLoop
              (fun (col : Array E) i =>
                let v := foldRange right.size
                  (fun acc idx =>
                    match right[idx]? with
                    | none => acc
                    | some (c, w) =>
                      let kc := cols[base + c]?.getD #[]
                      let lo := kc[i]?.getD 0
                      let hi := kc[i + half]?.getD 0
                      let wr := planarEmul w r
                      planarEadd acc
                        (planarEadd (planarMulBase w lo)
                          (planarMulBase wr (Model.Field.add lo hi))))
                  zero
                col.push v)
              rowLen rowBase (Array.emptyWithCapacity rowLen))
          Array.append
        (stateCols.push leftCol).push rightCol) =
    (fun (stateCols : Array (Array E)) (g : Nat) =>
      match gf.groups[g]? with
      | none => stateCols
      | some (left, right) =>
        let kc := cols[base + left]?.getD #[]
        let leftCol := foldRange half
          (fun (col : Array E) i =>
            let lo := kc[i]?.getD 0
            let hi := kc[i + half]?.getD 0
            col.push (Model.Bus.interpK lo hi r))
          (Array.emptyWithCapacity half)
        let rightCol := foldRange half
          (fun (col : Array E) i =>
            let v := foldRange right.size
              (fun acc idx =>
                match right[idx]? with
                | none => acc
                | some (c, w) =>
                  let kc := cols[base + c]?.getD #[]
                  let lo := kc[i]?.getD 0
                  let hi := kc[i + half]?.getD 0
                  let wr := nativeKaratsuba w r
                  Model.Field.eadd acc
                    (Model.Field.eadd (nativeMulBase w lo)
                      (nativeMulBase wr (Model.Field.add lo hi))))
              zero
            col.push v)
          (Array.emptyWithCapacity half)
        (stateCols.push leftCol).push rightCol) := by
    funext stateCols g
    cases gf.groups[g]? with
    | none => rfl
    | some lr =>
      rcases lr with ⟨left, right⟩
      have hleft : parReduce16 512 half
          (fun rowBase rowLen =>
            foldRangeLoop
              (fun (col : Array E) i =>
                col.push (interpKFlat ((cols[base + left]?.getD #[])[i]?.getD 0)
                  ((cols[base + left]?.getD #[])[i + half]?.getD 0) r))
              rowLen rowBase (Array.emptyWithCapacity rowLen))
          Array.append =
        foldRange half
          (fun (col : Array E) i =>
            col.push (Model.Bus.interpK ((cols[base + left]?.getD #[])[i]?.getD 0)
              ((cols[base + left]?.getD #[])[i + half]?.getD 0) r))
          (Array.emptyWithCapacity half) := by
        unfold parReduce16 foldRange
        simp only [funext (fun a => funext (fun b => funext (fun t => interpKFlat_eq a b t)))]
        exact parTreeReduce_push_eq
          (fun i => Model.Bus.interpK ((cols[base + left]?.getD #[])[i]?.getD 0)
            ((cols[base + left]?.getD #[])[i + half]?.getD 0) r)
          4 512 0 half
      dsimp only []
      rw [hleft, hlin right]
  exact congr (congrArg (foldRange gf.groups.size) hstep) hinit

private theorem tableMessageEFlat_eq (constant : E) (state : Array (Array E))
    (eqr : Array E) (half : Nat) (atOne : Bool) :
    tableMessageEFlat constant state eqr half atOne =
      tableMessageE constant state eqr half atOne := by
  unfold tableMessageEFlat tableMessageE parReduce16 foldRange
  simp only [planarEadd_eq, planarEmul_eq]
  let pairOp (a b : E × E) : E × E := (Model.Field.eadd a.1 b.1, Model.Field.eadd a.2 b.2)
  let rowFn (i : Nat) : E × E :=
    let endIdx := if atOne then i + half else i
    let linEnd := (state[0]?.getD #[])[endIdx]?.getD zero
    let (ep, sl) := foldRangeLoop
      (fun (epG, slG) g =>
        let lCol := state[1 + 2 * g]?.getD #[]
        let rCol := state[2 + 2 * g]?.getD #[]
        let lEnd := lCol[endIdx]?.getD zero
        let rEnd := rCol[endIdx]?.getD zero
        let lSum := Model.Field.eadd (lCol[i]?.getD zero) (lCol[i + half]?.getD zero)
        let rSum := Model.Field.eadd (rCol[i]?.getD zero) (rCol[i + half]?.getD zero)
        (Model.Field.eadd epG (nativeKaratsuba lEnd rEnd),
          Model.Field.eadd slG (nativeKaratsuba lSum rSum)))
      ((state.size - 1) / 2) 0 (linEnd, zero)
    let eqw := eqr[i]?.getD zero
    (nativeKaratsuba eqw ep, nativeKaratsuba eqw sl)
  have hpar := parTreeReduce_monoid pairOp (zero, zero)
    (fun a b c => pair_eadd_assoc a b c) pair_eadd_zero_right rowFn 4 512 0 half
  have hshift := foldRangeLoop_monoid pairOp (zero, zero)
    (fun a b c => pair_eadd_assoc a b c) pair_eadd_zero_right rowFn (constant, zero) 0 half
  have hlhs := congrArg (fun p : E × E => (Model.Field.eadd constant p.1, p.2)) hpar
  refine hlhs.trans ?_
  have hfst : (Model.Field.eadd constant (foldRangeLoop (fun s i => pairOp s (rowFn i))
        half 0 (zero, zero)).1,
      (foldRangeLoop (fun s i => pairOp s (rowFn i)) half 0 (zero, zero)).2) =
      pairOp (constant, zero)
        (foldRangeLoop (fun s i => pairOp s (rowFn i)) half 0 (zero, zero)) := by
    simp [pairOp, eadd_zero_left_model]
  rw [hfst, hshift]

theorem foldTable_flat_refines (state : Array (Array E)) (r : E) (half : Nat) :
    foldTableFlat state r half = foldTableState state r half := by
  simp only [foldTableFlat, foldTableState, foldRange]
  congr 1
  funext acc c
  congr 1
  unfold parReduce16
  simp only [interpFlat_fun_eq]
  exact parTreeReduce_push_eq
    (fun i => Model.Bus.interp ((state[c]?.getD #[])[i]?.getD zero)
      ((state[c]?.getD #[])[i + half]?.getD zero) r)
    4 512 0 half

private theorem constraintsRoundMsgsFlat_eq (airs : Array AirTable) (gForms : Array GroupedForm)
    (cols : Array (Array K)) (weights : Array E)
    (states : Array (Option (Array (Array E)))) (eqr : Array E)
    (m half : Nat) (atOne : Bool) :
    constraintsRoundMsgsFlat airs gForms cols weights states eqr m half atOne =
      constraintsRoundMsgs airs gForms cols weights states eqr m half atOne := by
  unfold constraintsRoundMsgsFlat constraintsRoundMsgs
  simp only [planarEadd_eq, planarEmul_eq, tableMessageEFlat_eq, tableMessageKFlat_eq]
  rfl

private theorem constraintsUpdateTablesFlat_eq (airs : Array AirTable) (gForms : Array GroupedForm)
    (cols : Array (Array K)) (weights : Array E)
    (states : Array (Option (Array (Array E))))
    (m half : Nat) (rk eqK : E) :
    constraintsUpdateTablesFlat airs gForms cols weights states m half rk eqK =
      constraintsUpdateTables airs gForms cols weights states m half rk eqK := by
  unfold constraintsUpdateTablesFlat constraintsUpdateTables
  simp only [planarEmul_eq, foldTable_flat_refines, joinTableStateFlat_eq]
  rfl

private theorem constraintsRoundsFoldFlat_eq (airs : Array AirTable) (gForms : Array GroupedForm)
    (cols : Array (Array K)) (zeta : Array E) (n : Nat)
    (eqr0 chi0 : Array E) (claim0 : E) (weights0 : Array E)
    (states0 : Array (Option (Array (Array E)))) (ps : ProverState) :
    constraintsRoundsFoldFlat airs gForms cols zeta n eqr0 chi0 claim0 weights0 states0 ps =
      constraintsRoundsFold airs gForms cols zeta n eqr0 chi0 claim0 weights0 states0 ps := by
  unfold constraintsRoundsFoldFlat constraintsRoundsFold
  simp only [planarEadd_eq, planarEmul_eq, constraintsRoundMsgsFlat_eq,
    shrinkEqHighFlat_eq, constraintsUpdateTablesFlat_eq]

theorem proveConstraints_flat_refines (airs : Array AirTable) (cols : Array (Array K))
    (zeta : Array E) (ps : ProverState) :
    proveConstraintsFlat airs cols zeta ps = proveConstraints airs cols zeta ps := by
  unfold proveConstraintsFlat proveConstraints
  simp only [eqTableArrayFlat_eq, planarEadd_eq, constraintsRoundsFoldFlat_eq]
  unfold foldRange
  apply foldRangeLoop_congr_lt
  intro ⟨claimsAcc, curPs⟩ t _
  dsimp only []
  let n := foldRangeLoop
    (fun acc t => max acc (airs[t]?.map Spec.Bus.AirTable.tau |>.getD 0)) airs.size 0 0
  let gForms := foldRangeLoop
    (fun acc t =>
      acc.push (buildGroupedForm (airs[t]?.map Spec.Bus.AirTable.form |>.getD (emptyBusForm 0))))
    airs.size 0 (Array.emptyWithCapacity airs.size)
  let eqr0 := eqTable (zeta.extract 0 (n - 1))
  let chi0 := Array.replicate n zero
  let claim0 := foldRangeLoop
    (fun acc t => Model.Field.eadd acc (airs[t]?.map Spec.Bus.AirTable.sigma |>.getD zero))
    airs.size 0 zero
  let weights0 := Array.replicate airs.size one
  let states0 : Array (Option (Array (Array E))) := Array.replicate airs.size none
  let chi := (constraintsRoundsFold airs gForms cols zeta n
    eqr0 chi0 claim0 weights0 states0 ps).2.1
  let tau := airs[t]?.map Spec.Bus.AirTable.tau |>.getD 0
  let base := airs[t]?.map Spec.Bus.AirTable.base |>.getD 0
  let nCols := airs[t]?.map Spec.Bus.AirTable.nCols |>.getD 0
  let chiT := chi.extract 0 tau
  have hevals : parReduce16 2 nCols
      (fun b l =>
        foldRangeLoop
          (fun acc c =>
            acc.push (mleEvalWithEqFlat (cols[base + c]?.getD #[]) (eqTable chiT)))
          l b (Array.emptyWithCapacity l))
      Array.append =
    foldRangeLoop
      (fun acc c => acc.push (mleEval (cols[base + c]?.getD #[]) chiT))
      nCols 0 (Array.emptyWithCapacity nCols) := by
    simp only [mleEvalWithEqFlat_eq_table]
    unfold parReduce16
    exact parTreeReduce_push_eq _ 4 2 0 nCols
  exact congrArg (fun evals => (claimsAcc.push ⟨chiT, evals⟩, addScalars curPs evals)) hevals

private theorem buildColumnsFlat_eq (program : Array Spec.Vm.Op) (sized : SizedRun)
    (message : Array K) :
    buildColumnsFlat program sized message = buildColumns program sized message := by
  unfold buildColumnsFlat buildColumns
  dsimp only []
  let keccakRows := sized.trace.tables[opKeccak]?.getD #[]
  let zeroPerm := Model.Keccak.keccakF1600 Model.Layout.zeroState25
  let rowPerm (step : Nat) : Model.Keccak.State25 :=
    Model.Keccak.keccakF1600
      (inputState25 program sized.trace.memory (keccakRows[step]?.getD default))
  have hrp : parReduce16 256 keccakRows.size
      (fun base len =>
        foldRangeLoop (fun out step => out.push (rowPerm step))
          len base (Array.emptyWithCapacity len))
      Array.append =
    foldRangeLoop (fun out step => out.push (rowPerm step))
      keccakRows.size 0 (Array.emptyWithCapacity keccakRows.size) := by
    unfold parReduce16
    exact parTreeReduce_push_eq rowPerm 4 256 0 keccakRows.size
  have hout : foldRange keccakRows.size
      (fun cols step =>
        let outState := (parReduce16 256 keccakRows.size
          (fun base len =>
            foldRangeLoop (fun out step => out.push (rowPerm step))
              len base (Array.emptyWithCapacity len))
          Array.append)[step]?.getD zeroPerm
        foldRange stateLanes
          (fun cur lane =>
            cur.modify lane (fun col => col.setIfInBounds step (outState.toSpec[lane]?.getD 0)))
          cols)
      (foldRange stateLanes
        (fun acc lane =>
          acc.push (Array.replicate (1 <<< (sized.layout.taus[opKeccak]?.getD 0))
            (zeroPerm.toSpec[lane]?.getD 0)))
        (Array.emptyWithCapacity stateLanes)) =
    foldRange keccakRows.size
      (fun cols step =>
        let outState := rowPerm step
        foldRange stateLanes
          (fun cur lane =>
            cur.modify lane (fun col => col.setIfInBounds step (outState.toSpec[lane]?.getD 0)))
          cols)
      (foldRange stateLanes
        (fun acc lane =>
          acc.push (Array.replicate (1 <<< (sized.layout.taus[opKeccak]?.getD 0))
            (zeroPerm.toSpec[lane]?.getD 0)))
        (Array.emptyWithCapacity stateLanes)) := by
    rw [hrp]
    unfold foldRange
    apply foldRangeLoop_congr_lt
    intro cols step hlt
    rw [precomputed_array_getD rowPerm zeroPerm keccakRows.size step hlt]
  rw [hout]
  rfl

theorem proveBus_flat_refines (program : Array Spec.Vm.Op) (iv : ByteArray)
    (publicInput : Array E) (bundle : WitnessBundle) :
    proveBusAndConstraintsFlat program iv publicInput bundle =
      proveBusAndConstraints program iv publicInput bundle := by
  unfold proveBusAndConstraintsFlat proveBusAndConstraints
  simp only [buildColumnsFlat_eq, proveBalance_flat_refines, proveConstraints_flat_refines]

end LeanVmXmss.Proofs.Bus
