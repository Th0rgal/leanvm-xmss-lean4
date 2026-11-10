import Model.Layout.Scalar
import Proofs.Vm.GPow
import Proofs.Keccak.Registers
import Proofs.Pcs.Refinement

namespace LeanVmXmss.Proofs.Layout

open Spec.Field (K E)
open Spec.Layout
open LeanVmXmss.Model.Layout

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem kappaOf_refines_spec (logMem logBytecode : Nat) (taus : Fin nTables → Nat) (col : Nat) :
    Model.Layout.kappaOf logMem logBytecode taus col =
      Spec.Layout.kappaOf logMem logBytecode taus col :=
  rfl

theorem placementsOf_refines_spec (logMem logBytecode : Nat) (taus : Fin nTables → Nat) :
    Model.Layout.placementsOf logMem logBytecode taus =
      Spec.Layout.placementsOf logMem logBytecode taus :=
  rfl

theorem nColumns_val : nColumns = 163 := by decide

theorem qKeccakSlots_val : qKeccakSlots = 50 := by decide

theorem slotLog_val : slotLog = 6 := by decide

theorem qKeccakSpare_val : qKeccakSpare = 14 := by decide

theorem xiFormBase_val : xiFormBase = 2 := by decide

theorem schema_table_contiguous (t : Fin nTables) (ht : t.val + 1 < nTables) :
    tableBase ⟨t.val + 1, ht⟩ = tableBase t + tableWidth t := by
  rcases t with ⟨tv, htv⟩
  have hcases : tv = 0 ∨ tv = 1 ∨ tv = 2 ∨ tv = 3 ∨ tv = 4 := by
    change tv + 1 < 6 at ht
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem schema_first_base : tableBase ⟨0, by decide⟩ = nGlobal := rfl

theorem schema_last_end :
    tableBase ⟨5, by decide⟩ + tableWidth ⟨5, by decide⟩ = nColumns := rfl

theorem spareLocal_strict_mono (j k : Nat) (hjk : j < k) (hk : k < qKeccakSpare) :
    spareLocal j < spareLocal k := by
  change k < 14 at hk
  have hj : j < 14 := Nat.lt_trans hjk hk
  cases hkj : decide (k < keccakIn) with
  | true =>
    have hklt : k < keccakIn := of_decide_eq_true hkj
    have hjlt : j < keccakIn := Nat.lt_trans hjk hklt
    simp [spareLocal, hjlt, hklt, hjk]
  | false =>
    have hkge : ¬ k < keccakIn := of_decide_eq_false hkj
    cases hjj : decide (j < keccakIn) with
    | true =>
      have hjlt : j < keccakIn := of_decide_eq_true hjj
      simp only [spareLocal, hjlt, hkge, ite_true, ite_false]
      change j < 63 + (k - 13)
      change j < 13 at hjlt
      omega
    | false =>
      have hjge : ¬ j < keccakIn := of_decide_eq_false hjj
      simp only [spareLocal, hjge, hkge, ite_false]
      change 63 + (j - 13) < 63 + (k - 13)
      change ¬ j < 13 at hjge
      change ¬ k < 13 at hkge
      omega

theorem spareLocal_not_value_lane (k : Nat) (hk : k < qKeccakSpare) :
    spareLocal k < keccakIn ∨ (keccakCnt ≤ spareLocal k ∧ spareLocal k < keccakWidth) := by
  change k < 14 at hk
  cases hkj : decide (k < keccakIn) with
  | true =>
    have hklt : k < keccakIn := of_decide_eq_true hkj
    left
    simp only [spareLocal, hklt, ite_true]
  | false =>
    have hkge : ¬ k < keccakIn := of_decide_eq_false hkj
    simp only [spareLocal, hkge, ite_false]
    right
    change ¬ k < 13 at hkge
    have hkeq : k = 13 := by omega
    subst k
    decide

theorem keccakValue_output (l : Nat) (hl : l < stateLanes) :
    keccakValue (tableBase ⟨5, by decide⟩ + keccakOut + l) = some (KeccakLane.output l) := by
  change l < 25 at hl
  have h1 : ¬ 73 + 38 + l < 73 := by omega
  have h2 : ¬ 73 + 38 + l - 73 ≥ 90 := by omega
  have h3 : ¬ 73 + 38 + l - 73 < 13 := by omega
  have h4 : (decide (63 ≤ 73 + 38 + l - 73) && decide (73 + 38 + l - 73 < 64)) = false := by
    cases hd : decide (63 ≤ 73 + 38 + l - 73) with
    | false => rfl
    | true =>
      have hge := of_decide_eq_true hd
      omega
  have h5 : ¬ 73 + 38 + l - 73 - 13 < 25 := by omega
  have h6 : 73 + 38 + l - 73 - 13 < 50 := by omega
  have h7 : 73 + 38 + l - 73 - 13 - 25 = l := by omega
  change (if 73 + 38 + l < 73 then none else
    if 73 + 38 + l - 73 ≥ 90 then none else
      match
        if 73 + 38 + l - 73 < 13 then some (50 + (73 + 38 + l - 73))
        else if (decide (63 ≤ 73 + 38 + l - 73) && decide (73 + 38 + l - 73 < 64)) = true then
          some (63 + (73 + 38 + l - 73 - 63))
        else none
      with
      | some s => some (KeccakLane.slot s)
      | none =>
        if 73 + 38 + l - 73 < 13 then none else
          if 73 + 38 + l - 73 - 13 < 25 then some (KeccakLane.slot (73 + 38 + l - 73 - 13))
          else if 73 + 38 + l - 73 - 13 < 50 then some (KeccakLane.output (73 + 38 + l - 73 - 13 - 25))
          else none) = some (KeccakLane.output l)
  simp [h1, h2, h3, h4, h5, h6, h7]

theorem keccakValue_input (l : Nat) (hl : l < stateLanes) :
    keccakValue (tableBase ⟨5, by decide⟩ + keccakIn + l) = some (KeccakLane.slot l) := by
  change l < 25 at hl
  have h1 : ¬ 73 + 13 + l < 73 := by omega
  have h2 : ¬ 73 + 13 + l - 73 ≥ 90 := by omega
  have h3 : ¬ 73 + 13 + l - 73 < 13 := by omega
  have h4 : (decide (63 ≤ 73 + 13 + l - 73) && decide (73 + 13 + l - 73 < 64)) = false := by
    cases hd : decide (63 ≤ 73 + 13 + l - 73) with
    | false => rfl
    | true =>
      have hge := of_decide_eq_true hd
      omega
  have h5 : 73 + 13 + l - 73 - 13 < 25 := by omega
  have h6 : 73 + 13 + l - 73 - 13 = l := by omega
  change (if 73 + 13 + l < 73 then none else
    if 73 + 13 + l - 73 ≥ 90 then none else
      match
        if 73 + 13 + l - 73 < 13 then some (50 + (73 + 13 + l - 73))
        else if (decide (63 ≤ 73 + 13 + l - 73) && decide (73 + 13 + l - 73 < 64)) = true then
          some (63 + (73 + 13 + l - 73 - 63))
        else none
      with
      | some s => some (KeccakLane.slot s)
      | none =>
        if 73 + 13 + l - 73 < 13 then none else
          if 73 + 13 + l - 73 - 13 < 25 then some (KeccakLane.slot (73 + 13 + l - 73 - 13))
          else if 73 + 13 + l - 73 - 13 < 50 then some (KeccakLane.output (73 + 13 + l - 73 - 13 - 25))
          else none) = some (KeccakLane.slot l)
  simp [h1, h2, h3, h4, h6, hl]

theorem keccakValue_spare (k : Nat) (hk : k < qKeccakSpare) :
    keccakValue (tableBase ⟨5, by decide⟩ + spareLocal k) = some (KeccakLane.slot (qKeccakSlots + k)) := by
  change k < 14 at hk
  cases hkj : decide (k < 13) with
  | true =>
    have hklt : k < 13 := of_decide_eq_true hkj
    have hk90 : k < 90 := by omega
    have hsp : spareLocal k = k := by
      change (if k < 13 then k else 63 + (k - 13)) = k
      simp [hklt]
    rw [hsp]
    have h1 : ¬ 73 + k < 73 := by omega
    change (if 73 + k < 73 then none else
      if 73 + k - 73 ≥ 90 then none else
        match
          if 73 + k - 73 < 13 then some (50 + (73 + k - 73))
          else if (decide (63 ≤ 73 + k - 73) && decide (73 + k - 73 < 64)) = true then
            some (63 + (73 + k - 73 - 63))
          else none
        with
        | some s => some (KeccakLane.slot s)
        | none =>
          if 73 + k - 73 < 13 then none else
            if 73 + k - 73 - 13 < 25 then some (KeccakLane.slot (73 + k - 73 - 13))
            else if 73 + k - 73 - 13 < 50 then some (KeccakLane.output (73 + k - 73 - 13 - 25))
            else none) = some (KeccakLane.slot (50 + k))
    simp [h1, hklt, hk90]
  | false =>
    have hkge : ¬ k < 13 := of_decide_eq_false hkj
    have hk13 : k = 13 := by omega
    subst hk13
    rfl

private def keccakLaneInjCheck : Bool :=
  (List.range nColumns).all fun c1 =>
    (List.range nColumns).all fun c2 =>
      c1 == c2 ||
        match keccakValue c1, keccakValue c2 with
        | some s1, some s2 => s1 != s2
        | _, _ => true

private theorem keccakLaneInjCheck_true : keccakLaneInjCheck = true := by
  decide

theorem keccakValue_injective (c1 c2 : Nat) (h1 : c1 < nColumns) (h2 : c2 < nColumns)
    (lane : KeccakLane) (hv1 : keccakValue c1 = some lane) (hv2 : keccakValue c2 = some lane) :
    c1 = c2 := by
  have hall := List.all_eq_true.mp keccakLaneInjCheck_true
  have hrow := hall c1 (List.mem_range.mpr h1)
  have hcell := (List.all_eq_true.mp hrow) c2 (List.mem_range.mpr h2)
  cases hceq : c1 == c2 with
  | true =>
    exact beq_iff_eq.mp hceq
  | false =>
    simp [hceq, hv1, hv2] at hcell

theorem keccakValue_slot_bounded (c : Nat) (hc : c < nColumns) (s : Nat)
    (hv : keccakValue c = some (.slot s)) : s < 1 <<< slotLog := by
  have hcheck :
      ((List.range nColumns).all fun col =>
        match keccakValue col with
        | some (.slot slot) => decide (slot < 1 <<< slotLog)
        | _ => true) = true := by
    decide
  have hcol := (List.all_eq_true.mp hcheck) c (List.mem_range.mpr hc)
  simp [hv] at hcol
  exact hcol

theorem sharedPushPull_size (logMem logBytecode : Nat) :
    (sharedPushBlocks logMem logBytecode).size = 3 ∧
      (sharedPullBlocks logMem logBytecode).size = 3 := by
  simp [sharedPushBlocks, sharedPullBlocks]

theorem tableFlushes_sizes :
    (tableFlushes ⟨0, by decide⟩).push.size = 5 ∧
    (tableFlushes ⟨0, by decide⟩).pull.size = 5 ∧
    (tableFlushes ⟨1, by decide⟩).push.size = 5 ∧
    (tableFlushes ⟨1, by decide⟩).pull.size = 5 ∧
    (tableFlushes ⟨2, by decide⟩).push.size = 3 ∧
    (tableFlushes ⟨2, by decide⟩).pull.size = 3 ∧
    (tableFlushes ⟨3, by decide⟩).push.size = 5 ∧
    (tableFlushes ⟨3, by decide⟩).pull.size = 5 ∧
    (tableFlushes ⟨4, by decide⟩).push.size = 5 ∧
    (tableFlushes ⟨4, by decide⟩).pull.size = 5 ∧
    (tableFlushes ⟨5, by decide⟩).push.size = 28 ∧
    (tableFlushes ⟨5, by decide⟩).pull.size = 28 := by
  decide

theorem tableFlushes_paired (t : Fin nTables) :
    (tableFlushes t).push.size = (tableFlushes t).pull.size := by
  rcases tableFlushes_sizes with ⟨h0a, h0b, h1a, h1b, h2a, h2b, h3a, h3b, h4a, h4b, h5a, h5b⟩
  rcases t with ⟨tv, htv⟩
  have hcases : tv = 0 ∨ tv = 1 ∨ tv = 2 ∨ tv = 3 ∨ tv = 4 ∨ tv = 5 := by
    change tv < 6 at htv
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0a.trans h0b.symm
  · exact h1a.trans h1b.symm
  · exact h2a.trans h2b.symm
  · exact h3a.trans h3b.symm
  · exact h4a.trans h4b.symm
  · exact h5a.trans h5b.symm

theorem tableCountColumns_sizes :
    (tableCountColumns ⟨0, by decide⟩).size = 4 ∧
    (tableCountColumns ⟨1, by decide⟩).size = 4 ∧
    (tableCountColumns ⟨2, by decide⟩).size = 2 ∧
    (tableCountColumns ⟨3, by decide⟩).size = 4 ∧
    (tableCountColumns ⟨4, by decide⟩).size = 4 ∧
    (tableCountColumns ⟨5, by decide⟩).size = 27 := by
  decide

theorem busBlocks_counts (logMem logBytecode : Nat) (rows taus : Fin nTables → Nat) :
    let (push, pull, count) := busBlocks logMem logBytecode rows taus
    push.size = 54 ∧ pull.size = 54 ∧ count.size = 45 := by
  rcases tableFlushes_sizes with
    ⟨hp0, hq0, hp1, hq1, hp2, hq2, hp3, hq3, hp4, hq4, hp5, hq5⟩
  rcases tableCountColumns_sizes with ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩
  have hs := sharedPushPull_size logMem logBytecode
  simp only [busBlocks, List.foldl_cons, List.foldl_nil, Array.size_append, Array.size_map,
    hs.1, hs.2, hp0, hq0, hp1, hq1, hp2, hq2, hp3, hq3, hp4, hq4, hp5, hq5,
    hc0, hc1, hc2, hc3, hc4, hc5]
  decide

private theorem gpowLoop_inv (rem idx : Nat) (acc : Array K)
    (hsz : acc.size = idx + 1)
    (hval : ∀ i, i < acc.size → acc[i]? = some (Spec.Xmss.gpow i)) :
    (Model.Pcs.Ntt.foldRangeLoop gpowStep rem idx (acc, Spec.Xmss.gpow idx)).1.size =
      idx + rem + 1 ∧
    ∀ i, i < (Model.Pcs.Ntt.foldRangeLoop gpowStep rem idx (acc, Spec.Xmss.gpow idx)).1.size →
      (Model.Pcs.Ntt.foldRangeLoop gpowStep rem idx (acc, Spec.Xmss.gpow idx)).1[i]? =
        some (Spec.Xmss.gpow i) := by
  induction rem generalizing idx acc with
  | zero =>
    dsimp only [Proofs.Pcs.foldRangeLoop_zero]
    refine ⟨by omega, hval⟩
  | succ rem ih =>
    rw [Proofs.Pcs.foldRangeLoop_succ]
    have hstep : Model.Vm.scalarGeneratorStep (Spec.Xmss.gpow idx) = Spec.Xmss.gpow (idx + 1) := by
      rw [Proofs.Vm.scalarGeneratorStep_eq]
      rfl
    have heq : gpowStep (acc, Spec.Xmss.gpow idx) idx =
        (acc.push (Spec.Xmss.gpow (idx + 1)), Spec.Xmss.gpow (idx + 1)) := by
      unfold gpowStep
      dsimp only []
      rw [hstep]
    rw [heq]
    have hsz' : (acc.push (Spec.Xmss.gpow (idx + 1))).size = (idx + 1) + 1 := by
      rw [Array.size_push, hsz]
    have hval' : ∀ i, i < (acc.push (Spec.Xmss.gpow (idx + 1))).size →
        (acc.push (Spec.Xmss.gpow (idx + 1)))[i]? = some (Spec.Xmss.gpow i) := by
      intro i hi
      rw [Proofs.Vm.array_push_lookup]
      by_cases he : i = acc.size
      · subst he
        simp only [↓reduceIte, hsz]
      · simp only [he, ↓reduceIte]
        apply hval
        rw [Array.size_push] at hi
        omega
    rcases ih (idx + 1) (acc.push (Spec.Xmss.gpow (idx + 1))) hsz' hval' with ⟨h1, h2⟩
    refine ⟨by omega, h2⟩

theorem gpowTable_lookup (limit n : Nat) (hn : n ≤ limit) :
    (gpowTable limit)[n]? = some (Spec.Xmss.gpow n) := by
  have hinit_eq : ((Array.emptyWithCapacity (limit + 1)).push (1 : K)) = #[1] := rfl
  have hsz0 : (#[(1 : K)]).size = 0 + 1 := rfl
  have hval0 : ∀ i, i < (#[(1 : K)]).size → (#[(1 : K)])[i]? = some (Spec.Xmss.gpow i) := by
    intro i hi
    have hi0 : i = 0 := by
      change i < 1 at hi
      omega
    subst hi0
    rfl
  have hinv := gpowLoop_inv limit 0 #[1] hsz0 hval0
  have hfold : gpowTable limit =
      (Model.Pcs.Ntt.foldRangeLoop gpowStep limit 0 (#[1], Spec.Xmss.gpow 0)).1 := by
    unfold gpowTable Model.Pcs.Ntt.foldRange
    rw [hinit_eq]
    rfl
  rw [hfold]
  apply hinv.2
  omega

theorem gAt_gpowTable_eq (limit n : Nat) :
    gAt (gpowTable limit) n = Spec.Xmss.gpow n := by
  unfold gAt
  by_cases hn : n ≤ limit
  · rw [gpowTable_lookup limit n hn]
  · have hinit_eq : ((Array.emptyWithCapacity (limit + 1)).push (1 : K)) = #[1] := rfl
    have hsz0 : (#[(1 : K)]).size = 0 + 1 := rfl
    have hval0 : ∀ i, i < (#[(1 : K)]).size → (#[(1 : K)])[i]? = some (Spec.Xmss.gpow i) := by
      intro i hi
      have hi0 : i = 0 := by
        change i < 1 at hi
        omega
      subst hi0
      rfl
    have hinv := gpowLoop_inv limit 0 #[1] hsz0 hval0
    have hfold : gpowTable limit =
        (Model.Pcs.Ntt.foldRangeLoop gpowStep limit 0 (#[1], Spec.Xmss.gpow 0)).1 := by
      unfold gpowTable Model.Pcs.Ntt.foldRange
      rw [hinit_eq]
      rfl
    have hge : (gpowTable limit).size ≤ n := by
      rw [hfold, hinv.1]
      omega
    rw [Array.getElem?_eq_none hge]

theorem bytecodeRowFast_eq (limit : Nat) (op : Spec.Vm.Op) :
    bytecodeRowFast (gpowTable limit) op = bytecodeRow op := by
  cases op <;>
    simp only [bytecodeRowFast, bytecodeRow, opTag, gAt_gpowTable_eq]

theorem bytecodeColumnsFast_refines_spec (prog : Array Spec.Vm.Op) :
    bytecodeColumnsFast prog = bytecodeColumns prog := by
  unfold bytecodeColumnsFast bytecodeColumns
  simp only [bytecodeRowFast_eq]

theorem range_eight : Array.range 8 = #[0, 1, 2, 3, 4, 5, 6, 7] := rfl

theorem pushWordLE_data (bytes : ByteArray) (w : UInt64) :
    (pushWordLE bytes w).data = bytes.data ++ (Spec.Keccak.wordBytes w).data := by
  simp only [pushWordLE, Spec.Keccak.wordBytes, range_eight, ByteArray.push]
  apply Array.toList_inj.mp
  simp [Array.toList_append]

theorem wordsBytesFast_refines_spec (ws : Array UInt64) :
    wordsBytesFast ws = Spec.Keccak.wordsBytes ws := by
  have hfold (xs : List UInt64) (acc : ByteArray) :
      (xs.foldl pushWordLE acc).data =
        xs.foldl (fun b w => b ++ (Spec.Keccak.wordBytes w).data) acc.data := by
    induction xs generalizing acc with
    | nil => rfl
    | cons w rest ih =>
      simp only [List.foldl_cons, ih, pushWordLE_data]
  apply ByteArray.ext
  unfold wordsBytesFast Spec.Keccak.wordsBytes
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact hfold ws.toList (ByteArray.emptyWithCapacity (ws.size * 8))

private theorem byteArray_getElem?_eq_data (b : ByteArray) (i : Nat) :
    (b[i]? : Option UInt8) = b.data[i]? := by
  cases h : decide (i < b.size) with
  | true =>
    have hlt : i < b.size := of_decide_eq_true h
    have hlt' : i < b.data.size := hlt
    rw [getElem?_pos b i hlt, getElem?_pos b.data i hlt', ByteArray.getElem_eq_getElem_data]
  | false =>
    have hge : ¬ i < b.size := of_decide_eq_false h
    have hge' : ¬ i < b.data.size := hge
    rw [getElem?_neg b i hge, getElem?_neg b.data i hge']

theorem readWordLE_eq_wordAt (b : ByteArray) (offset : Nat) :
    readWordLE b offset = Spec.Keccak.wordAt b offset := by
  simp [readWordLE, Spec.Keccak.wordAt, byteArray_getElem?_eq_data, List.range_succ, Nat.add_zero]

theorem absorb25Block_toSpec (s : Model.Keccak.State25) (blk : ByteArray) :
    (absorb25Block s blk).toSpec = Spec.Keccak.absorbBlock s.toSpec blk := by
  unfold absorb25Block absorb25 Spec.Keccak.absorbBlock
  let mixed : Model.Keccak.State25 :=
    { s with
      a00 := s.a00 ^^^ readWordLE blk 0
      a01 := s.a01 ^^^ readWordLE blk 8
      a02 := s.a02 ^^^ readWordLE blk 16
      a03 := s.a03 ^^^ readWordLE blk 24
      a04 := s.a04 ^^^ readWordLE blk 32
      a05 := s.a05 ^^^ readWordLE blk 40
      a06 := s.a06 ^^^ readWordLE blk 48
      a07 := s.a07 ^^^ readWordLE blk 56
      a08 := s.a08 ^^^ readWordLE blk 64
      a09 := s.a09 ^^^ readWordLE blk 72
      a10 := s.a10 ^^^ readWordLE blk 80
      a11 := s.a11 ^^^ readWordLE blk 88
      a12 := s.a12 ^^^ readWordLE blk 96
      a13 := s.a13 ^^^ readWordLE blk 104
      a14 := s.a14 ^^^ readWordLE blk 112
      a15 := s.a15 ^^^ readWordLE blk 120
      a16 := s.a16 ^^^ readWordLE blk 128 }
  change (Model.Keccak.keccakF1600 mixed).toSpec = _
  rw [Proofs.Keccak.registers_permutation_refines_spec, Proofs.Keccak.spec_rounds_eq_permute]
  congr 1
  apply Array.ext
  · simp [mixed, Model.Keccak.State25.toSpec, -Array.getElem_range,
      Proofs.Keccak.range_twenty_five]
  · intro i h1 h2
    have hi : i < 25 := by simpa [mixed, Model.Keccak.State25.toSpec] using h1
    have hcases :
        i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
        i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨
        i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 := by
      omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;>
      simp [mixed, Model.Keccak.State25.toSpec, readWordLE_eq_wordAt,
        -Array.getElem_range, Proofs.Keccak.range_twenty_five]

theorem zeroState25_toSpec : zeroState25.toSpec = Spec.Keccak.zero := by
  decide

theorem keccak256Fast_refines_spec (b : ByteArray) :
    keccak256Fast b = Spec.Keccak.keccak256 b := by
  have hfold (blks : List ByteArray) (st : Model.Keccak.State25) :
      (blks.foldl absorb25Block st).toSpec =
        blks.foldl Spec.Keccak.absorbBlock st.toSpec := by
    induction blks generalizing st with
    | nil => rfl
    | cons blk rest ih =>
      simp only [List.foldl_cons, ih, absorb25Block_toSpec]
  unfold keccak256Fast Spec.Keccak.keccak256 Spec.Keccak.hashWithDomain
  have hst :
      ((Spec.Keccak.blocks b 1).foldl absorb25Block zeroState25).toSpec =
        (Spec.Keccak.blocks b 1).foldl Spec.Keccak.absorbBlock Spec.Keccak.zero := by
    rw [← Array.foldl_toList, ← Array.foldl_toList, hfold, zeroState25_toSpec]
  congr 1
  rw [← hst]
  generalize hst' : (Spec.Keccak.blocks b 1).foldl absorb25Block zeroState25 = st
  have hwords :
      Spec.Keccak.wordsBytes #[st.a00, st.a01, st.a02, st.a03] =
        Spec.Keccak.wordsBytes (st.toSpec.extract 0 4) := by
    rfl
  exact hwords

private theorem ofFn_go_toList {n : Nat} (acc : Array Nat) (m : Nat) (hm : m ≤ n) :
    (Array.ofFn.go (fun j : Fin n => j.val) acc m hm).toList =
      acc.toList ++ List.range' (n - m) m := by
  induction m generalizing acc with
  | zero =>
    rw [Array.ofFn.go.eq_2]
    simp
  | succ k ih =>
    rw [Array.ofFn.go.eq_1, ih]
    rw [Array.toList_push, List.append_assoc, List.singleton_append]
    have hsub : n - (k + 1) = n - k - 1 := by omega
    have hstep : n - k - 1 + 1 = n - k := by omega
    rw [hsub, List.range'_succ, hstep]

private theorem array_toList_range_constructive (n : Nat) :
    (Array.range n).toList = List.range n := by
  unfold Array.range Array.ofFn
  rw [ofFn_go_toList]
  have hemp : (Array.emptyWithCapacity n : Array Nat).toList = [] := rfl
  rw [hemp, List.nil_append, Nat.sub_self, List.range_eq_range']

private theorem extract_loop_toList (as : Array UInt8) (rem j : Nat) (bs : Array UInt8)
    (hj : j + rem ≤ as.size) :
    (Array.extract.loop as rem j bs).toList =
      bs.toList ++ (List.range' j rem).map (fun p => as.toList[p]?.getD 0) := by
  induction rem generalizing j bs with
  | zero =>
    rw [Array.extract.loop.eq_1]
    split <;> simp
  | succ rem' ih =>
    have hlt : j < as.size := by omega
    rw [Array.extract.loop.eq_1]
    simp only [hlt, dite_true]
    rw [ih (j + 1) _ (by omega), Array.toList_push, List.append_assoc, List.singleton_append,
      List.range'_succ, List.map_cons]
    have hget : as.getInternal j hlt = as.toList[j]?.getD 0 := by
      change as.toList[j] = as.toList[j]?.getD 0
      rw [List.getElem?_eq_getElem hlt]
      rfl
    rw [hget]

private theorem readWordLE_extract_block (b : ByteArray) (i r : Nat)
    (h : 136 * (i + 1) ≤ b.size) (hr : r + 8 ≤ 136) :
    readWordLE b (136 * i + r) =
      readWordLE (b.extract (136 * i) (136 * (i + 1))) r := by
  have hbyte (k : Nat) (hk : k < 8) :
      b.data[136 * i + (r + k)]? =
        (b.extract (136 * i) (136 * (i + 1))).data[r + k]? := by
    have hd : (b.extract (136 * i) (136 * (i + 1))).data =
        b.data.extract (136 * i) (136 * (i + 1)) := by
      have hemp : ByteArray.empty.data = #[] := rfl
      simp only [ByteArray.extract, ByteArray.copySlice, hemp, Array.extract_empty,
        Array.empty_append, Array.append_empty]
      congr 1
      omega
    have hextract : (b.data.extract (136 * i) (136 * (i + 1))).toList =
        (List.range' (136 * i) 136).map (fun p => b.data.toList[p]?.getD 0) := by
      unfold Array.extract
      have hsz : (min (136 * (i + 1)) b.data.size).sub (136 * i) = 136 := by
        change (min (136 * (i + 1)) b.size) - 136 * i = 136
        omega
      rw [hsz]
      have hloop := extract_loop_toList b.data 136 (136 * i) (Array.emptyWithCapacity 136) (by
        change 136 * i + 136 ≤ b.size
        omega)
      have hemp2 : (Array.emptyWithCapacity 136 : Array UInt8).toList = [] := rfl
      rw [hemp2, List.nil_append] at hloop
      exact hloop
    rw [hd, ← Array.getElem?_toList, ← Array.getElem?_toList, hextract]
    have hrk : r + k < 136 := by omega
    simp only [List.getElem?_map, List.getElem?_range', hrk, Option.map_some, Nat.one_mul]
    have hlt1 : 136 * i + (r + k) < b.data.toList.length := by
      change 136 * i + (r + k) < b.size
      omega
    rw [List.getElem?_eq_getElem hlt1]
    rfl
  unfold readWordLE
  simp only [byteArray_getElem?_eq_data]
  have hb0 := hbyte 0 (by omega)
  simp only [Nat.add_zero] at hb0
  simp only [Nat.add_assoc, hb0,
    hbyte 1 (by omega), hbyte 2 (by omega), hbyte 3 (by omega),
    hbyte 4 (by omega), hbyte 5 (by omega), hbyte 6 (by omega), hbyte 7 (by omega)]

private theorem absorb25_eq_block (s : Model.Keccak.State25) (b : ByteArray) (i : Nat)
    (h : 136 * (i + 1) ≤ b.size) :
    absorb25 s b (136 * i) = absorb25Block s (b.extract (136 * i) (136 * (i + 1))) := by
  unfold absorb25Block absorb25
  have h0 := readWordLE_extract_block b i 0 h (by omega)
  simp only [Nat.add_zero] at h0
  simp only [Nat.zero_add]
  rw [h0,
    readWordLE_extract_block b i 8 h (by omega),
    readWordLE_extract_block b i 16 h (by omega),
    readWordLE_extract_block b i 24 h (by omega),
    readWordLE_extract_block b i 32 h (by omega),
    readWordLE_extract_block b i 40 h (by omega),
    readWordLE_extract_block b i 48 h (by omega),
    readWordLE_extract_block b i 56 h (by omega),
    readWordLE_extract_block b i 64 h (by omega),
    readWordLE_extract_block b i 72 h (by omega),
    readWordLE_extract_block b i 80 h (by omega),
    readWordLE_extract_block b i 88 h (by omega),
    readWordLE_extract_block b i 96 h (by omega),
    readWordLE_extract_block b i 104 h (by omega),
    readWordLE_extract_block b i 112 h (by omega),
    readWordLE_extract_block b i 120 h (by omega),
    readWordLE_extract_block b i 128 h (by omega)]

theorem keccak256Stream_eq_fast (b : ByteArray) :
    keccak256Stream b = keccak256Fast b := by
  simp only [keccak256Stream, keccak256Fast, Spec.Keccak.blocks, ← Array.foldl_toList,
    Array.toList_push, List.foldl_append, List.foldl_cons, List.foldl_nil,
    Array.toList_map, array_toList_range_constructive]
  have hfold (n : Nat) (hn : 136 * n ≤ b.size) (st : Model.Keccak.State25) :
      (List.range n).foldl (fun s i => absorb25 s b (136 * i)) st =
        ((List.range n).map fun i => b.extract (136 * i) (136 * (i + 1))).foldl absorb25Block st := by
    induction n generalizing st with
    | zero => rfl
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.map_singleton,
        List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons,
        List.foldl_nil, List.foldl_nil]
      rw [ih (by omega) st, absorb25_eq_block _ b k hn]
  rw [hfold (b.size / 136) (Nat.mul_div_le b.size 136) zeroState25]

theorem stackBytecodeColumnsFast_refines_spec (logBytecode : Nat) (cols : Array (Array K)) :
    stackBytecodeColumnsFast logBytecode cols = stackBytecodeColumns logBytecode cols := by
  unfold stackBytecodeColumnsFast stackBytecodeColumns
  simp only [← Array.foldl_toList, array_toList_range_constructive]

theorem fiatShamirIvFast_refines_spec (table : Array K) :
    fiatShamirIvFast table = fiatShamirIv table := by
  unfold fiatShamirIvFast fiatShamirIv
  rw [wordsBytesFast_refines_spec, keccak256Stream_eq_fast, keccak256Fast_refines_spec]

end LeanVmXmss.Proofs.Layout
