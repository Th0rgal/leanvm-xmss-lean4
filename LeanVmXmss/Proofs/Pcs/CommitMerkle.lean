import Model.Pcs.Commit
import Proofs.Layout.Basic
import Proofs.Merkle.Contracts
import Proofs.Pcs.Refinement

namespace LeanVmXmss.Proofs.Pcs

set_option maxHeartbeats 0

open Spec.Field (K)
open Model.Layout (readWordLE absorb25 absorb25Block zeroState25 keccak256Stream)
open Model.Pcs.Commit (absorbWords17 absorbFinal13 hashPair25 subtreeRoot zeroPrefixState
  leafDigest hashLeafVec8From subtreeRootBuf)
open Proofs.Merkle.Contracts (digest32ToSpec digest32ToSpec_bytes wordBytes_size wordsBytes_size)

private theorem wordsBytes_toList_go (ws : List UInt64) (acc : Array UInt8) :
    (ws.foldl (fun b w => b ++ (Spec.Keccak.wordBytes w).data) acc).toList =
      acc.toList ++ (ws.map fun w => (Spec.Keccak.wordBytes w).data.toList).flatten := by
  induction ws generalizing acc with
  | nil => simp
  | cons w rest ih =>
    rw [List.foldl_cons, ih, Array.toList_append, List.map_cons, List.flatten_cons,
      List.append_assoc]

theorem wordsBytes_data_toList (ws : Array UInt64) :
    (Spec.Keccak.wordsBytes ws).data.toList =
      (ws.toList.map fun w => (Spec.Keccak.wordBytes w).data.toList).flatten := by
  unfold Spec.Keccak.wordsBytes
  rw [← Array.foldl_toList, wordsBytes_toList_go]
  rfl

private theorem wordBytes_length (w : UInt64) :
    (Spec.Keccak.wordBytes w).data.toList.length = 8 := by
  rw [Array.length_toList]
  exact wordBytes_size w

private theorem words_flatten_drop (ws : List UInt64) (k : Nat) :
    ((ws.map fun w => (Spec.Keccak.wordBytes w).data.toList).flatten).drop (8 * k) =
      ((ws.drop k).map fun w => (Spec.Keccak.wordBytes w).data.toList).flatten := by
  induction k generalizing ws with
  | zero => simp
  | succ k ih =>
    cases ws with
    | nil => simp
    | cons w rest =>
      have hmul : 8 * (k + 1) = 8 + 8 * k := by omega
      have hlen : (Spec.Keccak.wordBytes w).data.toList.length = 8 := wordBytes_length w
      have hd8 : List.drop 8 (Spec.Keccak.wordBytes w).data.toList = [] :=
        List.drop_eq_nil_of_le (by omega)
      rw [hmul, ← List.drop_drop, List.map_cons, List.flatten_cons]
      rw [List.drop_append_of_le_length (by omega), hd8, List.nil_append, List.drop_succ_cons, ih]

private theorem words_flatten_length (ws : List UInt64) :
    ((ws.map fun w => (Spec.Keccak.wordBytes w).data.toList).flatten).length = 8 * ws.length := by
  induction ws with
  | nil => simp
  | cons w rest ih =>
    rw [List.map_cons, List.flatten_cons, List.length_append, wordBytes_length, ih,
      List.length_cons]
    omega

theorem readWordLE_wordBytes (w : UInt64) :
    readWordLE (Spec.Keccak.wordBytes w) 0 = w := by
  rw [Proofs.Layout.readWordLE_eq_wordAt, Proofs.Merkle.Contracts.wordAt_eq_readLimb,
    Proofs.Merkle.Contracts.wordBytes_eq_encodeBytesK, Proofs.Field.readLimb_refines_spec,
    Proofs.Field.encodeBytesK_refines_spec]
  exact Proofs.Field.read_encoded_limb w

theorem readWordLE_wordsBytes (ws : Array UInt64) (k : Nat) (hk : k < ws.size) :
    readWordLE (Spec.Keccak.wordsBytes ws) (8 * k) = ws.getD k 0 := by
  rw [Proofs.Layout.readWordLE_eq_wordAt, Proofs.Merkle.Contracts.wordAt_eq_readLimb,
    ← Proofs.Field.readLimb_extract]
  have hslice : Proofs.Field.byteSlice (Spec.Keccak.wordsBytes ws) (8 * k) 8 =
      Spec.Keccak.wordBytes (ws.getD k 0) := by
    unfold Proofs.Field.byteSlice
    rw [wordsBytes_data_toList, words_flatten_drop]
    have hk_list : k < ws.toList.length := by simpa using hk
    obtain ⟨hd, tl, hdrop⟩ := List.exists_cons_of_length_pos (l := ws.toList.drop k) (by
      rw [List.length_drop]
      omega)
    have hhd : hd = ws.getD k 0 := by
      have hget : (ws.toList.drop k)[0]? = some hd := by simp [hdrop]
      rw [List.getElem?_drop, Nat.add_zero, Array.getElem?_toList] at hget
      simp [Array.getD_eq_getD_getElem?, hget]
    have hlen : (Spec.Keccak.wordBytes (ws.getD k 0)).data.toList.length = 8 :=
      wordBytes_length (ws.getD k 0)
    have ht8 : List.take 8 (Spec.Keccak.wordBytes (ws.getD k 0)).data.toList =
        (Spec.Keccak.wordBytes (ws.getD k 0)).data.toList :=
      List.take_of_length_le (by omega)
    rw [hdrop, hhd, List.map_cons, List.flatten_cons]
    rw [List.take_append_of_le_length (by omega), ht8]
  rw [hslice, ← Proofs.Merkle.Contracts.wordAt_eq_readLimb, ← Proofs.Layout.readWordLE_eq_wordAt,
    readWordLE_wordBytes]

theorem absorb25_wordsBytes (s : Model.Keccak.State25) (ws : Array UInt64) (i : Nat)
    (hi : 17 * (i + 1) ≤ ws.size) :
    absorb25 s (Spec.Keccak.wordsBytes ws) (136 * i) =
      absorbWords17 s
        (ws.getD (17 * i + 0) 0) (ws.getD (17 * i + 1) 0) (ws.getD (17 * i + 2) 0)
        (ws.getD (17 * i + 3) 0) (ws.getD (17 * i + 4) 0) (ws.getD (17 * i + 5) 0)
        (ws.getD (17 * i + 6) 0) (ws.getD (17 * i + 7) 0) (ws.getD (17 * i + 8) 0)
        (ws.getD (17 * i + 9) 0) (ws.getD (17 * i + 10) 0) (ws.getD (17 * i + 11) 0)
        (ws.getD (17 * i + 12) 0) (ws.getD (17 * i + 13) 0) (ws.getD (17 * i + 14) 0)
        (ws.getD (17 * i + 15) 0) (ws.getD (17 * i + 16) 0) := by
  unfold absorb25 absorbWords17
  have hw (j : Nat) (hj : j < 17) :
      readWordLE (Spec.Keccak.wordsBytes ws) (136 * i + 8 * j) =
        ws.getD (17 * i + j) 0 := by
    have hoff : 136 * i + 8 * j = 8 * (17 * i + j) := by omega
    rw [hoff]
    exact readWordLE_wordsBytes ws (17 * i + j) (by omega)
  have h0 := hw 0 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero] at h0
  apply congrArg Model.Keccak.keccakF1600
  rw [h0, hw 1 (by decide), hw 2 (by decide), hw 3 (by decide), hw 4 (by decide),
    hw 5 (by decide), hw 6 (by decide), hw 7 (by decide), hw 8 (by decide),
    hw 9 (by decide), hw 10 (by decide), hw 11 (by decide), hw 12 (by decide),
    hw 13 (by decide), hw 14 (by decide), hw 15 (by decide), hw 16 (by decide)]
  rfl

private theorem byteArray_set_data (b : ByteArray) (i : Nat) (v : UInt8) :
    (b.set! i v).data = b.data.set! i v := by
  cases b
  rfl

private theorem byteArray_getElem?_eq_data (b : ByteArray) (i : Nat) :
    b[i]? = b.data[i]? := by
  cases h : decide (i < b.size) with
  | true =>
    have hi : i < b.size := of_decide_eq_true h
    have hi' : i < b.data.size := hi
    rw [getElem?_pos b i hi, getElem?_pos b.data i hi']
    rfl
  | false =>
    have hge : ¬ i < b.size := of_decide_eq_false h
    have hge' : ¬ i < b.data.size := hge
    rw [getElem?_neg b i hge, getElem?_neg b.data i hge']

private theorem byteArray_getElem_bang_eq (b : ByteArray) (i : Nat) :
    b[i]! = b.data[i]! := by
  simp [getElem!_def, byteArray_getElem?_eq_data]

private theorem fold_copy_data (tail : ByteArray) (n : Nat) (hn : n ≤ tail.size) (hn2 : n ≤ 136) :
    let f := fun (b : ByteArray) (j : Nat) => b.set! j tail[j]!
    let out := (List.range n).foldl f (ByteArray.mk (Array.replicate 136 0))
    out.data.size = 136 ∧
      ∀ i < 136, out.data[i]? = if i < n then tail.data[i]? else some 0 := by
  dsimp only
  induction n with
  | zero =>
    refine ⟨by simp, ?_⟩
    intro i hi
    simp [hi]
  | succ k ih =>
    obtain ⟨hsz, hget⟩ := ih (by omega) (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize hprev : (List.range k).foldl (fun b j => b.set! j tail[j]!)
      (ByteArray.mk (Array.replicate 136 0)) = prev at hsz hget ⊢
    refine ⟨by simp [byteArray_set_data, hsz], ?_⟩
    intro i hi
    rw [byteArray_set_data, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    cases hki : decide (k = i) with
    | true =>
      have heq : k = i := of_decide_eq_true hki
      subst heq
      have hlt_sz : k < prev.size := by
        change k < prev.data.size
        omega
      have hlt_tail : k < tail.data.size := by
        change k < tail.size
        omega
      simp [hlt_sz, byteArray_getElem_bang_eq, getElem!_pos tail.data k hlt_tail,
        Array.getElem?_eq_getElem hlt_tail]
    | false =>
      have hne : k ≠ i := of_decide_eq_false hki
      simp only [hne, ↓reduceIte, hget i hi]
      cases hlt : decide (i < k) with
      | true =>
        have hik : i < k := of_decide_eq_true hlt
        have hik1 : i < k + 1 := by omega
        simp [hik, hik1]
      | false =>
        have hnik : ¬ i < k := of_decide_eq_false hlt
        have hnik1 : ¬ i < k + 1 := by omega
        simp [hnik, hnik1]

private theorem finalBlock_byte (tail : ByteArray) (ht : tail.size < 135) (i : Nat) (hi : i < 136) :
    (Spec.Keccak.finalBlock tail 1)[i]? =
      if i < tail.size then tail[i]?
      else if i = tail.size then some 1
      else if i = 135 then some 128
      else some 0 := by
  unfold Spec.Keccak.finalBlock
  dsimp only
  obtain ⟨hsz, hget⟩ := fold_copy_data tail tail.size (Nat.le_refl _) (by omega)
  generalize hb0 : (List.range tail.size).foldl (fun b j => b.set! j tail[j]!)
    (ByteArray.mk (Array.replicate 136 0)) = b0 at hsz hget ⊢
  have hb0_tail : b0[tail.size]! = 0 := by
    rw [byteArray_getElem_bang_eq]
    have hlt : tail.size < b0.data.size := by omega
    rw [getElem!_pos b0.data tail.size hlt]
    have hq := hget tail.size (by omega)
    rw [Array.getElem?_eq_getElem hlt] at hq
    simp only [Nat.lt_irrefl, ↓reduceIte] at hq
    exact Option.some.inj hq
  let b1 := b0.set! tail.size (b0[tail.size]! ^^^ 1)
  have hb1_sz : b1.data.size = 136 := by simp [b1, byteArray_set_data, hsz]
  have hb1_135 : b1[135]! = 0 := by
    rw [byteArray_getElem_bang_eq]
    have hlt : 135 < b1.data.size := by omega
    rw [getElem!_pos b1.data 135 hlt]
    have hq : b1.data[135]? = some 0 := by
      simp only [b1, byteArray_set_data, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      have hne : tail.size ≠ 135 := by omega
      simp only [hne, ↓reduceIte]
      simpa [show ¬ 135 < tail.size by omega] using hget 135 (by decide)
    rw [Array.getElem?_eq_getElem hlt] at hq
    exact Option.some.inj hq
  change (b1.set! 135 (b1[135]! ^^^ 128))[i]? = _
  rw [byteArray_getElem?_eq_data, byteArray_getElem?_eq_data tail i, byteArray_set_data,
    Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  cases h135 : decide (135 = i) with
  | true =>
    have heq : 135 = i := of_decide_eq_true h135
    subst heq
    have hlt135 : 135 < b1.size := by
      change 135 < b1.data.size
      omega
    have hnt : ¬ 135 < tail.size := by omega
    have hne : 135 ≠ tail.size := by omega
    have hb1_elem : b1[135]'(by exact hlt135) = 0 := by
      have hbang := hb1_135
      rw [byteArray_getElem_bang_eq] at hbang
      have hlt_d : 135 < b1.data.size := by omega
      rw [getElem!_pos b1.data 135 hlt_d] at hbang
      exact hbang
    simp [hlt135, hb1_elem, hnt, hne]
  | false =>
    have hne135 : 135 ≠ i := of_decide_eq_false h135
    have hne135' : i ≠ 135 := by omega
    simp only [hne135, hne135', ↓reduceIte, b1, byteArray_set_data,
      Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    cases hts : decide (tail.size = i) with
    | true =>
      have heq : tail.size = i := of_decide_eq_true hts
      subst heq
      have hlts : tail.size < b0.size := by
        change tail.size < b0.data.size
        omega
      have hb0_elem : b0[tail.size]'(by exact hlts) = 0 := by
        have hbang := hb0_tail
        rw [byteArray_getElem_bang_eq] at hbang
        have hlt_d : tail.size < b0.data.size := by omega
        rw [getElem!_pos b0.data tail.size hlt_d] at hbang
        exact hbang
      simp [hlts, hb0_elem]
    | false =>
      have hnets : tail.size ≠ i := of_decide_eq_false hts
      have hnets' : i ≠ tail.size := by omega
      simp only [hnets, hnets', ↓reduceIte, hget i hi]

theorem finalBlock_readWordLE_words (ws : Array UInt64) (hws : ws.size ≤ 15) :
    let tail := Spec.Keccak.wordsBytes ws
    let blk := Spec.Keccak.finalBlock tail 1
    (∀ k < ws.size, readWordLE blk (8 * k) = ws.getD k 0) ∧
      readWordLE blk (8 * ws.size) = 1 ∧
      (∀ k, ws.size < k → k < 16 → readWordLE blk (8 * k) = 0) ∧
      readWordLE blk 128 = 0x8000000000000000 := by
  intro tail blk
  have htsz : tail.size = 8 * ws.size := wordsBytes_size ws
  have htlt : tail.size < 135 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    have eq_tail : readWordLE blk (8 * k) = readWordLE tail (8 * k) := by
      unfold readWordLE
      have hb (j : Nat) (hj : j < 8) : blk[8 * k + j]? = tail[8 * k + j]? := by
        have hlt1 : 8 * k + j < 136 := by omega
        have hlt2 : 8 * k + j < tail.size := by omega
        simpa [blk, hlt2] using finalBlock_byte tail htlt (8 * k + j) hlt1
      have hb0 := hb 0 (by decide)
      simp only [Nat.add_zero] at hb0
      simp only [hb0, hb 1 (by decide), hb 2 (by decide), hb 3 (by decide),
        hb 4 (by decide), hb 5 (by decide), hb 6 (by decide), hb 7 (by decide)]
    rw [eq_tail]
    exact readWordLE_wordsBytes ws k hk
  · unfold readWordLE
    have hb0 : blk[8 * ws.size]? = some 1 := by
      have hlt : 8 * ws.size < 136 := by omega
      simpa [blk, htsz] using finalBlock_byte tail htlt (8 * ws.size) hlt
    have hbj (j : Nat) (hj1 : 1 ≤ j) (hj2 : j < 8) : blk[8 * ws.size + j]? = some 0 := by
      have hlt : 8 * ws.size + j < 136 := by omega
      have h1 : ¬ 8 * ws.size + j < tail.size := by omega
      have h2 : 8 * ws.size + j ≠ tail.size := by omega
      have h3 : 8 * ws.size + j ≠ 135 := by omega
      simpa [blk, h1, h2, h3] using finalBlock_byte tail htlt (8 * ws.size + j) hlt
    rw [hb0, hbj 1 (by decide) (by decide), hbj 2 (by decide) (by decide),
      hbj 3 (by decide) (by decide), hbj 4 (by decide) (by decide),
      hbj 5 (by decide) (by decide), hbj 6 (by decide) (by decide),
      hbj 7 (by decide) (by decide)]
    decide
  · intro k hk1 hk2
    unfold readWordLE
    have hbj (j : Nat) (hj : j < 8) : blk[8 * k + j]? = some 0 := by
      have hlt : 8 * k + j < 136 := by omega
      have h1 : ¬ 8 * k + j < tail.size := by omega
      have h2 : 8 * k + j ≠ tail.size := by omega
      have h3 : 8 * k + j ≠ 135 := by omega
      simpa [blk, h1, h2, h3] using finalBlock_byte tail htlt (8 * k + j) hlt
    have hb0 := hbj 0 (by decide)
    simp only [Nat.add_zero] at hb0
    rw [hb0, hbj 1 (by decide), hbj 2 (by decide), hbj 3 (by decide),
      hbj 4 (by decide), hbj 5 (by decide), hbj 6 (by decide), hbj 7 (by decide)]
    decide
  · unfold readWordLE
    have hbj (j : Nat) (hj : j < 7) : blk[128 + j]? = some 0 := by
      have hlt : 128 + j < 136 := by omega
      have h1 : ¬ 128 + j < tail.size := by omega
      have h2 : 128 + j ≠ tail.size := by omega
      have h3 : 128 + j ≠ 135 := by omega
      simpa [blk, h1, h2, h3] using finalBlock_byte tail htlt (128 + j) hlt
    have hb0 := hbj 0 (by decide)
    simp only [Nat.add_zero] at hb0
    have hb7 : blk[128 + 7]? = some 128 := by
      have h1 : ¬ 135 < tail.size := by omega
      have h2 : 135 ≠ tail.size := by omega
      simpa [blk, h1, h2] using finalBlock_byte tail htlt 135 (by decide)
    rw [hb0, hbj 1 (by decide), hbj 2 (by decide), hbj 3 (by decide),
      hbj 4 (by decide), hbj 5 (by decide), hbj 6 (by decide), hb7]
    decide

theorem digest32_words_roundtrip (d : Model.Merkle.Digest32) :
    (⟨Spec.Keccak.wordAt d.toBytes 0, Spec.Keccak.wordAt d.toBytes 8,
      Spec.Keccak.wordAt d.toBytes 16, Spec.Keccak.wordAt d.toBytes 24⟩ :
      Model.Merkle.Digest32) = d := by
  unfold Model.Merkle.Digest32.toBytes
  have rw0 := readWordLE_wordsBytes #[d.lo0, d.lo1, d.hi0, d.hi1] 0 (by simp)
  have rw1 := readWordLE_wordsBytes #[d.lo0, d.lo1, d.hi0, d.hi1] 1 (by simp)
  have rw2 := readWordLE_wordsBytes #[d.lo0, d.lo1, d.hi0, d.hi1] 2 (by simp)
  have rw3 := readWordLE_wordsBytes #[d.lo0, d.lo1, d.hi0, d.hi1] 3 (by simp)
  rw [Proofs.Layout.readWordLE_eq_wordAt] at rw0 rw1 rw2 rw3
  simp at rw0 rw1 rw2 rw3
  cases d
  simp only at rw0 rw1 rw2 rw3
  rw [rw0, rw1, rw2, rw3]

private theorem list_drop_cons {α : Type} (l : List α) (j : Nat) (hj : j < l.length) :
    l.drop j = l[j] :: l.drop (j + 1) := by
  induction l generalizing j with
  | nil => contradiction
  | cons x xs ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simp only [List.length_cons] at hj
      exact ih j (by omega)

private theorem extract_loop_toList {α : Type} (as : Array α) (i j : Nat) (bs : Array α)
    (hj : j + i ≤ as.size) :
    (Array.extract.loop as i j bs).toList =
      bs.toList ++ (as.toList.drop j).take i := by
  induction i generalizing j bs with
  | zero =>
    rw [Array.extract.loop.eq_1]
    split <;> simp
  | succ i ih =>
    rw [Array.extract.loop.eq_1]
    have hlt : j < as.size := by omega
    have hltL : j < as.toList.length := by
      rw [Array.length_toList]
      exact hlt
    simp only [hlt, ↓reduceDIte]
    rw [ih (j + 1) (bs.push (as.getInternal j hlt)) (by omega)]
    rw [Array.toList_push, List.append_assoc, List.singleton_append]
    rw [list_drop_cons as.toList j hltL, List.take_succ_cons]
    rfl

theorem array_extract_toList {α : Type} (as : Array α) (start stop : Nat) :
    (as.extract start stop).toList =
      (as.toList.drop start).take (min stop as.size - start) := by
  unfold Array.extract
  dsimp only
  simp only [Nat.sub_eq]
  by_cases h : min stop as.size - start = 0
  · rw [h, List.take_zero, Array.extract.loop.eq_1]
    split <;> rfl
  · rw [extract_loop_toList as (min stop as.size - start) start _ (by omega)]
    rfl

theorem hashPair25_eq_hashPair (left right : Model.Merkle.Digest32) :
    hashPair25 left right = Model.Merkle.Digest32.hashPair left right := by
  have hcat : left.toBytes ++ right.toBytes =
      Spec.Keccak.wordsBytes
        #[left.lo0, left.lo1, left.hi0, left.hi1, right.lo0, right.lo1, right.hi0, right.hi1] := by
    apply ByteArray.ext
    apply Array.toList_inj.mp
    simp [Model.Merkle.Digest32.toBytes, ByteArray.data_append, wordsBytes_data_toList]
  let ws : Array UInt64 :=
    #[left.lo0, left.lo1, left.hi0, left.hi1, right.lo0, right.lo1, right.hi0, right.hi1]
  have hws : ws.size = 8 := rfl
  obtain ⟨hw_lt, hw_eq, hw_gt, hw_128⟩ := finalBlock_readWordLE_words ws (by simp [ws])
  have hkec : Spec.Keccak.keccak256 (Spec.Keccak.wordsBytes ws) =
      (hashPair25 left right).toBytes := by
    rw [← Proofs.Layout.keccak256Fast_refines_spec, ← Proofs.Layout.keccak256Stream_eq_fast]
    unfold keccak256Stream
    have hsz : (Spec.Keccak.wordsBytes ws).size = 64 := by
      rw [wordsBytes_size, hws]
    have hnfull : (Spec.Keccak.wordsBytes ws).size / 136 = 0 := by omega
    have htail : (Spec.Keccak.wordsBytes ws).extract (136 * 0) (Spec.Keccak.wordsBytes ws).size =
        Spec.Keccak.wordsBytes ws := by
      apply ByteArray.ext
      apply Array.toList_inj.mp
      have hemp : ByteArray.empty.data = #[] := rfl
      simp only [ByteArray.extract, ByteArray.copySlice, hemp, Array.extract_empty,
        Array.empty_append, Array.append_empty, array_extract_toList, Nat.mul_zero,
        Nat.zero_add, List.drop_zero, Nat.sub_zero, ByteArray.size]
      rw [Nat.min_self, ← Array.length_toList, List.take_length]
    have hr0 : Array.range 0 = #[] := rfl
    rw [hnfull]
    simp only [hr0, Array.foldl_empty, htail]
    have hst : absorb25Block zeroState25 (Spec.Keccak.finalBlock (Spec.Keccak.wordsBytes ws) 1) =
        Model.Keccak.keccakF1600
          { zeroState25 with
            a00 := left.lo0
            a01 := left.lo1
            a02 := left.hi0
            a03 := left.hi1
            a04 := right.lo0
            a05 := right.lo1
            a06 := right.hi0
            a07 := right.hi1
            a08 := 1
            a16 := 0x8000000000000000 } := by
      unfold absorb25Block absorb25
      apply congrArg Model.Keccak.keccakF1600
      have h0 := hw_lt 0 (by simp [ws])
      have h1 := hw_lt 1 (by simp [ws])
      have h2 := hw_lt 2 (by simp [ws])
      have h3 := hw_lt 3 (by simp [ws])
      have h4 := hw_lt 4 (by simp [ws])
      have h5 := hw_lt 5 (by simp [ws])
      have h6 := hw_lt 6 (by simp [ws])
      have h7 := hw_lt 7 (by simp [ws])
      have h8 : readWordLE (Spec.Keccak.finalBlock (Spec.Keccak.wordsBytes ws) 1) 64 = 1 := by
        simpa [hws] using hw_eq
      have h9 := hw_gt 9 (by simp [ws]) (by decide)
      have h10 := hw_gt 10 (by simp [ws]) (by decide)
      have h11 := hw_gt 11 (by simp [ws]) (by decide)
      have h12 := hw_gt 12 (by simp [ws]) (by decide)
      have h13 := hw_gt 13 (by simp [ws]) (by decide)
      have h14 := hw_gt 14 (by simp [ws]) (by decide)
      have h15 := hw_gt 15 (by simp [ws]) (by decide)
      simp only [Nat.zero_add] at *
      rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, hw_128]
      simp [zeroState25, ws, UInt64.zero_xor]
    rw [hst]
    rfl
  unfold Model.Merkle.Digest32.hashPair
  rw [hcat, hkec]
  exact (digest32_words_roundtrip (hashPair25 left right)).symm

theorem hashPair25_toSpec (left right : Model.Merkle.Digest32) :
    digest32ToSpec (hashPair25 left right) =
      Spec.Merkle.compress (digest32ToSpec left) (digest32ToSpec right) := by
  rw [hashPair25_eq_hashPair]
  exact Proofs.Merkle.Contracts.hashPair_toSpec left right

private theorem list_drop_eq_tail (ws : Array UInt64) (start : Nat) (hstart : start ≤ ws.size) :
    ws.toList.drop start =
      (List.range (ws.size - start)).map fun j => ws.getD (start + j) 0 := by
  apply List.ext_getElem
  · rw [List.length_drop, List.length_map, List.length_range, Array.length_toList]
  · intro j hj1 hj2
    rw [List.getElem_drop, Array.getElem_toList, List.getElem_map, List.getElem_range]
    have hlt : start + j < ws.size := by
      rw [List.length_drop, Array.length_toList] at hj1
      omega
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]

private theorem wordsBytes_extract_tail (ws : Array UInt64) (start : Nat) (hstart : start ≤ ws.size) :
    (Spec.Keccak.wordsBytes ws).extract (8 * start) (8 * ws.size) =
      Spec.Keccak.wordsBytes
        ((List.range (ws.size - start)).map fun j => ws.getD (start + j) 0).toArray := by
  have hsz : (Spec.Keccak.wordsBytes ws).size = 8 * ws.size := wordsBytes_size ws
  apply ByteArray.ext
  apply Array.toList_inj.mp
  have hemp : ByteArray.empty.data = #[] := rfl
  have hlo : 8 * start ≤ 8 * ws.size := by omega
  have hhi : 8 * ws.size ≤ (Spec.Keccak.wordsBytes ws).size := by omega
  have hextract :
      ((Spec.Keccak.wordsBytes ws).extract (8 * start) (8 * ws.size)).data.toList =
        ((Spec.Keccak.wordsBytes ws).data.toList.drop (8 * start)).take
          (8 * ws.size - 8 * start) := by
    simp only [ByteArray.extract, ByteArray.copySlice, hemp, Array.extract_empty,
      Array.empty_append, Array.append_empty, array_extract_toList, ByteArray.size]
    congr 1
    rw [ByteArray.size] at hsz
    omega
  rw [hextract, wordsBytes_data_toList, words_flatten_drop]
  have hlen_drop : ((ws.toList.drop start).map
      (fun w => (Spec.Keccak.wordBytes w).data.toList)).flatten.length = 8 * (ws.size - start) := by
    rw [words_flatten_length, List.length_drop, Array.length_toList]
  have htake : 8 * ws.size - 8 * start = 8 * (ws.size - start) := by omega
  rw [htake, List.take_of_length_le (by omega), list_drop_eq_tail ws start hstart]
  rw [wordsBytes_data_toList, List.toList_toArray]

private theorem keccak256_words_fold3 (ws : Array UInt64) (hws : ws.size = 64) :
    let b := Spec.Keccak.wordsBytes ws
    keccak256Stream b =
      let s1 := absorb25 zeroState25 b 0
      let s2 := absorb25 s1 b 136
      let s3 := absorb25 s2 b 272
      let tail := b.extract 408 b.size
      Spec.Keccak.wordsBytes #[
        (absorb25Block s3 (Spec.Keccak.finalBlock tail 1)).a00,
        (absorb25Block s3 (Spec.Keccak.finalBlock tail 1)).a01,
        (absorb25Block s3 (Spec.Keccak.finalBlock tail 1)).a02,
        (absorb25Block s3 (Spec.Keccak.finalBlock tail 1)).a03] := by
  intro b
  have hsz : b.size = 512 := by
    rw [show b = Spec.Keccak.wordsBytes ws from rfl, wordsBytes_size, hws]
  have hnfull : b.size / 136 = 3 := by omega
  have hr3 : Array.range 3 = #[0, 1, 2] := rfl
  unfold keccak256Stream
  rw [hnfull]
  dsimp only
  rw [hr3]
  simp only [← Array.foldl_toList, List.foldl_cons, List.foldl_nil]

theorem leafDigest_toSpec (row : Array K) (hrow : row.size ≤ 64) :
    digest32ToSpec (leafDigest row) = Spec.Merkle.hashRow row 64 := by
  let padded := Array.replicate (64 - row.size) (0 : K) ++ row
  have hpad : padded.size = 64 := by
    simp only [padded, Array.size_append, Array.size_replicate]
    omega
  have hwords : Spec.Keccak.wordsBytes padded =
      Spec.Merkle.leafImage row 64 := by
    unfold Spec.Merkle.leafImage padded
    rfl
  have hfold := keccak256_words_fold3 padded hpad
  unfold Spec.Merkle.hashRow Spec.Merkle.hashLeaf
  rw [← hwords, ← Proofs.Layout.keccak256Fast_refines_spec,
    ← Proofs.Layout.keccak256Stream_eq_fast, hfold]
  have h1 : absorb25 zeroState25 (Spec.Keccak.wordsBytes padded) 0 =
      absorbWords17 zeroState25
        (padded.getD 0 0) (padded.getD 1 0) (padded.getD 2 0) (padded.getD 3 0)
        (padded.getD 4 0) (padded.getD 5 0) (padded.getD 6 0) (padded.getD 7 0)
        (padded.getD 8 0) (padded.getD 9 0) (padded.getD 10 0) (padded.getD 11 0)
        (padded.getD 12 0) (padded.getD 13 0) (padded.getD 14 0) (padded.getD 15 0)
        (padded.getD 16 0) :=
    absorb25_wordsBytes zeroState25 padded 0 (by omega)
  have h2 : absorb25 (absorb25 zeroState25 (Spec.Keccak.wordsBytes padded) 0)
        (Spec.Keccak.wordsBytes padded) 136 =
      absorbWords17 (absorb25 zeroState25 (Spec.Keccak.wordsBytes padded) 0)
        (padded.getD 17 0) (padded.getD 18 0) (padded.getD 19 0) (padded.getD 20 0)
        (padded.getD 21 0) (padded.getD 22 0) (padded.getD 23 0) (padded.getD 24 0)
        (padded.getD 25 0) (padded.getD 26 0) (padded.getD 27 0) (padded.getD 28 0)
        (padded.getD 29 0) (padded.getD 30 0) (padded.getD 31 0) (padded.getD 32 0)
        (padded.getD 33 0) :=
    absorb25_wordsBytes _ padded 1 (by omega)
  have h3 : absorb25 (absorb25 (absorb25 zeroState25 (Spec.Keccak.wordsBytes padded) 0)
        (Spec.Keccak.wordsBytes padded) 136) (Spec.Keccak.wordsBytes padded) 272 =
      absorbWords17 (absorb25 (absorb25 zeroState25 (Spec.Keccak.wordsBytes padded) 0)
        (Spec.Keccak.wordsBytes padded) 136)
        (padded.getD 34 0) (padded.getD 35 0) (padded.getD 36 0) (padded.getD 37 0)
        (padded.getD 38 0) (padded.getD 39 0) (padded.getD 40 0) (padded.getD 41 0)
        (padded.getD 42 0) (padded.getD 43 0) (padded.getD 44 0) (padded.getD 45 0)
        (padded.getD 46 0) (padded.getD 47 0) (padded.getD 48 0) (padded.getD 49 0)
        (padded.getD 50 0) :=
    absorb25_wordsBytes _ padded 2 (by omega)
  have htail := wordsBytes_extract_tail padded 51 (by omega)
  have htail_sz : (Spec.Keccak.wordsBytes padded).size = 512 := by
    rw [wordsBytes_size, hpad]
  rw [hpad] at htail
  have hr13 : List.range (64 - 51) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] := by decide
  rw [hr13] at htail
  simp only [List.map_cons, List.map_nil] at htail
  obtain ⟨hw_lt, hw_eq, hw_gt, hw_128⟩ := finalBlock_readWordLE_words
    #[padded.getD 51 0, padded.getD 52 0, padded.getD 53 0, padded.getD 54 0,
      padded.getD 55 0, padded.getD 56 0, padded.getD 57 0, padded.getD 58 0,
      padded.getD 59 0, padded.getD 60 0, padded.getD 61 0, padded.getD 62 0,
      padded.getD 63 0] (by simp)
  let st3 := absorbWords17 (absorbWords17 (absorbWords17 zeroState25
    (padded.getD 0 0) (padded.getD 1 0) (padded.getD 2 0) (padded.getD 3 0)
    (padded.getD 4 0) (padded.getD 5 0) (padded.getD 6 0) (padded.getD 7 0)
    (padded.getD 8 0) (padded.getD 9 0) (padded.getD 10 0) (padded.getD 11 0)
    (padded.getD 12 0) (padded.getD 13 0) (padded.getD 14 0) (padded.getD 15 0)
    (padded.getD 16 0))
    (padded.getD 17 0) (padded.getD 18 0) (padded.getD 19 0) (padded.getD 20 0)
    (padded.getD 21 0) (padded.getD 22 0) (padded.getD 23 0) (padded.getD 24 0)
    (padded.getD 25 0) (padded.getD 26 0) (padded.getD 27 0) (padded.getD 28 0)
    (padded.getD 29 0) (padded.getD 30 0) (padded.getD 31 0) (padded.getD 32 0)
    (padded.getD 33 0))
    (padded.getD 34 0) (padded.getD 35 0) (padded.getD 36 0) (padded.getD 37 0)
    (padded.getD 38 0) (padded.getD 39 0) (padded.getD 40 0) (padded.getD 41 0)
    (padded.getD 42 0) (padded.getD 43 0) (padded.getD 44 0) (padded.getD 45 0)
    (padded.getD 46 0) (padded.getD 47 0) (padded.getD 48 0) (padded.getD 49 0)
    (padded.getD 50 0)
  have hst :
      (let stFinal := absorb25Block st3
        (Spec.Keccak.finalBlock (Spec.Keccak.wordsBytes
          #[padded.getD 51 0, padded.getD 52 0, padded.getD 53 0, padded.getD 54 0,
            padded.getD 55 0, padded.getD 56 0, padded.getD 57 0, padded.getD 58 0,
            padded.getD 59 0, padded.getD 60 0, padded.getD 61 0, padded.getD 62 0,
            padded.getD 63 0]) 1)
       ({ lo0 := stFinal.a00, lo1 := stFinal.a01, hi0 := stFinal.a02, hi1 := stFinal.a03 } :
         Model.Merkle.Digest32)) =
      absorbFinal13 st3
        (padded.getD 51 0) (padded.getD 52 0) (padded.getD 53 0) (padded.getD 54 0)
        (padded.getD 55 0) (padded.getD 56 0) (padded.getD 57 0) (padded.getD 58 0)
        (padded.getD 59 0) (padded.getD 60 0) (padded.getD 61 0) (padded.getD 62 0)
        (padded.getD 63 0) := by
    have hperm :
        absorb25Block st3
          (Spec.Keccak.finalBlock (Spec.Keccak.wordsBytes
            #[padded.getD 51 0, padded.getD 52 0, padded.getD 53 0, padded.getD 54 0,
              padded.getD 55 0, padded.getD 56 0, padded.getD 57 0, padded.getD 58 0,
              padded.getD 59 0, padded.getD 60 0, padded.getD 61 0, padded.getD 62 0,
              padded.getD 63 0]) 1) =
        Model.Keccak.keccakF1600
          { st3 with
            a00 := st3.a00 ^^^ padded.getD 51 0
            a01 := st3.a01 ^^^ padded.getD 52 0
            a02 := st3.a02 ^^^ padded.getD 53 0
            a03 := st3.a03 ^^^ padded.getD 54 0
            a04 := st3.a04 ^^^ padded.getD 55 0
            a05 := st3.a05 ^^^ padded.getD 56 0
            a06 := st3.a06 ^^^ padded.getD 57 0
            a07 := st3.a07 ^^^ padded.getD 58 0
            a08 := st3.a08 ^^^ padded.getD 59 0
            a09 := st3.a09 ^^^ padded.getD 60 0
            a10 := st3.a10 ^^^ padded.getD 61 0
            a11 := st3.a11 ^^^ padded.getD 62 0
            a12 := st3.a12 ^^^ padded.getD 63 0
            a13 := st3.a13 ^^^ 1
            a16 := st3.a16 ^^^ 0x8000000000000000 } := by
      unfold absorb25Block absorb25
      apply congrArg Model.Keccak.keccakF1600
      have hw0 := hw_lt 0 (by simp)
      have hw1 := hw_lt 1 (by simp)
      have hw2 := hw_lt 2 (by simp)
      have hw3 := hw_lt 3 (by simp)
      have hw4 := hw_lt 4 (by simp)
      have hw5 := hw_lt 5 (by simp)
      have hw6 := hw_lt 6 (by simp)
      have hw7 := hw_lt 7 (by simp)
      have hw8 := hw_lt 8 (by simp)
      have hw9 := hw_lt 9 (by simp)
      have hw10 := hw_lt 10 (by simp)
      have hw11 := hw_lt 11 (by simp)
      have hw12 := hw_lt 12 (by simp)
      have hw13 : readWordLE (Spec.Keccak.finalBlock (Spec.Keccak.wordsBytes
          #[padded.getD 51 0, padded.getD 52 0, padded.getD 53 0, padded.getD 54 0,
            padded.getD 55 0, padded.getD 56 0, padded.getD 57 0, padded.getD 58 0,
            padded.getD 59 0, padded.getD 60 0, padded.getD 61 0, padded.getD 62 0,
            padded.getD 63 0]) 1) 104 = 1 := by
        simpa using hw_eq
      have hw14 := hw_gt 14 (by simp) (by decide)
      have hw15 := hw_gt 15 (by simp) (by decide)
      simp only [Nat.mul_zero, Nat.add_zero] at hw0
      rw [hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9, hw10, hw11, hw12,
        hw13, hw14, hw15, hw_128]
      simp [UInt64.xor_zero]
    dsimp only
    rw [hperm]
    rfl
  dsimp only
  rw [htail_sz, h3, h2, h1]
  have htail' : (Spec.Keccak.wordsBytes padded).extract 408 512 =
      Spec.Keccak.wordsBytes
        #[padded.getD 51 0, padded.getD 52 0, padded.getD 53 0, padded.getD 54 0,
          padded.getD 55 0, padded.getD 56 0, padded.getD 57 0, padded.getD 58 0,
          padded.getD 59 0, padded.getD 60 0, padded.getD 61 0, padded.getD 62 0,
          padded.getD 63 0] := htail
  rw [htail']
  let stFinal := absorb25Block st3 (Spec.Keccak.finalBlock (Spec.Keccak.wordsBytes
    #[padded.getD 51 0, padded.getD 52 0, padded.getD 53 0, padded.getD 54 0,
      padded.getD 55 0, padded.getD 56 0, padded.getD 57 0, padded.getD 58 0,
      padded.getD 59 0, padded.getD 60 0, padded.getD 61 0, padded.getD 62 0,
      padded.getD 63 0]) 1)
  have hleaf : leafDigest row =
      { lo0 := stFinal.a00, lo1 := stFinal.a01, hi0 := stFinal.a02, hi1 := stFinal.a03 } := by
    unfold leafDigest Spec.Pcs.Commit.leafWords
    exact hst.symm
  rw [hleaf]
  rfl

@[simp] theorem subtreeRoot_zero (leafAt : Nat → Model.Merkle.Digest32) (base : Nat) :
    subtreeRoot leafAt 0 base = leafAt base := rfl

@[simp] theorem subtreeRoot_succ (leafAt : Nat → Model.Merkle.Digest32) (k base : Nat) :
    subtreeRoot leafAt (k + 1) base =
      hashPair25 (subtreeRoot leafAt k base) (subtreeRoot leafAt k (base + (1 <<< k))) := rfl

theorem subtreeRoot_shift (leafAt : Nat → Model.Merkle.Digest32) (k off base : Nat) :
    subtreeRoot leafAt k (off + base) =
      subtreeRoot (fun i => leafAt (off + i)) k base := by
  induction k generalizing off base with
  | zero => rfl
  | succ k ih =>
    simp only [subtreeRoot_succ, Nat.shiftLeft_eq]
    rw [ih off base]
    rw [show off + base + 1 * 2 ^ k = off + (base + 2 ^ k) by omega]
    rw [ih off (base + 2 ^ k)]
    congr 2
    omega

theorem subtreeRoot_add (leafAt : Nat → Model.Merkle.Digest32) (a b base : Nat) :
    subtreeRoot leafAt (a + b) base =
      subtreeRoot (fun i => subtreeRoot leafAt a (base + i * (1 <<< a))) b 0 := by
  induction b generalizing base with
  | zero =>
    simp [subtreeRoot_zero, Nat.mul_zero, Nat.add_zero]
  | succ b ih =>
    simp only [Nat.add_succ, subtreeRoot_succ, Nat.shiftLeft_eq]
    change hashPair25 (subtreeRoot leafAt (a + b) base)
        (subtreeRoot leafAt (a + b) (base + 1 * 2 ^ (a + b))) =
      hashPair25 (subtreeRoot (fun i => subtreeRoot leafAt a (base + i * (1 * 2 ^ a))) b 0)
        (subtreeRoot (fun i => subtreeRoot leafAt a (base + i * (1 * 2 ^ a))) b (0 + 1 * 2 ^ b))
    rw [ih base]
    rw [show base + 1 * 2 ^ (a + b) = base + 2 ^ (a + b) by omega]
    rw [ih (base + 2 ^ (a + b))]
    congr 1
    simp only [Nat.shiftLeft_eq]
    simp only [Nat.one_mul, Nat.zero_add]
    have hshift :
        subtreeRoot (fun i => subtreeRoot leafAt a (base + i * 2 ^ a)) b (2 ^ b) =
          subtreeRoot (fun i => subtreeRoot leafAt a (base + (2 ^ b + i) * 2 ^ a)) b 0 := by
      have hs := subtreeRoot_shift (fun i => subtreeRoot leafAt a (base + i * 2 ^ a)) b (2 ^ b) 0
      simpa only [Nat.add_zero] using hs
    rw [hshift]
    congr 1
    funext i
    simp only [Nat.shiftLeft_eq, Nat.one_mul]
    congr 1
    have hpow : 2 ^ b * 2 ^ a = 2 ^ (a + b) := by
      rw [Nat.pow_add, Nat.mul_comm]
    have hdist : (2 ^ b + i) * 2 ^ a = 2 ^ b * 2 ^ a + i * 2 ^ a := Nat.add_mul (2 ^ b) i (2 ^ a)
    omega

theorem array_getElem_range (n i : Nat) (h : i < (Array.range n).size) :
    (Array.range n)[i] = i := by
  rw [← Array.getElem_toList]
  simp only [array_range_toList, List.getElem_range', Nat.zero_add, Nat.one_mul]

theorem array_getElem?_range (n i : Nat) :
    (Array.range n)[i]? = if i < n then some i else none := by
  if hi : i < n then
    have hsz : i < (Array.range n).size := by
      rw [← Array.length_toList, array_range_toList, List.length_range']
      exact hi
    rw [Array.getElem?_eq_getElem hsz, array_getElem_range n i hsz]
    simp only [hi, ↓reduceIte]
  else
    have hge : (Array.range n).size ≤ i := by
      rw [← Array.length_toList, array_range_toList, List.length_range']
      exact Nat.le_of_not_lt hi
    rw [Array.getElem?_eq_none hge]
    simp only [hi, ↓reduceIte]

theorem subtreeRoot_level (leaves : Array Model.Merkle.Digest32)
    (depth : Nat) (hsize : leaves.size = 2 ^ depth)
    (k : Nat) (hk : k ≤ depth) (idx : Nat) (hidx : idx < 2 ^ (depth - k)) :
    digest32ToSpec (subtreeRoot (fun i => leaves.getD i default) k (idx * (1 <<< k))) =
      (Spec.Merkle.levels leaves.size (leaves.map digest32ToSpec))[k]![idx]! := by
  let specLeaves := leaves.map digest32ToSpec
  have hspec : specLeaves.size = leaves.size := by simp [specLeaves]
  have hlog : depth ≤ specLeaves.size := by
    rw [hspec, hsize]
    exact Nat.le_of_lt Nat.lt_two_pow_self
  have hshape := Proofs.Merkle.Contracts.levels_power_shape depth specLeaves.size
    specLeaves hlog (by rw [hspec, hsize])
  change digest32ToSpec (subtreeRoot (fun i => leaves.getD i default) k (idx * (1 <<< k))) =
    (Spec.Merkle.levels leaves.size specLeaves)[k]![idx]!
  rw [← hspec]
  induction k generalizing idx with
  | zero =>
    simp only [subtreeRoot_zero, Nat.mul_one, Nat.shiftLeft_zero]
    have hfirst : (Spec.Merkle.levels specLeaves.size specLeaves)[0]! = specLeaves := by
      cases specLeaves.size <;>
        simp only [Spec.Merkle.levels_zero, Spec.Merkle.levels_succ] <;>
        (try split) <;>
        simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_append]
    rw [hfirst]
    have hlt : idx < leaves.size := by
      rw [hsize]
      simpa using hidx
    simp [specLeaves, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hlt]
  | succ k ih =>
    have hstep := Proofs.Merkle.Contracts.levels_parent_equations depth specLeaves.size
      specLeaves hlog (by rw [hspec, hsize]) k (by omega)
    rw [hstep]
    have hsub : depth - k = (depth - (k + 1)) + 1 := by omega
    have hpow2 : 2 ^ (depth - k) = 2 * 2 ^ (depth - (k + 1)) := by
      rw [hsub, Nat.pow_succ]
      omega
    let cur := (Spec.Merkle.levels specLeaves.size specLeaves)[k]!
    have hwidth : cur.size = 2 ^ (depth - k) := hshape.2 k (by omega)
    have hlt_parent : idx < cur.size / 2 := by
      rw [hwidth, hpow2]
      omega
    have hlt2 : 2 * idx < cur.size := by
      rw [hwidth, hpow2]
      omega
    have hlt21 : 2 * idx + 1 < cur.size := by
      rw [hwidth, hpow2]
      omega
    change digest32ToSpec (subtreeRoot (fun i => leaves.getD i default) (k + 1) (idx * (1 <<< (k + 1)))) =
      (Spec.Merkle.parentLevel cur)[idx]!
    simp only [subtreeRoot_succ, Spec.Merkle.parentLevel]
    rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_map,
      array_getElem?_range]
    simp only [hlt_parent, ↓reduceIte, ↓reduceDIte, Option.map_some, Option.getD_some]
    rw [hashPair25_toSpec]
    have hleft := ih (by omega) (2 * idx) (by
      rw [hpow2]
      omega)
    have hright := ih (by omega) (2 * idx + 1) (by
      rw [hpow2]
      omega)
    simp only [Nat.shiftLeft_eq] at hleft hright ⊢
    simp only [Nat.one_mul] at hleft hright ⊢
    have hl : 2 * idx * 2 ^ k = idx * 2 ^ (k + 1) := by
      calc 2 * idx * 2 ^ k
        _ = idx * 2 * 2 ^ k := by rw [Nat.mul_comm 2 idx]
        _ = idx * (2 * 2 ^ k) := by rw [Nat.mul_assoc]
        _ = idx * (2 ^ k * 2) := by rw [Nat.mul_comm 2 (2 ^ k)]
        _ = idx * 2 ^ (k + 1) := by rw [← Nat.pow_succ]
    have hr : (2 * idx + 1) * 2 ^ k = idx * 2 ^ (k + 1) + 2 ^ k := by
      rw [Nat.add_mul, Nat.one_mul, hl]
    rw [hl] at hleft
    rw [hr] at hright
    rw [hleft, hright]

theorem subtreeRoot_eq_treeRoot (leaves : Array Model.Merkle.Digest32)
    (depth : Nat) (hsize : leaves.size = 2 ^ depth) :
    (subtreeRoot (fun i => leaves.getD i default) depth 0).toBytes =
      Spec.Merkle.digestBytes (Spec.Merkle.treeRoot
        (Spec.Merkle.build (leaves.map digest32ToSpec))) := by
  have htop := subtreeRoot_level leaves depth hsize depth (Nat.le_refl _) 0 (by simp)
  rw [Nat.zero_mul] at htop
  rw [← digest32ToSpec_bytes, htop]
  have hspec : (leaves.map digest32ToSpec).size = leaves.size := by simp
  have hlog : depth ≤ (leaves.map digest32ToSpec).size := by
    rw [hspec, hsize]
    exact Nat.le_of_lt Nat.lt_two_pow_self
  have hheight := (Proofs.Merkle.Contracts.levels_power_shape depth
    (leaves.map digest32ToSpec).size (leaves.map digest32ToSpec) hlog (by rw [hspec, hsize])).1
  unfold Spec.Merkle.treeRoot Array.back! Spec.Merkle.build
  rw [hheight, hspec]
  rfl

section Vec8Leaf

open Model.Pcs.Ntt (Vec8)

private theorem absorbWords17_zeros (s : Model.Keccak.State25) :
    absorbWords17 s 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = Model.Keccak.keccakF1600 s := by
  unfold absorbWords17
  apply congrArg Model.Keccak.keccakF1600
  simp [UInt64.xor_zero]

private theorem zps1_eq :
    absorbWords17 zeroState25 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = zeroPrefixState 1 :=
  absorbWords17_zeros zeroState25

private theorem zps2_eq :
    absorbWords17 (zeroPrefixState 1) 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = zeroPrefixState 2 :=
  absorbWords17_zeros (zeroPrefixState 1)

private theorem zps3_eq :
    absorbWords17 (zeroPrefixState 2) 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 = zeroPrefixState 3 :=
  absorbWords17_zeros (zeroPrefixState 2)

private def leafDigestFromFn (w : Nat → K) : Model.Merkle.Digest32 :=
  let s1 := absorbWords17 zeroState25
    (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7)
    (w 8) (w 9) (w 10) (w 11) (w 12) (w 13) (w 14) (w 15) (w 16)
  let s2 := absorbWords17 s1
    (w 17) (w 18) (w 19) (w 20) (w 21) (w 22) (w 23) (w 24)
    (w 25) (w 26) (w 27) (w 28) (w 29) (w 30) (w 31) (w 32) (w 33)
  let s3 := absorbWords17 s2
    (w 34) (w 35) (w 36) (w 37) (w 38) (w 39) (w 40) (w 41)
    (w 42) (w 43) (w 44) (w 45) (w 46) (w 47) (w 48) (w 49) (w 50)
  absorbFinal13 s3
    (w 51) (w 52) (w 53) (w 54) (w 55) (w 56) (w 57)
    (w 58) (w 59) (w 60) (w 61) (w 62) (w 63)

private def leafDigestVecs (v0 v1 v2 v3 v4 v5 v6 v7 : Vec8) : Model.Merkle.Digest32 :=
  let s1 := absorbWords17 zeroState25
    v0.w0 v0.w1 v0.w2 v0.w3 v0.w4 v0.w5 v0.w6 v0.w7
    v1.w0 v1.w1 v1.w2 v1.w3 v1.w4 v1.w5 v1.w6 v1.w7 v2.w0
  let s2 := absorbWords17 s1
    v2.w1 v2.w2 v2.w3 v2.w4 v2.w5 v2.w6 v2.w7
    v3.w0 v3.w1 v3.w2 v3.w3 v3.w4 v3.w5 v3.w6 v3.w7
    v4.w0 v4.w1
  let s3 := absorbWords17 s2
    v4.w2 v4.w3 v4.w4 v4.w5 v4.w6 v4.w7
    v5.w0 v5.w1 v5.w2 v5.w3 v5.w4 v5.w5 v5.w6 v5.w7
    v6.w0 v6.w1 v6.w2
  absorbFinal13 s3
    v6.w3 v6.w4 v6.w5 v6.w6 v6.w7
    v7.w0 v7.w1 v7.w2 v7.w3 v7.w4 v7.w5 v7.w6 v7.w7

private def vecAt8 (v0 v1 v2 v3 v4 v5 v6 v7 : Vec8) : Nat → Vec8
  | 0 => v0
  | 1 => v1
  | 2 => v2
  | 3 => v3
  | 4 => v4
  | 5 => v5
  | 6 => v6
  | 7 => v7
  | _ => default

private theorem vec8_default_lane (j : Nat) : (default : Vec8).lane j = 0 := by
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rfl
  | _ + 8 => rfl

private theorem padded_getD_eq (rowK : Array K) (pad idx : Nat) :
    (Array.replicate pad (0 : K) ++ rowK).getD idx 0 =
      if idx < pad then 0 else rowK.getD (idx - pad) 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_append, Array.getElem?_replicate,
    Array.size_replicate]
  split
  · rfl
  · rfl

private theorem leafDigestVecs_eq_fromFn (v0 v1 v2 v3 v4 v5 v6 v7 : Vec8) :
    leafDigestVecs v0 v1 v2 v3 v4 v5 v6 v7 =
      leafDigestFromFn (fun idx =>
        if idx < 64 then (vecAt8 v0 v1 v2 v3 v4 v5 v6 v7 (idx / 8)).lane (idx % 8) else 0) :=
  rfl

private theorem leafDigest_eq_fromFn (rowK : Array K) :
    leafDigest rowK =
      leafDigestFromFn (fun idx =>
        if idx < 64 then
          (Array.replicate (Spec.Pcs.Commit.leafWords - rowK.size) (0 : K) ++ rowK).getD idx 0
        else 0) :=
  rfl

private def paddedVecs (buf : Array Vec8) (nVecs row : Nat) :
    Vec8 × Vec8 × Vec8 × Vec8 × Vec8 × Vec8 × Vec8 × Vec8 :=
  let z : Vec8 := default
  let base := row * nVecs
  match nVecs with
  | 0 => (z, z, z, z, z, z, z, z)
  | 1 => (z, z, z, z, z, z, z, buf.getD base z)
  | 2 => (z, z, z, z, z, z, buf.getD base z, buf.getD (base + 1) z)
  | 3 => (z, z, z, z, z, buf.getD base z, buf.getD (base + 1) z, buf.getD (base + 2) z)
  | 4 =>
    (z, z, z, z, buf.getD base z, buf.getD (base + 1) z,
      buf.getD (base + 2) z, buf.getD (base + 3) z)
  | 5 =>
    (z, z, z, buf.getD base z, buf.getD (base + 1) z, buf.getD (base + 2) z,
      buf.getD (base + 3) z, buf.getD (base + 4) z)
  | 6 =>
    (z, z, buf.getD base z, buf.getD (base + 1) z, buf.getD (base + 2) z,
      buf.getD (base + 3) z, buf.getD (base + 4) z, buf.getD (base + 5) z)
  | 7 =>
    (z, buf.getD base z, buf.getD (base + 1) z, buf.getD (base + 2) z,
      buf.getD (base + 3) z, buf.getD (base + 4) z,
      buf.getD (base + 5) z, buf.getD (base + 6) z)
  | _ =>
    (buf.getD base z, buf.getD (base + 1) z, buf.getD (base + 2) z,
      buf.getD (base + 3) z, buf.getD (base + 4) z, buf.getD (base + 5) z,
      buf.getD (base + 6) z, buf.getD (base + 7) z)

private theorem hashLeafVec8From_eq_padded (buf : Array Vec8) (nVecs row : Nat) :
    hashLeafVec8From (zeroPrefixState 1) (zeroPrefixState 2) (zeroPrefixState 3)
      buf nVecs row =
      leafDigestVecs (paddedVecs buf nVecs row).1 (paddedVecs buf nVecs row).2.1
        (paddedVecs buf nVecs row).2.2.1 (paddedVecs buf nVecs row).2.2.2.1
        (paddedVecs buf nVecs row).2.2.2.2.1 (paddedVecs buf nVecs row).2.2.2.2.2.1
        (paddedVecs buf nVecs row).2.2.2.2.2.2.1 (paddedVecs buf nVecs row).2.2.2.2.2.2.2 := by
  have hw0 : (default : Vec8).w0 = 0 := rfl
  have hw1 : (default : Vec8).w1 = 0 := rfl
  have hw2 : (default : Vec8).w2 = 0 := rfl
  have hw3 : (default : Vec8).w3 = 0 := rfl
  have hw4 : (default : Vec8).w4 = 0 := rfl
  have hw5 : (default : Vec8).w5 = 0 := rfl
  have hw6 : (default : Vec8).w6 = 0 := rfl
  have hw7 : (default : Vec8).w7 = 0 := rfl
  match nVecs with
  | 0 =>
    dsimp only [hashLeafVec8From, paddedVecs, leafDigestVecs]
    simp only [if_pos (by decide : 0 ≤ 5), if_pos (by decide : 0 ≤ 3),
      if_pos (by decide : 0 ≤ 1), hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7,
      zps1_eq, zps2_eq, zps3_eq]
  | 1 =>
    dsimp only [hashLeafVec8From, paddedVecs, leafDigestVecs]
    simp only [if_pos (by decide : 1 ≤ 5), if_pos (by decide : 1 ≤ 3),
      if_pos (by decide : 1 ≤ 1), hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7,
      zps1_eq, zps2_eq, zps3_eq]
  | 2 =>
    dsimp only [hashLeafVec8From, paddedVecs, leafDigestVecs]
    simp only [if_pos (by decide : 2 ≤ 5), if_pos (by decide : 2 ≤ 3),
      if_neg (by decide : ¬ 2 ≤ 1), hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7,
      zps1_eq, zps2_eq]
  | 3 =>
    dsimp only [hashLeafVec8From, paddedVecs, leafDigestVecs]
    simp only [if_pos (by decide : 3 ≤ 5), if_pos (by decide : 3 ≤ 3),
      if_neg (by decide : ¬ 3 ≤ 1), hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7,
      zps1_eq, zps2_eq]
  | 4 =>
    dsimp only [hashLeafVec8From, paddedVecs, leafDigestVecs]
    simp only [if_pos (by decide : 4 ≤ 5), if_neg (by decide : ¬ 4 ≤ 3),
      if_neg (by decide : ¬ 4 ≤ 1), hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7,
      zps1_eq]
  | 5 =>
    dsimp only [hashLeafVec8From, paddedVecs, leafDigestVecs]
    simp only [if_pos (by decide : 5 ≤ 5), if_neg (by decide : ¬ 5 ≤ 3),
      if_neg (by decide : ¬ 5 ≤ 1), hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7,
      zps1_eq]
  | 6 =>
    dsimp only [hashLeafVec8From, paddedVecs, leafDigestVecs]
    simp only [if_neg (by decide : ¬ 6 ≤ 5), if_neg (by decide : ¬ 6 ≤ 3),
      if_neg (by decide : ¬ 6 ≤ 1)]
  | 7 =>
    dsimp only [hashLeafVec8From, paddedVecs, leafDigestVecs]
    simp only [if_neg (by decide : ¬ 7 ≤ 5), if_neg (by decide : ¬ 7 ≤ 3),
      if_neg (by decide : ¬ 7 ≤ 1)]
  | n + 8 =>
    dsimp only [hashLeafVec8From, paddedVecs, leafDigestVecs]
    simp only [if_neg (by omega : ¬ n + 8 ≤ 5), if_neg (by omega : ¬ n + 8 ≤ 3),
      if_neg (by omega : ¬ n + 8 ≤ 1)]

private theorem paddedVecAt_eq (buf : Array Vec8) (nVecs row q : Nat)
    (hlo : 1 ≤ nVecs) (hhi : nVecs ≤ 8) (hq : q < 8) :
    vecAt8 (paddedVecs buf nVecs row).1 (paddedVecs buf nVecs row).2.1
      (paddedVecs buf nVecs row).2.2.1 (paddedVecs buf nVecs row).2.2.2.1
      (paddedVecs buf nVecs row).2.2.2.2.1 (paddedVecs buf nVecs row).2.2.2.2.2.1
      (paddedVecs buf nVecs row).2.2.2.2.2.2.1 (paddedVecs buf nVecs row).2.2.2.2.2.2.2 q =
      if q < 8 - nVecs then default else buf.getD (row * nVecs + (q - (8 - nVecs))) default := by
  rcases (by omega :
      nVecs = 1 ∨ nVecs = 2 ∨ nVecs = 3 ∨ nVecs = 4 ∨
      nVecs = 5 ∨ nVecs = 6 ∨ nVecs = 7 ∨ nVecs = 8) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases (by omega :
        q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [paddedVecs, vecAt8]

private theorem paddedWord_eq (buf : Array Vec8) (rowK : Array K) (nVecs row idx : Nat)
    (hlo : 1 ≤ nVecs) (hhi : nVecs ≤ 8) (hsz : rowK.size = 8 * nVecs) (hlt : idx < 64)
    (hbuf : ∀ v < nVecs, ∀ j < 8,
      (buf.getD (row * nVecs + v) default).lane j = rowK.getD (8 * v + j) 0) :
    (vecAt8 (paddedVecs buf nVecs row).1 (paddedVecs buf nVecs row).2.1
      (paddedVecs buf nVecs row).2.2.1 (paddedVecs buf nVecs row).2.2.2.1
      (paddedVecs buf nVecs row).2.2.2.2.1 (paddedVecs buf nVecs row).2.2.2.2.2.1
      (paddedVecs buf nVecs row).2.2.2.2.2.2.1 (paddedVecs buf nVecs row).2.2.2.2.2.2.2
      (idx / 8)).lane (idx % 8) =
      (Array.replicate (64 - rowK.size) (0 : K) ++ rowK).getD idx 0 := by
  have hq : idx / 8 < 8 := by omega
  have hj : idx % 8 < 8 := by omega
  have hpad : 64 - rowK.size = 64 - 8 * nVecs := by
    rw [hsz]
  rw [paddedVecAt_eq buf nVecs row (idx / 8) hlo hhi hq, hpad, padded_getD_eq]
  split
  · rename_i hqpad
    rw [vec8_default_lane, if_pos (by omega)]
  · rename_i hqpad
    rw [if_neg (by omega)]
    have hidx : idx - (64 - 8 * nVecs) = 8 * (idx / 8 - (8 - nVecs)) + idx % 8 := by omega
    rw [hidx]
    exact hbuf (idx / 8 - (8 - nVecs)) (by omega) (idx % 8) hj

theorem hashLeafVec8From_eq_leafDigest (buf : Array Vec8) (rowK : Array K) (nVecs row : Nat)
    (hlo : 1 ≤ nVecs) (hhi : nVecs ≤ 8) (hsz : rowK.size = 8 * nVecs)
    (hbuf : ∀ v < nVecs, ∀ j < 8,
      (buf.getD (row * nVecs + v) default).lane j = rowK.getD (8 * v + j) 0) :
    hashLeafVec8From (zeroPrefixState 1) (zeroPrefixState 2) (zeroPrefixState 3)
      buf nVecs row = leafDigest rowK := by
  rw [hashLeafVec8From_eq_padded, leafDigestVecs_eq_fromFn, leafDigest_eq_fromFn]
  have hwords : Spec.Pcs.Commit.leafWords = 64 := rfl
  rw [hwords]
  congr 1
  funext idx
  split
  · rename_i hlt
    exact paddedWord_eq buf rowK nVecs row idx hlo hhi hsz hlt hbuf
  · rfl

@[simp] theorem subtreeRootBuf_zero (st1 st2 st3 : Model.Keccak.State25)
    (buf : Array Vec8) (nVecs base : Nat) :
    subtreeRootBuf st1 st2 st3 buf nVecs 0 base =
      hashLeafVec8From st1 st2 st3 buf nVecs base := rfl

@[simp] theorem subtreeRootBuf_succ (st1 st2 st3 : Model.Keccak.State25)
    (buf : Array Vec8) (nVecs k base : Nat) :
    subtreeRootBuf st1 st2 st3 buf nVecs (k + 1) base =
      hashPair25 (subtreeRootBuf st1 st2 st3 buf nVecs k base)
        (subtreeRootBuf st1 st2 st3 buf nVecs k (base + (1 <<< k))) := rfl

theorem subtreeRootBuf_eq_subtreeRoot (st1 st2 st3 : Model.Keccak.State25)
    (buf : Array Vec8) (nVecs : Nat) (leafAt : Nat → Model.Merkle.Digest32)
    (k base : Nat)
    (hleaf : ∀ i < 2 ^ k, hashLeafVec8From st1 st2 st3 buf nVecs (base + i) = leafAt (base + i)) :
    subtreeRootBuf st1 st2 st3 buf nVecs k base = subtreeRoot leafAt k base := by
  induction k generalizing base with
  | zero =>
    simpa [subtreeRootBuf_zero, subtreeRoot_zero] using hleaf 0 (by decide)
  | succ k ih =>
    simp only [subtreeRootBuf_succ, subtreeRoot_succ, Nat.shiftLeft_eq, Nat.one_mul]
    have hl := ih base (fun i hi => hleaf i (by omega))
    have hr := ih (base + 2 ^ k) (fun i hi => by
      have heq : base + 2 ^ k + i = base + (2 ^ k + i) := by omega
      rw [heq]
      exact hleaf (2 ^ k + i) (by omega))
    rw [hl, hr]

end Vec8Leaf

end LeanVmXmss.Proofs.Pcs

