import Model.Pcs.Commit
import Proofs.Pcs.CommitMerkle
import Proofs.Pcs.Refinement
import Proofs.Field.Squares

namespace LeanVmXmss.Proofs.Pcs

set_option maxHeartbeats 0

open Spec.Field (K)
open Model.Pcs.Ntt (Vec8)
open Model.Pcs.Commit (subtreeRoot)
open Proofs.Merkle.Contracts (digest32ToSpec)

theorem log2_pow (n : Nat) : Nat.log2 (2 ^ n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hgt : 2 ^ (n + 1) ≥ 2 := by
      rw [Nat.pow_succ]
      have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
      omega
    rw [Nat.log2_def, if_pos hgt]
    have hdiv : 2 ^ (n + 1) / 2 = 2 ^ n := by
      rw [Nat.pow_succ]
      omega
    rw [hdiv, ih]

theorem rowWords_of_lanes (lanes : Nat) (hlo : 1 ≤ lanes) (hhi : lanes ≤ 64) :
    Spec.Pcs.Commit.rowWords lanes = (lanes + 7) / 8 * 8 := by
  unfold Spec.Pcs.Commit.rowWords Spec.Pcs.Commit.leafWords
  have hle : (lanes + 7) / 8 * 8 ≤ 64 := by omega
  simp [Nat.min_eq_right hle]

theorem rowWords_mul8 (lanes : Nat) (hlo : 1 ≤ lanes) (hhi : lanes ≤ 64) :
    Spec.Pcs.Commit.rowWords lanes = 8 * (Spec.Pcs.Commit.rowWords lanes / 8) := by
  rw [rowWords_of_lanes lanes hlo hhi]
  omega

theorem nVecs_bounds (lanes : Nat) (hlo : 1 ≤ lanes) (hhi : lanes ≤ 64) :
    1 ≤ Spec.Pcs.Commit.rowWords lanes / 8 ∧ Spec.Pcs.Commit.rowWords lanes / 8 ≤ 8 := by
  rw [rowWords_of_lanes lanes hlo hhi]
  constructor <;> omega

private theorem setIf_getD_same {α : Type} (a : Array α) (i : Nat) (v d : α) (hi : i < a.size) :
    (a.setIfInBounds i v).getD i d = v := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, hi]

private theorem setIf_getD_other {α : Type} (a : Array α) (i j : Nat) (v d : α) (hne : i ≠ j) :
    (a.setIfInBounds i v).getD j d = a.getD j d := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, hne]

private theorem setIf_size {α : Type} (a : Array α) (i : Nat) (v : α) :
    (a.setIfInBounds i v).size = a.size := by
  simp [Array.size_setIfInBounds]

private theorem foldl_range'_size {α : Type} (s n : Nat) (a : Array α)
    (f : Array α → Nat → Array α) (hf : ∀ acc x, (f acc x).size = acc.size) :
    ((List.range' s n).foldl f a).size = a.size := by
  induction n generalizing s a with
  | zero => rfl
  | succ n ih =>
    rw [List.range'_succ, List.foldl_cons, ih, hf]

private theorem foldl_range'_miss {α : Type} (s n : Nat) (a : Array α) (d : α) (j : Nat)
    (f : Array α → Nat → Array α)
    (hmiss : ∀ acc k, s ≤ k → k < s + n → (f acc k).getD j d = acc.getD j d) :
    ((List.range' s n).foldl f a).getD j d = a.getD j d := by
  induction n generalizing s a with
  | zero => rfl
  | succ n ih =>
    rw [List.range'_succ, List.foldl_cons]
    rw [ih (s + 1) (f a s) (fun acc k h1 h2 => hmiss acc k (by omega) (by omega))]
    exact hmiss a s (Nat.le_refl _) (by omega)

private theorem foldl_range'_hit {α : Type} (s n : Nat) (a : Array α) (d : α) (j k0 : Nat)
    (hk0_lo : s ≤ k0) (hk0_hi : k0 < s + n)
    (f : Array α → Nat → Array α)
    (hmiss : ∀ acc k, s ≤ k → k < s + n → k ≠ k0 → (f acc k).getD j d = acc.getD j d) :
    ((List.range' s n).foldl f a).getD j d =
      (f ((List.range' s (k0 - s)).foldl f a) k0).getD j d := by
  induction n generalizing s a with
  | zero =>
    rw [Nat.add_zero] at hk0_hi
    exact absurd (Nat.lt_of_le_of_lt hk0_lo hk0_hi) (Nat.lt_irrefl _)
  | succ n ih =>
    rw [List.range'_succ, List.foldl_cons]
    if heq : k0 = s then
      subst heq
      rw [Nat.sub_self]
      dsimp only [List.range', List.foldl]
      refine foldl_range'_miss (k0 + 1) n (f a k0) d j f (fun acc k h1 h2 => ?_)
      have hlo : k0 ≤ k := Nat.le_of_succ_le h1
      have hhi : k < k0 + (n + 1) := by
        rw [Nat.add_right_comm k0 1 n] at h2
        exact h2
      exact hmiss acc k hlo hhi (Nat.ne_of_gt h1)
    else
      have hgt : s + 1 ≤ k0 := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hk0_lo (Ne.symm heq))
      have hsub : k0 - s = (k0 - (s + 1)) + 1 := by
        rw [← Nat.sub_add_comm hgt, Nat.add_sub_add_right]
      have hhi' : k0 < (s + 1) + n := by
        rw [Nat.add_right_comm s 1 n]
        exact hk0_hi
      rw [hsub, List.range'_succ, List.foldl_cons]
      refine ih (s + 1) (f a s) hgt hhi' (fun acc k h1 h2 hne => ?_)
      have hhi2 : k < s + (n + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 n] at h2
        exact h2
      exact hmiss acc k (Nat.le_of_succ_le h1) hhi2 hne

theorem transpose_size (message : Array K) (lanes width logRows : Nat) :
    (Spec.Pcs.Commit.transpose message lanes width logRows).size =
      width * (1 <<< logRows) := by
  unfold Spec.Pcs.Commit.transpose
  rw [← Array.foldl_toList, array_range_toList, foldl_range'_size]
  · simp
  · intro acc _
    rw [← Array.foldl_toList, array_range_toList]
    exact foldl_range'_size 0 _ acc _ (fun b _ => setIf_size _ _ _)

theorem transpose_getD (message : Array K) (lanes width logRows rowIndex col : Nat)
    (hlanes : lanes ≤ width) (hrow : rowIndex < 1 <<< logRows) (hcol : col < width) :
    (Spec.Pcs.Commit.transpose message lanes width logRows).getD
        (rowIndex * width + col) 0 =
      if col + lanes ≥ width then
        message.getD ((width - 1 - col) * (1 <<< logRows) + rowIndex) 0
      else 0 := by
  let rows := 1 <<< logRows
  let stepRow (lane : Nat) (out : Array K) (r : Nat) : Array K :=
    out.setIfInBounds (r * width + (width - 1 - lane))
      (message.getD (lane * rows + r) 0)
  let stepLane (out : Array K) (lane : Nat) : Array K :=
    (List.range' 0 rows).foldl (stepRow lane) out
  have hstepLane_sz (acc : Array K) (lane : Nat) : (stepLane acc lane).size = acc.size :=
    foldl_range'_size 0 rows acc (stepRow lane) (fun b _ => setIf_size _ _ _)
  have hstepLane_miss (acc : Array K) (lane : Nat) (hlane : lane < lanes)
      (hdest : width - 1 - lane ≠ col) :
      (stepLane acc lane).getD (rowIndex * width + col) 0 =
        acc.getD (rowIndex * width + col) 0 := by
    refine foldl_range'_miss 0 rows acc 0 (rowIndex * width + col) (stepRow lane) ?_
    intro b r _ _
    apply setIf_getD_other
    intro heq
    have hd_lt : width - 1 - lane < width := by omega
    have hrem : (r * width + (width - 1 - lane)) % width = (rowIndex * width + col) % width :=
      congrArg (· % width) heq
    have h1 : (r * width + (width - 1 - lane)) % width = width - 1 - lane := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hd_lt]
    have h2 : (rowIndex * width + col) % width = col := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hcol]
    omega
  change ((Array.range lanes).foldl
      (fun out lane => (Array.range rows).foldl (stepRow lane) out)
      (Array.replicate (width * rows) 0)).getD (rowIndex * width + col) 0 = _
  have hconv : (Array.range lanes).foldl
      (fun out lane => (Array.range rows).foldl (stepRow lane) out)
      (Array.replicate (width * rows) 0) =
      (List.range' 0 lanes).foldl stepLane (Array.replicate (width * rows) 0) := by
    rw [← Array.foldl_toList, array_range_toList]
    congr 1
    funext out lane
    rw [← Array.foldl_toList, array_range_toList]
  rw [hconv]
  split
  · rename_i hhit
    let k0 := width - 1 - col
    have hk0_lt : k0 < lanes := by omega
    rw [foldl_range'_hit 0 lanes (Array.replicate (width * rows) 0) 0
      (rowIndex * width + col) k0 (Nat.zero_le _) (by omega) stepLane
      (fun acc k _ hk hne => hstepLane_miss acc k (by omega) (by omega))]
    let mid := (List.range' 0 (k0 - 0)).foldl stepLane (Array.replicate (width * rows) 0)
    have hmid_sz : mid.size = width * rows := by
      dsimp only [mid]
      rw [foldl_range'_size 0 (k0 - 0) _ stepLane hstepLane_sz, Array.size_replicate]
    change (stepLane mid k0).getD (rowIndex * width + col) 0 = _
    dsimp only [stepLane]
    rw [foldl_range'_hit 0 rows mid 0 (rowIndex * width + col) rowIndex
      (Nat.zero_le _) (by omega) (stepRow k0) (fun acc r _ _ hne => by
        apply setIf_getD_other
        intro heq
        have hk0_col : width - 1 - k0 = col := by omega
        rw [hk0_col] at heq
        have hdiv : (r * width + col) / width = (rowIndex * width + col) / width :=
          congrArg (· / width) heq
        have h1 : (r * width + col) / width = r := by
          rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hcol, Nat.add_zero]
        have h2 : (rowIndex * width + col) / width = rowIndex := by
          rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hcol, Nat.add_zero]
        omega)]
    let mid2 := (List.range' 0 (rowIndex - 0)).foldl (stepRow k0) mid
    have hmid2_sz : mid2.size = width * rows := by
      dsimp only [mid2]
      rw [foldl_range'_size 0 (rowIndex - 0) mid (stepRow k0) (fun b _ => setIf_size _ _ _),
        hmid_sz]
    change (mid2.setIfInBounds (rowIndex * width + (width - 1 - k0))
      (message.getD (k0 * rows + rowIndex) 0)).getD (rowIndex * width + col) 0 = _
    have hk0_col : width - 1 - k0 = col := by omega
    rw [hk0_col, setIf_getD_same mid2 _ _ 0]
    have hbound : rowIndex * width + col < width * rows := by
      calc rowIndex * width + col < rowIndex * width + width := by omega
        _ = (rowIndex + 1) * width := by rw [Nat.succ_mul]
        _ ≤ rows * width := Nat.mul_le_mul_right width (by omega)
        _ = width * rows := Nat.mul_comm _ _
    omega
  · rename_i hmiss
    rw [foldl_range'_miss 0 lanes _ 0 (rowIndex * width + col) stepLane
      (fun acc k _ hk => hstepLane_miss acc k (by omega) (by omega))]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl

private theorem firstCosetColLoop_succ (message : Array K) (lanes width rows rowIndex : Nat)
    (rem v : Nat) (out : Array Vec8) :
    Model.Pcs.Commit.firstCosetColLoop message lanes width rows rowIndex (rem + 1) v out =
      let base := 8 * v
      let word (j : Nat) : K :=
        let col := base + j
        if col + lanes ≥ width then
          message.getD ((width - 1 - col) * rows + rowIndex) 0
        else 0
      Model.Pcs.Commit.firstCosetColLoop message lanes width rows rowIndex rem (v + 1)
        (out.push ⟨word 0, word 1, word 2, word 3, word 4, word 5, word 6, word 7⟩) := by
  unfold Model.Pcs.Commit.firstCosetColLoop
  exact foldRangeLoop_succ _ rem v out

private theorem firstCosetRowLoop_succ (message : Array K) (lanes nVecs rows : Nat)
    (rem r : Nat) (out : Array Vec8) :
    Model.Pcs.Commit.firstCosetRowLoop message lanes nVecs rows (rem + 1) r out =
      Model.Pcs.Commit.firstCosetRowLoop message lanes nVecs rows rem (r + 1)
        (Model.Pcs.Commit.firstCosetColLoop message lanes (8 * nVecs) rows r nVecs 0 out) := by
  unfold Model.Pcs.Commit.firstCosetRowLoop
  exact foldRangeLoop_succ _ rem r out

private theorem firstCosetColLoop_eq (message : Array K) (lanes width rows rowIndex : Nat)
    (rem v : Nat) (out : Array Vec8) :
    Model.Pcs.Commit.firstCosetColLoop message lanes width rows rowIndex rem v out =
      out ++ ((List.range' v rem).map (fun k =>
        let word (j : Nat) : K :=
          let col := 8 * k + j
          if col + lanes ≥ width then
            message.getD ((width - 1 - col) * rows + rowIndex) 0
          else 0
        (⟨word 0, word 1, word 2, word 3, word 4, word 5, word 6, word 7⟩ : Vec8))).toArray := by
  induction rem generalizing v out with
  | zero =>
    change out = _
    simp
  | succ rem ih =>
    rw [firstCosetColLoop_succ, ih, List.range'_succ, List.map_cons]
    apply Array.toList_inj.mp
    simp [Array.toList_append, Array.toList_push, List.append_assoc]

private theorem firstCosetRowLoop_size (message : Array K) (lanes nVecs rows : Nat)
    (rem r : Nat) (out : Array Vec8) :
    (Model.Pcs.Commit.firstCosetRowLoop message lanes nVecs rows rem r out).size =
      out.size + rem * nVecs := by
  induction rem generalizing r out with
  | zero =>
    change out.size = _
    simp
  | succ rem ih =>
    rw [firstCosetRowLoop_succ, ih, firstCosetColLoop_eq]
    simp [Nat.succ_mul]
    omega

private theorem firstCosetRowLoop_prefix (message : Array K) (lanes nVecs rows : Nat)
    (rem r : Nat) (out : Array Vec8) (idx : Nat) (hidx : idx < out.size) :
    (Model.Pcs.Commit.firstCosetRowLoop message lanes nVecs rows rem r out).getD idx default =
      out.getD idx default := by
  induction rem generalizing r out with
  | zero => rfl
  | succ rem ih =>
    rw [firstCosetRowLoop_succ]
    let nextOut := Model.Pcs.Commit.firstCosetColLoop message lanes (8 * nVecs) rows r nVecs 0 out
    have hnext_eq := firstCosetColLoop_eq message lanes (8 * nVecs) rows r nVecs 0 out
    have hidx2 : idx < nextOut.size := by
      dsimp only [nextOut]
      rw [hnext_eq]
      simp
      omega
    rw [ih (r + 1) nextOut hidx2]
    dsimp only [nextOut]
    rw [hnext_eq]
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_append, hidx]

private theorem firstCosetRowLoop_getD (message : Array K) (lanes nVecs rows : Nat)
    (rem r : Nat) (out : Array Vec8) (rowOff v : Nat) (hrowOff : rowOff < rem) (hv : v < nVecs) :
    (Model.Pcs.Commit.firstCosetRowLoop message lanes nVecs rows rem r out).getD
        (out.size + rowOff * nVecs + v) default =
      let rowIndex := r + rowOff
      let width := 8 * nVecs
      let word (j : Nat) : K :=
        let col := 8 * v + j
        if col + lanes ≥ width then
          message.getD ((width - 1 - col) * rows + rowIndex) 0
        else 0
      ⟨word 0, word 1, word 2, word 3, word 4, word 5, word 6, word 7⟩ := by
  induction rem generalizing r out rowOff with
  | zero => omega
  | succ rem ih =>
    rw [firstCosetRowLoop_succ]
    let nextOut := Model.Pcs.Commit.firstCosetColLoop message lanes (8 * nVecs) rows r nVecs 0 out
    have hnext_eq : nextOut = _ :=
      firstCosetColLoop_eq message lanes (8 * nVecs) rows r nVecs 0 out
    have hnext_sz : nextOut.size = out.size + nVecs := by
      rw [hnext_eq]; simp
    cases rowOff with
    | zero =>
      have hidx : out.size + 0 * nVecs + v = out.size + v := by omega
      rw [hidx, Nat.add_zero]
      rw [firstCosetRowLoop_prefix message lanes nVecs rows rem (r + 1) nextOut (out.size + v)
        (by omega), hnext_eq]
      have hlt_out : ¬ (out.size + v < out.size) := by omega
      have hsub_v : out.size + v - out.size = v := by omega
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_append]
      simp only [hlt_out, ↓reduceIte, hsub_v]
      have hv_arr : v < ((List.range' 0 nVecs).map (fun k =>
          let word (j : Nat) : K :=
            let col := 8 * k + j
            if col + lanes ≥ 8 * nVecs then
              message.getD ((8 * nVecs - 1 - col) * rows + r) 0
            else 0
          (⟨word 0, word 1, word 2, word 3, word 4, word 5, word 6, word 7⟩ : Vec8))).toArray.size := by
        simp [hv]
      rw [Array.getElem?_eq_getElem hv_arr, Option.getD_some]
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range', Nat.zero_add,
        Nat.one_mul, Nat.add_zero]
    | succ rowOff =>
      have hidx : out.size + (rowOff + 1) * nVecs + v = nextOut.size + rowOff * nVecs + v := by
        rw [hnext_sz, Nat.succ_mul]
        omega
      rw [hidx, ih (r + 1) nextOut rowOff (by omega)]
      have hr : r + 1 + rowOff = r + (rowOff + 1) := by omega
      rw [hr]

theorem firstCosetVec8_size (message : Array K) (lanes nVecs logRows : Nat) :
    (Model.Pcs.Commit.firstCosetVec8 message lanes nVecs logRows).size =
      (1 <<< logRows) * nVecs := by
  unfold Model.Pcs.Commit.firstCosetVec8
  rw [firstCosetRowLoop_size]
  simp

theorem firstCosetVec8_lane_eq_transpose (message : Array K) (lanes nVecs logRows rowIndex v j : Nat)
    (hlanes : lanes ≤ 8 * nVecs) (hrow : rowIndex < 1 <<< logRows) (hv : v < nVecs) (hj : j < 8) :
    ((Model.Pcs.Commit.firstCosetVec8 message lanes nVecs logRows).getD
        (rowIndex * nVecs + v) default).lane j =
      (Spec.Pcs.Commit.transpose message lanes (8 * nVecs) logRows).getD
        (rowIndex * (8 * nVecs) + (8 * v + j)) 0 := by
  unfold Model.Pcs.Commit.firstCosetVec8
  have hemp : (Array.emptyWithCapacity ((1 <<< logRows) * nVecs) : Array Vec8).size = 0 := rfl
  have hidx : rowIndex * nVecs + v =
      (Array.emptyWithCapacity ((1 <<< logRows) * nVecs) : Array Vec8).size +
        rowIndex * nVecs + v := by
    rw [hemp, Nat.zero_add]
  rw [hidx, firstCosetRowLoop_getD message lanes nVecs (1 <<< logRows) (1 <<< logRows) 0 _
    rowIndex v hrow hv, Nat.zero_add]
  rw [transpose_getD message lanes (8 * nVecs) logRows rowIndex (8 * v + j) hlanes hrow (by omega)]
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rfl
  | _ + 8 => omega

private theorem replicate_go_size (block : Array K) (s n : Nat) (acc : Array K) :
    ((List.range' s n).foldl (fun a _ => a ++ block) acc).size = acc.size + n * block.size := by
  induction n generalizing s acc with
  | zero => simp
  | succ n ih =>
    rw [List.range'_succ, List.foldl_cons, ih]
    simp [Nat.succ_mul]
    omega

private theorem replicate_go_prefix (block : Array K) (s n : Nat) (acc : Array K) (idx : Nat)
    (hidx : idx < acc.size) :
    ((List.range' s n).foldl (fun a _ => a ++ block) acc).getD idx 0 = acc.getD idx 0 := by
  induction n generalizing s acc with
  | zero => rfl
  | succ n ih =>
    rw [List.range'_succ, List.foldl_cons]
    have hidx2 : idx < (acc ++ block).size := by simp; omega
    rw [ih (s + 1) (acc ++ block) hidx2]
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_append, hidx]

private theorem replicate_go_getD (block : Array K) (s n : Nat) (acc : Array K)
    (c off : Nat) (hc : c < n) (hoff : off < block.size) :
    ((List.range' s n).foldl (fun a _ => a ++ block) acc).getD
        (acc.size + c * block.size + off) 0 = block.getD off 0 := by
  induction n generalizing s acc c with
  | zero => omega
  | succ n ih =>
    rw [List.range'_succ, List.foldl_cons]
    cases c with
    | zero =>
      have hidx : acc.size + 0 * block.size + off = acc.size + off := by omega
      rw [hidx, replicate_go_prefix block (s + 1) n (acc ++ block) (acc.size + off)
        (by simp; omega)]
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_append, hoff]
    | succ c =>
      have hidx : acc.size + (c + 1) * block.size + off =
          (acc ++ block).size + c * block.size + off := by
        simp [Nat.succ_mul]
        omega
      rw [hidx, ih (s + 1) (acc ++ block) c (by omega)]

theorem replicate_size (block : Array K) (rate : Nat) :
    (Spec.Pcs.Commit.replicate block rate).size = rate * block.size := by
  unfold Spec.Pcs.Commit.replicate
  rw [← Array.foldl_toList, array_range_toList, replicate_go_size]
  simp

theorem replicate_getD (block : Array K) (rate c off : Nat)
    (hc : c < rate) (hoff : off < block.size) :
    (Spec.Pcs.Commit.replicate block rate).getD (c * block.size + off) 0 =
      block.getD off 0 := by
  unfold Spec.Pcs.Commit.replicate
  rw [← Array.foldl_toList, array_range_toList]
  have hidx : c * block.size + off = (#[] : Array K).size + c * block.size + off := by simp
  rw [hidx]
  exact replicate_go_getD block 0 rate #[] c off hc hoff

private theorem butterflyVec8U_lane (top bot : Vec8) (t : K) (j : Nat) (hj : j < 8) :
    (Model.Pcs.Ntt.butterflyVec8U top bot t).lane j =
      (Spec.Pcs.Ntt.butterfly (top.lane j) (bot.lane j) t).1 := by
  unfold Model.Pcs.Ntt.butterflyVec8U Spec.Pcs.Ntt.butterfly
  by_cases ht : t = 0
  · subst ht
    have hmul0 : Spec.Field.mul (bot.lane j) 0 = 0 := by
      rw [← Proofs.Field.mul_refines_spec, Proofs.Field.mul_zero_right]
    simp [Spec.Field.add, hmul0, UInt64.xor_zero]
  · simp only [ht, ↓reduceIte]
    match j with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 =>
      simp [Vec8.lane, Spec.Field.add, nativeMul_eq_spec]
    | _ + 8 => omega

private theorem butterflyVec8V_lane (top bot : Vec8) (t : K) (j : Nat) (hj : j < 8) :
    (Model.Pcs.Ntt.butterflyVec8V bot (Model.Pcs.Ntt.butterflyVec8U top bot t)).lane j =
      (Spec.Pcs.Ntt.butterfly (top.lane j) (bot.lane j) t).2 := by
  have hu := butterflyVec8U_lane top bot t j hj
  unfold Spec.Pcs.Ntt.butterfly at hu ⊢
  dsimp only at hu ⊢
  rw [← hu]
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rfl
  | _ + 8 => omega

theorem encodeLayer_size (data : Array K) (lanes layer logD : Nat) :
    (Spec.Pcs.Ntt.encodeLayer data lanes layer logD).size = data.size := by
  unfold Spec.Pcs.Ntt.encodeLayer
  rw [← Array.foldl_toList, array_range_toList]
  refine foldl_range'_size 0 _ data _ ?_
  intro acc _
  rw [← Array.foldl_toList, array_range_toList]
  refine foldl_range'_size 0 _ acc _ ?_
  intro acc _
  rw [← Array.foldl_toList, array_range_toList]
  refine foldl_range'_size 0 _ acc _ ?_
  intro acc _
  rw [setIf_size, setIf_size]

private theorem pow2_split (a b : Nat) (hb : b < a) :
    2 ^ b * (2 * 2 ^ (a - b - 1)) = 2 ^ a := by
  have heq : a = b + 1 + (a - b - 1) := by omega
  conv => rhs; rw [heq]
  rw [Nat.pow_add, Nat.pow_succ, Nat.mul_assoc]

theorem encodeLayer_getD (data : Array K) (lanes layer logD r l : Nat)
    (hlayer : layer < logD) (hsz : data.size = 2 ^ logD * lanes)
    (hr : r < 2 ^ logD) (hl : l < lanes) :
    let half := 1 <<< (logD - layer - 1)
    let block := r / (2 * half)
    let rem := r % (2 * half)
    let t := Spec.Pcs.Ntt.twiddle logD layer block
    (Spec.Pcs.Ntt.encodeLayer data lanes layer logD).getD (r * lanes + l) 0 =
      if rem < half then
        (Spec.Pcs.Ntt.butterfly
          (data.getD (r * lanes + l) 0) (data.getD ((r + half) * lanes + l) 0) t).1
      else
        (Spec.Pcs.Ntt.butterfly
          (data.getD ((r - half) * lanes + l) 0) (data.getD (r * lanes + l) 0) t).2 := by
  have hlanes_pos : 0 < lanes := by omega
  let blocks := 1 <<< layer
  let half := 1 <<< (logD - layer - 1)
  have hblocks : blocks = 2 ^ layer := by simp [blocks, Nat.shiftLeft_eq]
  have hhalf : half = 2 ^ (logD - layer - 1) := by simp [half, Nat.shiftLeft_eq]
  have hhalf_pos : 0 < half := by rw [hhalf]; exact Nat.two_pow_pos _
  have hprod : blocks * (2 * half) = 2 ^ logD := by
    rw [hblocks, hhalf]
    exact pow2_split logD layer hlayer
  let b0 := r / (2 * half)
  let rem0 := r % (2 * half)
  have hb0 : b0 < blocks := by
    have hr_lt : r < blocks * (2 * half) := by omega
    exact (Nat.div_lt_iff_lt_mul (by omega)).2 hr_lt
  have hrem0 : rem0 < 2 * half := Nat.mod_lt r (by omega)
  have hr_eq : r = b0 * (2 * half) + rem0 := by
    have hdiv := Nat.div_add_mod r (2 * half)
    rw [Nat.mul_comm] at hdiv
    exact hdiv.symm
  let stepLane (top bot : Nat) (t : K) (acc : Array K) (lane : Nat) : Array K :=
    let pair := Spec.Pcs.Ntt.butterfly (acc.getD (top + lane) 0) (acc.getD (bot + lane) 0) t
    (acc.setIfInBounds (top + lane) pair.1).setIfInBounds (bot + lane) pair.2
  let stepRow (block : Nat) (t : K) (acc : Array K) (rowIdx : Nat) : Array K :=
    let top := (block * (2 * half) + rowIdx) * lanes
    let bot := top + half * lanes
    (List.range' 0 lanes).foldl (stepLane top bot t) acc
  let stepBlock (acc : Array K) (block : Nat) : Array K :=
    let t := Spec.Pcs.Ntt.twiddle logD layer block
    (List.range' 0 half).foldl (stepRow block t) acc
  have hstepLane_sz (top bot : Nat) (t : K) (acc : Array K) (lane : Nat) :
      (stepLane top bot t acc lane).size = acc.size := by
    dsimp only [stepLane]; rw [setIf_size, setIf_size]
  have hstepRow_sz (block : Nat) (t : K) (acc : Array K) (rowIdx : Nat) :
      (stepRow block t acc rowIdx).size = acc.size :=
    foldl_range'_size 0 lanes acc _ (hstepLane_sz _ _ t)
  have hstepBlock_sz (acc : Array K) (block : Nat) :
      (stepBlock acc block).size = acc.size :=
    foldl_range'_size 0 half acc _ (hstepRow_sz block _)
  have hlane_miss (topR botR : Nat) (t : K) (acc : Array K) (q : Nat) (hq_row : q / lanes ≠ topR ∧ q / lanes ≠ botR) :
      ((List.range' 0 lanes).foldl (stepLane (topR * lanes) (botR * lanes) t) acc).getD q 0 =
        acc.getD q 0 := by
    refine foldl_range'_miss 0 lanes acc 0 q _ ?_
    intro cur lane _ hlane
    dsimp only [stepLane]
    rw [setIf_getD_other, setIf_getD_other]
    · intro heq
      have hdiv : (topR * lanes + lane) / lanes = q / lanes := congrArg (· / lanes) heq
      rw [Nat.mul_comm, Nat.mul_add_div hlanes_pos, Nat.div_eq_of_lt (by omega), Nat.add_zero] at hdiv
      exact hq_row.1 hdiv.symm
    · intro heq
      have hdiv : (botR * lanes + lane) / lanes = q / lanes := congrArg (· / lanes) heq
      rw [Nat.mul_comm, Nat.mul_add_div hlanes_pos, Nat.div_eq_of_lt (by omega), Nat.add_zero] at hdiv
      exact hq_row.2 hdiv.symm
  have hrow_miss_block (block : Nat) (acc : Array K) (q : Nat)
      (hq_blk : (q / lanes) / (2 * half) ≠ block) :
      (stepBlock acc block).getD q 0 = acc.getD q 0 := by
    refine foldl_range'_miss 0 half acc 0 q _ ?_
    intro cur rowIdx _ hrowIdx
    dsimp only [stepRow]
    have hbot : (block * (2 * half) + rowIdx) * lanes + half * lanes =
        (block * (2 * half) + rowIdx + half) * lanes := by
      rw [← Nat.add_mul]
    rw [hbot]
    apply hlane_miss
    constructor <;> intro hEq
    · have : (q / lanes) / (2 * half) = block := by
        rw [hEq, Nat.mul_comm block, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
      exact hq_blk this
    · have : (q / lanes) / (2 * half) = block := by
        have hsum : block * (2 * half) + rowIdx + half = block * (2 * half) + (rowIdx + half) := by omega
        rw [hEq, hsum, Nat.mul_comm block, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
      exact hq_blk this
  have hconv : Spec.Pcs.Ntt.encodeLayer data lanes layer logD =
      (List.range' 0 blocks).foldl stepBlock data := by
    unfold Spec.Pcs.Ntt.encodeLayer
    rw [← Array.foldl_toList, array_range_toList]
    congr 1; funext a1 b1
    rw [← Array.foldl_toList, array_range_toList]
    congr 1; funext a2 r2
    rw [← Array.foldl_toList, array_range_toList]
  have hqr_div : (r * lanes + l) / lanes = r := by
    rw [Nat.mul_comm, Nat.mul_add_div hlanes_pos, Nat.div_eq_of_lt hl, Nat.add_zero]
  rw [hconv]
  rw [foldl_range'_hit 0 blocks data 0 (r * lanes + l) b0 (Nat.zero_le _) (by omega) stepBlock
    (fun acc k _ _ hne => hrow_miss_block k acc (r * lanes + l) (by rw [hqr_div]; exact hne.symm))]
  let preB := (List.range' 0 (b0 - 0)).foldl stepBlock data
  have hpreB_sz : preB.size = data.size := foldl_range'_size 0 (b0 - 0) data stepBlock hstepBlock_sz
  have hpreB_same (q : Nat) (hq : (q / lanes) / (2 * half) = b0) :
      preB.getD q 0 = data.getD q 0 := by
    dsimp only [preB]
    exact foldl_range'_miss 0 (b0 - 0) data 0 q stepBlock
      (fun acc k _ hk => hrow_miss_block k acc q (by omega))
  change (stepBlock preB b0).getD (r * lanes + l) 0 = _
  dsimp only [stepBlock]
  let t0 := Spec.Pcs.Ntt.twiddle logD layer b0
  let rIdx := if rem0 < half then rem0 else rem0 - half
  have hrIdx : rIdx < half := by dsimp only [rIdx]; split <;> omega
  have hrow_miss (cur : Array K) (k : Nat) (hk : k < half) (hne : k ≠ rIdx) (q : Nat)
      (hq : q / lanes = b0 * (2 * half) + rIdx ∨ q / lanes = b0 * (2 * half) + rIdx + half) :
      (stepRow b0 t0 cur k).getD q 0 = cur.getD q 0 := by
    dsimp only [stepRow]
    have hbot : (b0 * (2 * half) + k) * lanes + half * lanes =
        (b0 * (2 * half) + k + half) * lanes := by rw [← Nat.add_mul]
    rw [hbot]
    apply hlane_miss
    rcases hq with hq1 | hq2 <;> constructor <;> omega
  have hqr_cases : (r * lanes + l) / lanes = b0 * (2 * half) + rIdx ∨
      (r * lanes + l) / lanes = b0 * (2 * half) + rIdx + half := by
    rw [hqr_div]
    dsimp only [rIdx]
    split
    · left; omega
    · right; omega
  change ((List.range' 0 half).foldl (stepRow b0 t0) preB).getD (r * lanes + l) 0 = _
  rw [foldl_range'_hit 0 half preB 0 (r * lanes + l) rIdx (Nat.zero_le _) (by omega)
    (stepRow b0 t0) (fun cur k _ hk hne => hrow_miss cur k (by omega) hne _ hqr_cases)]
  let preR := (List.range' 0 (rIdx - 0)).foldl (stepRow b0 t0) preB
  have hpreR_sz : preR.size = data.size := by
    dsimp only [preR]
    rw [foldl_range'_size 0 (rIdx - 0) preB (stepRow b0 t0) (hstepRow_sz b0 t0), hpreB_sz]
  let topR := b0 * (2 * half) + rIdx
  let botR := topR + half
  have hbotR_lt : botR < 2 ^ logD := by
    have hstep1 : botR < b0 * (2 * half) + (2 * half) := by
      dsimp only [botR, topR]
      omega
    have hstep2 : b0 * (2 * half) + 1 * (2 * half) = (b0 + 1) * (2 * half) :=
      (Nat.add_mul b0 1 (2 * half)).symm
    rw [Nat.one_mul] at hstep2
    calc botR < (b0 + 1) * (2 * half) := by rw [← hstep2]; exact hstep1
      _ ≤ blocks * (2 * half) := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ logD := hprod
  have htop_preR : preR.getD (topR * lanes + l) 0 = data.getD (topR * lanes + l) 0 := by
    have h1 : preR.getD (topR * lanes + l) 0 = preB.getD (topR * lanes + l) 0 := by
      dsimp only [preR]
      refine foldl_range'_miss 0 (rIdx - 0) preB 0 (topR * lanes + l) (stepRow b0 t0) ?_
      intro cur k _ hk
      apply hrow_miss cur k (by omega) (by omega)
      left
      rw [Nat.mul_comm, Nat.mul_add_div hlanes_pos, Nat.div_eq_of_lt hl, Nat.add_zero]
    rw [h1]
    apply hpreB_same
    rw [Nat.mul_comm topR, Nat.mul_add_div hlanes_pos, Nat.div_eq_of_lt hl, Nat.add_zero]
    dsimp only [topR]
    rw [Nat.mul_comm b0, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
  have hbot_preR : preR.getD (botR * lanes + l) 0 = data.getD (botR * lanes + l) 0 := by
    have h1 : preR.getD (botR * lanes + l) 0 = preB.getD (botR * lanes + l) 0 := by
      dsimp only [preR]
      refine foldl_range'_miss 0 (rIdx - 0) preB 0 (botR * lanes + l) (stepRow b0 t0) ?_
      intro cur k _ hk
      apply hrow_miss cur k (by omega) (by omega)
      right
      rw [Nat.mul_comm, Nat.mul_add_div hlanes_pos, Nat.div_eq_of_lt hl, Nat.add_zero]
    rw [h1]
    apply hpreB_same
    rw [Nat.mul_comm botR, Nat.mul_add_div hlanes_pos, Nat.div_eq_of_lt hl, Nat.add_zero]
    have hb : botR = b0 * (2 * half) + (rIdx + half) := by omega
    rw [hb, Nat.mul_comm b0, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
  change (stepRow b0 t0 preR rIdx).getD (r * lanes + l) 0 = _
  dsimp only [stepRow]
  have hbot_eq : (b0 * (2 * half) + rIdx) * lanes + half * lanes = botR * lanes := by
    dsimp only [botR, topR]
    rw [← Nat.add_mul]
  have htop_eq : (b0 * (2 * half) + rIdx) * lanes = topR * lanes := rfl
  rw [hbot_eq, htop_eq]
  have hlane_other (cur : Array K) (k : Nat) (hk : k < lanes) (hne : k ≠ l) (qRow : Nat) :
      (stepLane (topR * lanes) (botR * lanes) t0 cur k).getD (qRow * lanes + l) 0 =
        cur.getD (qRow * lanes + l) 0 := by
    dsimp only [stepLane]
    rw [setIf_getD_other, setIf_getD_other]
    · intro heq
      have hmod := congrArg (· % lanes) heq
      rw [Nat.mul_comm topR, Nat.mul_add_mod, Nat.mod_eq_of_lt hk,
        Nat.mul_comm qRow, Nat.mul_add_mod, Nat.mod_eq_of_lt hl] at hmod
      exact hne hmod
    · intro heq
      have hmod := congrArg (· % lanes) heq
      rw [Nat.mul_comm botR, Nat.mul_add_mod, Nat.mod_eq_of_lt hk,
        Nat.mul_comm qRow, Nat.mul_add_mod, Nat.mod_eq_of_lt hl] at hmod
      exact hne hmod
  rw [foldl_range'_hit 0 lanes preR 0 (r * lanes + l) l (Nat.zero_le _) (by omega)
    (stepLane (topR * lanes) (botR * lanes) t0)
    (fun cur k _ hk hne => hlane_other cur k (by omega) hne r)]
  let preL := (List.range' 0 (l - 0)).foldl (stepLane (topR * lanes) (botR * lanes) t0) preR
  have hpreL_sz : preL.size = data.size := by
    dsimp only [preL]
    rw [foldl_range'_size 0 (l - 0) preR _ (hstepLane_sz _ _ t0), hpreR_sz]
  have htop_preL : preL.getD (topR * lanes + l) 0 = data.getD (topR * lanes + l) 0 := by
    rw [← htop_preR]
    exact foldl_range'_miss 0 (l - 0) preR 0 (topR * lanes + l) _
      (fun cur k _ hk => hlane_other cur k (by omega) (by omega) topR)
  have hbot_preL : preL.getD (botR * lanes + l) 0 = data.getD (botR * lanes + l) 0 := by
    rw [← hbot_preR]
    exact foldl_range'_miss 0 (l - 0) preR 0 (botR * lanes + l) _
      (fun cur k _ hk => hlane_other cur k (by omega) (by omega) botR)
  have htop_in : topR * lanes + l < preL.size := by
    rw [hpreL_sz, hsz]
    calc topR * lanes + l < topR * lanes + lanes := by omega
      _ = (topR + 1) * lanes := by rw [Nat.succ_mul]
      _ ≤ 2 ^ logD * lanes := Nat.mul_le_mul_right _ (by omega)
  have hbot_in : botR * lanes + l < preL.size := by
    rw [hpreL_sz, hsz]
    calc botR * lanes + l < botR * lanes + lanes := by omega
      _ = (botR + 1) * lanes := by rw [Nat.succ_mul]
      _ ≤ 2 ^ logD * lanes := Nat.mul_le_mul_right _ (by omega)
  have hne_tb : botR * lanes + l ≠ topR * lanes + l := by
    intro heq
    have : botR * lanes = topR * lanes := by omega
    have : botR = topR := Nat.eq_of_mul_eq_mul_right hlanes_pos this
    omega
  change (((preL.setIfInBounds (topR * lanes + l)
      (Spec.Pcs.Ntt.butterfly (preL.getD (topR * lanes + l) 0) (preL.getD (botR * lanes + l) 0) t0).1
    ).setIfInBounds (botR * lanes + l)
      (Spec.Pcs.Ntt.butterfly (preL.getD (topR * lanes + l) 0) (preL.getD (botR * lanes + l) 0) t0).2
    ).getD (r * lanes + l) 0) =
      if rem0 < half then
        (Spec.Pcs.Ntt.butterfly
          (data.getD (r * lanes + l) 0) (data.getD ((r + half) * lanes + l) 0) t0).1
      else
        (Spec.Pcs.Ntt.butterfly
          (data.getD ((r - half) * lanes + l) 0) (data.getD (r * lanes + l) 0) t0).2
  rw [htop_preL, hbot_preL]
  split
  · rename_i hlt_rem
    have hr_top : topR = r := by
      dsimp only [topR, rIdx]
      rw [if_pos hlt_rem]
      exact hr_eq.symm
    have hbot_r : botR = r + half := by
      dsimp only [botR]
      rw [hr_top]
    rw [setIf_getD_other _ (botR * lanes + l) (r * lanes + l) _ 0 (by rw [← hr_top]; exact hne_tb)]
    rw [← hr_top] at *
    rw [setIf_getD_same _ _ _ 0 htop_in]
  · rename_i hge_rem
    have hr_bot : botR = r := by
      dsimp only [botR, topR, rIdx]
      rw [if_neg hge_rem]
      omega
    have htop_r : topR = r - half := by
      have : topR + half = r := hr_bot
      omega
    rw [← hr_bot]
    rw [setIf_getD_same _ _ _ 0 (by rw [setIf_size]; exact hbot_in)]
    rw [hr_bot, htop_r]

private theorem vecPairLoop_size (topBase botBase : Nat) (t : K) (rem v : Nat) (data : Array Vec8) :
    (Model.Pcs.Ntt.vecPairLoop topBase botBase t rem v data).size = data.size := by
  unfold Model.Pcs.Ntt.vecPairLoop
  rw [foldRangeLoop_eq_range']
  refine foldl_range'_size v rem data _ ?_
  intro acc _
  rw [setIf_size, setIf_size, setIf_size, setIf_size]

private theorem rowPairLoop_size (blockRowBase half nVecs : Nat) (t : K) (rem rowIndex : Nat)
    (data : Array Vec8) :
    (Model.Pcs.Ntt.rowPairLoop blockRowBase half nVecs t rem rowIndex data).size = data.size := by
  unfold Model.Pcs.Ntt.rowPairLoop
  rw [foldRangeLoop_eq_range']
  exact foldl_range'_size rowIndex rem data _ (fun acc _ => vecPairLoop_size _ _ _ _ _ acc)

private theorem cosetBlockLoop_size (values : Array K) (blockBase half nVecs rem localBlock : Nat)
    (data : Array Vec8) :
    (Model.Pcs.Ntt.cosetBlockLoop values blockBase half nVecs rem localBlock data).size =
      data.size := by
  unfold Model.Pcs.Ntt.cosetBlockLoop
  rw [foldRangeLoop_eq_range']
  exact foldl_range'_size localBlock rem data _ (fun acc _ => rowPairLoop_size _ _ _ _ _ _ acc)

private theorem vecPairLoop_miss (topBase botBase : Nat) (t : K) (nVecs : Nat) (data : Array Vec8)
    (q : Nat) (hq : ∀ v < nVecs, q ≠ topBase + v ∧ q ≠ botBase + v) :
    (Model.Pcs.Ntt.vecPairLoop topBase botBase t nVecs 0 data).getD q default = data.getD q default := by
  let step (acc : Array Vec8) (v : Nat) : Array Vec8 :=
    let topV := acc.getD (topBase + v) default
    let botV := acc.getD (botBase + v) default
    let acc := (acc.setIfInBounds (topBase + v) default).setIfInBounds (botBase + v) default
    let uV := Model.Pcs.Ntt.butterflyVec8U topV botV t
    let vV := Model.Pcs.Ntt.butterflyVec8V botV uV
    (acc.setIfInBounds (topBase + v) uV).setIfInBounds (botBase + v) vV
  have hconv : Model.Pcs.Ntt.vecPairLoop topBase botBase t nVecs 0 data =
      (List.range' 0 nVecs).foldl step data := by
    unfold Model.Pcs.Ntt.vecPairLoop
    exact foldRangeLoop_eq_range' step nVecs 0 data
  rw [hconv]
  refine foldl_range'_miss 0 nVecs data default q step ?_
  intro acc v _ hv
  dsimp only [step]
  have hne1 : topBase + v ≠ q := (hq v (by omega)).1.symm
  have hne2 : botBase + v ≠ q := (hq v (by omega)).2.symm
  rw [setIf_getD_other _ (botBase + v) q _ _ hne2, setIf_getD_other _ (topBase + v) q _ _ hne1,
    setIf_getD_other _ (botBase + v) q _ _ hne2, setIf_getD_other _ (topBase + v) q _ _ hne1]

private theorem vecPairLoop_lane (topR botR : Nat) (t : K) (nVecs : Nat) (data : Array Vec8)
    (v0 j : Nat) (hv0 : v0 < nVecs) (hj : j < 8) (hnvecs_pos : 0 < nVecs) (hne_rows : topR ≠ botR)
    (htop_in : topR * nVecs + v0 < data.size) (hbot_in : botR * nVecs + v0 < data.size) :
    let topBase := topR * nVecs
    let botBase := botR * nVecs
    ((Model.Pcs.Ntt.vecPairLoop topBase botBase t nVecs 0 data).getD (topBase + v0) default).lane j =
      (Spec.Pcs.Ntt.butterfly ((data.getD (topBase + v0) default).lane j)
        ((data.getD (botBase + v0) default).lane j) t).1 ∧
    ((Model.Pcs.Ntt.vecPairLoop topBase botBase t nVecs 0 data).getD (botBase + v0) default).lane j =
      (Spec.Pcs.Ntt.butterfly ((data.getD (topBase + v0) default).lane j)
        ((data.getD (botBase + v0) default).lane j) t).2 := by
  intro topBase botBase
  have hrow_div (r k : Nat) (hk : k < nVecs) : (r * nVecs + k) / nVecs = r := by
    rw [Nat.mul_comm, Nat.mul_add_div hnvecs_pos, Nat.div_eq_of_lt hk, Nat.add_zero]
  have hne_tb : topBase + v0 ≠ botBase + v0 := by
    intro heq
    have hdiv : (topBase + v0) / nVecs = (botBase + v0) / nVecs := congrArg (· / nVecs) heq
    dsimp only [topBase, botBase] at hdiv
    rw [hrow_div topR v0 hv0, hrow_div botR v0 hv0] at hdiv
    exact hne_rows hdiv
  let step (acc : Array Vec8) (v : Nat) : Array Vec8 :=
    let topV := acc.getD (topBase + v) default
    let botV := acc.getD (botBase + v) default
    let acc := (acc.setIfInBounds (topBase + v) default).setIfInBounds (botBase + v) default
    let uV := Model.Pcs.Ntt.butterflyVec8U topV botV t
    let vV := Model.Pcs.Ntt.butterflyVec8V botV uV
    (acc.setIfInBounds (topBase + v) uV).setIfInBounds (botBase + v) vV
  have hconv : Model.Pcs.Ntt.vecPairLoop topBase botBase t nVecs 0 data =
      (List.range' 0 nVecs).foldl step data := by
    unfold Model.Pcs.Ntt.vecPairLoop
    exact foldRangeLoop_eq_range' step nVecs 0 data
  rw [hconv]
  have hstep_other : ∀ acc k, k < nVecs → k ≠ v0 →
      ∀ q, q = topBase + v0 ∨ q = botBase + v0 →
        (step acc k).getD q default = acc.getD q default := by
    intro acc k hk hne q hq
    dsimp only [step]
    have hkt : topBase + k ≠ topBase + v0 := by omega
    have hkb : botBase + k ≠ botBase + v0 := by omega
    have hktb : topBase + k ≠ botBase + v0 := by
      intro heq
      have hdiv : (topBase + k) / nVecs = (botBase + v0) / nVecs := congrArg (· / nVecs) heq
      dsimp only [topBase, botBase] at hdiv
      rw [hrow_div topR k hk, hrow_div botR v0 hv0] at hdiv
      exact hne_rows hdiv
    have hkbt : botBase + k ≠ topBase + v0 := by
      intro heq
      have hdiv : (botBase + k) / nVecs = (topBase + v0) / nVecs := congrArg (· / nVecs) heq
      dsimp only [topBase, botBase] at hdiv
      rw [hrow_div botR k hk, hrow_div topR v0 hv0] at hdiv
      exact hne_rows hdiv.symm
    rcases hq with rfl | rfl
    · rw [setIf_getD_other _ (botBase + k) (topBase + v0) _ _ hkbt,
        setIf_getD_other _ (topBase + k) (topBase + v0) _ _ hkt,
        setIf_getD_other _ (botBase + k) (topBase + v0) _ _ hkbt,
        setIf_getD_other _ (topBase + k) (topBase + v0) _ _ hkt]
    · rw [setIf_getD_other _ (botBase + k) (botBase + v0) _ _ hkb,
        setIf_getD_other _ (topBase + k) (botBase + v0) _ _ hktb,
        setIf_getD_other _ (botBase + k) (botBase + v0) _ _ hkb,
        setIf_getD_other _ (topBase + k) (botBase + v0) _ _ hktb]
  rw [foldl_range'_hit 0 nVecs data default (topBase + v0) v0 (Nat.zero_le _) (by omega) step
    (fun acc k _ hk hne => hstep_other acc k (by omega) hne (topBase + v0) (Or.inl rfl))]
  rw [foldl_range'_hit 0 nVecs data default (botBase + v0) v0 (Nat.zero_le _) (by omega) step
    (fun acc k _ hk hne => hstep_other acc k (by omega) hne (botBase + v0) (Or.inr rfl))]
  let pre := (List.range' 0 (v0 - 0)).foldl step data
  have hpre_top : pre.getD (topBase + v0) default = data.getD (topBase + v0) default := by
    dsimp only [pre]
    exact foldl_range'_miss 0 (v0 - 0) data default (topBase + v0) step
      (fun acc k _ hk => hstep_other acc k (by omega) (by omega) _ (Or.inl rfl))
  have hpre_bot : pre.getD (botBase + v0) default = data.getD (botBase + v0) default := by
    dsimp only [pre]
    exact foldl_range'_miss 0 (v0 - 0) data default (botBase + v0) step
      (fun acc k _ hk => hstep_other acc k (by omega) (by omega) _ (Or.inr rfl))
  have hpre_sz : pre.size = data.size := by
    dsimp only [pre]
    rw [foldl_range'_size 0 (v0 - 0) data step]
    intro acc k
    dsimp only [step]
    rw [setIf_size, setIf_size, setIf_size, setIf_size]
  have htop_in' : topBase + v0 < pre.size := by rw [hpre_sz]; exact htop_in
  have hbot_in' : botBase + v0 < pre.size := by rw [hpre_sz]; exact hbot_in
  change ((step pre v0).getD (topBase + v0) default).lane j = _ ∧
    ((step pre v0).getD (botBase + v0) default).lane j = _
  dsimp only [step]
  let cleared := (pre.setIfInBounds (topBase + v0) default).setIfInBounds (botBase + v0) default
  let uV := Model.Pcs.Ntt.butterflyVec8U (pre.getD (topBase + v0) default)
    (pre.getD (botBase + v0) default) t
  let vV := Model.Pcs.Ntt.butterflyVec8V (pre.getD (botBase + v0) default) uV
  have htop_lane : ((cleared.setIfInBounds (topBase + v0) uV).setIfInBounds (botBase + v0) vV
      ).getD (topBase + v0) default = uV := by
    rw [setIf_getD_other _ (botBase + v0) (topBase + v0) _ _ hne_tb.symm,
      setIf_getD_same _ _ _ _ (by rw [setIf_size, setIf_size]; exact htop_in')]
  have hbot_lane : ((cleared.setIfInBounds (topBase + v0) uV).setIfInBounds (botBase + v0) vV
      ).getD (botBase + v0) default = vV := by
    rw [setIf_getD_same _ _ _ _ (by rw [setIf_size, setIf_size, setIf_size]; exact hbot_in')]
  change (((cleared.setIfInBounds (topBase + v0) uV).setIfInBounds (botBase + v0) vV
      ).getD (topBase + v0) default).lane j = _ ∧
    (((cleared.setIfInBounds (topBase + v0) uV).setIfInBounds (botBase + v0) vV
      ).getD (botBase + v0) default).lane j = _
  rw [htop_lane, hbot_lane]
  dsimp only [uV, vV]
  rw [hpre_top, hpre_bot]
  exact ⟨butterflyVec8U_lane _ _ t j hj, butterflyVec8V_lane _ _ t j hj⟩

theorem encodeCosetLayerVec8_size (table : Array K) (data : Array Vec8)
    (nVecs logRows logInvRate coset step : Nat) :
    (Model.Pcs.Ntt.encodeCosetLayerVec8 table data nVecs logRows logInvRate coset step).size =
      data.size := by
  unfold Model.Pcs.Ntt.encodeCosetLayerVec8
  exact cosetBlockLoop_size _ _ _ _ _ _ _

theorem cosetStepLoop_size (table : Array K) (nVecs logRows logInvRate coset rem step : Nat)
    (data : Array Vec8) :
    (Model.Pcs.Ntt.cosetStepLoop table nVecs logRows logInvRate coset rem step data).size =
      data.size := by
  unfold Model.Pcs.Ntt.cosetStepLoop
  rw [foldRangeLoop_eq_range']
  exact foldl_range'_size step rem data _ (fun acc _ => encodeCosetLayerVec8_size _ acc _ _ _ _ _)

theorem encodeCosetLayerVec8_lane (buf : Array Vec8) (nVecs logRows logInvRate coset step : Nat)
    (localRow v j : Nat) (hstep : step < logRows) (hnvecs_pos : 0 < nVecs)
    (hsz : buf.size = 2 ^ logRows * nVecs)
    (hrow : localRow < 2 ^ logRows) (hv : v < nVecs) (hj : j < 8) :
    let logD := logRows + logInvRate
    let layer := logInvRate + step
    let half := 1 <<< (logRows - step - 1)
    let localBlock := localRow / (2 * half)
    let rem0 := localRow % (2 * half)
    let t := Spec.Pcs.Ntt.twiddle logD layer ((coset <<< step) + localBlock)
    ((Model.Pcs.Ntt.encodeCosetLayerVec8 (Model.Pcs.Ntt.evals logD) buf nVecs logRows logInvRate
        coset step).getD (localRow * nVecs + v) default).lane j =
      if rem0 < half then
        (Spec.Pcs.Ntt.butterfly
          ((buf.getD (localRow * nVecs + v) default).lane j)
          ((buf.getD (((localRow + half) * nVecs) + v) default).lane j) t).1
      else
        (Spec.Pcs.Ntt.butterfly
          ((buf.getD (((localRow - half) * nVecs) + v) default).lane j)
          ((buf.getD (localRow * nVecs + v) default).lane j) t).2 := by
  intro logD layer half localBlock rem0 t
  have hlocalBlocks : 1 <<< step = 2 ^ step := by simp [Nat.shiftLeft_eq]
  have hhalf : half = 2 ^ (logRows - step - 1) := by simp [half, Nat.shiftLeft_eq]
  have hhalf_pos : 0 < half := by rw [hhalf]; exact Nat.two_pow_pos _
  have hprod : (1 <<< step) * (2 * half) = 2 ^ logRows := by
    rw [hlocalBlocks, hhalf]
    exact pow2_split logRows step hstep
  have hblk_lt : localBlock < 1 <<< step := by
    dsimp only [localBlock]
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    calc localRow < 2 ^ logRows := hrow
      _ = (1 <<< step) * (2 * half) := hprod.symm
  have hrem0_lt : rem0 < 2 * half := Nat.mod_lt localRow (by omega)
  have hrow_eq : localRow = localBlock * (2 * half) + rem0 := by
    have hdiv := Nat.div_add_mod localRow (2 * half)
    rw [Nat.mul_comm] at hdiv
    exact hdiv.symm
  let values := Model.Pcs.Ntt.rowFromEvals (Model.Pcs.Ntt.evals logD) logD (logD - layer - 1)
  have hvalues : values = Spec.Pcs.Ntt.row logD (logD - layer - 1) :=
    rowFromEvals_refines logD (logD - layer - 1)
  have htw (blk : Nat) : Model.Pcs.Ntt.twiddleFromRow values blk =
      Spec.Pcs.Ntt.twiddle logD layer blk := by
    rw [twiddleFromRow_eq, hvalues]
    rfl
  let stepRow (blkRowBase : Nat) (tw : K) (acc : Array Vec8) (rowIdx : Nat) : Array Vec8 :=
    Model.Pcs.Ntt.vecPairLoop ((blkRowBase + rowIdx) * nVecs)
      ((blkRowBase + rowIdx) * nVecs + half * nVecs) tw nVecs 0 acc
  have hrow_conv (blkRowBase : Nat) (tw : K) (acc : Array Vec8) :
      Model.Pcs.Ntt.rowPairLoop blkRowBase half nVecs tw half 0 acc =
        (List.range' 0 half).foldl (stepRow blkRowBase tw) acc := by
    unfold Model.Pcs.Ntt.rowPairLoop
    exact foldRangeLoop_eq_range' (stepRow blkRowBase tw) half 0 acc
  let stepBlock (acc : Array Vec8) (lb : Nat) : Array Vec8 :=
    let tw := Model.Pcs.Ntt.twiddleFromRow values ((coset <<< step) + lb)
    Model.Pcs.Ntt.rowPairLoop (lb * (2 * half)) half nVecs tw half 0 acc
  have hblk_conv :
      Model.Pcs.Ntt.encodeCosetLayerVec8 (Model.Pcs.Ntt.evals logD) buf nVecs logRows logInvRate
        coset step = (List.range' 0 (1 <<< step)).foldl stepBlock buf := by
    unfold Model.Pcs.Ntt.encodeCosetLayerVec8 Model.Pcs.Ntt.cosetBlockLoop
    exact foldRangeLoop_eq_range' stepBlock (1 <<< step) 0 buf
  have hq_div (r k : Nat) (hk : k < nVecs) : (r * nVecs + k) / nVecs = r := by
    rw [Nat.mul_comm, Nat.mul_add_div hnvecs_pos, Nat.div_eq_of_lt hk, Nat.add_zero]
  have hvec_miss (topR botR : Nat) (tw : K) (acc : Array Vec8) (q : Nat)
      (hq : q / nVecs ≠ topR ∧ q / nVecs ≠ botR) :
      (Model.Pcs.Ntt.vecPairLoop (topR * nVecs) (botR * nVecs) tw nVecs 0 acc).getD q default =
        acc.getD q default := by
    refine vecPairLoop_miss _ _ tw nVecs acc q ?_
    intro k hk
    constructor <;> intro heq
    · have hdiv := congrArg (· / nVecs) heq
      rw [hq_div topR k hk] at hdiv
      exact hq.1 hdiv
    · have hdiv := congrArg (· / nVecs) heq
      rw [hq_div botR k hk] at hdiv
      exact hq.2 hdiv
  have hblk_miss (lb : Nat) (acc : Array Vec8) (q : Nat)
      (hq : (q / nVecs) / (2 * half) ≠ lb) :
      (stepBlock acc lb).getD q default = acc.getD q default := by
    dsimp only [stepBlock]
    rw [hrow_conv]
    refine foldl_range'_miss 0 half acc default q _ ?_
    intro cur rowIdx _ hrowIdx
    dsimp only [stepRow]
    have hbot : (lb * (2 * half) + rowIdx) * nVecs + half * nVecs =
        (lb * (2 * half) + rowIdx + half) * nVecs := by
      rw [← Nat.add_mul]
    rw [hbot]
    apply hvec_miss
    constructor <;> intro heq
    · have : (q / nVecs) / (2 * half) = lb := by
        rw [heq, Nat.mul_comm lb, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
      exact hq this
    · have : (q / nVecs) / (2 * half) = lb := by
        have hsum : lb * (2 * half) + rowIdx + half = lb * (2 * half) + (rowIdx + half) := by omega
        rw [heq, hsum, Nat.mul_comm lb, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
      exact hq this
  rw [hblk_conv]
  rw [foldl_range'_hit 0 (1 <<< step) buf default (localRow * nVecs + v) localBlock
    (Nat.zero_le _) (by omega) stepBlock
    (fun acc lb _ _ hne => hblk_miss lb acc _ (by rw [hq_div localRow v hv]; exact hne.symm))]
  let preB := (List.range' 0 (localBlock - 0)).foldl stepBlock buf
  have hpreB_sz : preB.size = buf.size :=
    foldl_range'_size 0 (localBlock - 0) buf stepBlock (fun acc lb => rowPairLoop_size _ _ _ _ _ _ acc)
  have hpreB_same (q : Nat) (hq : (q / nVecs) / (2 * half) = localBlock) :
      preB.getD q default = buf.getD q default :=
    foldl_range'_miss 0 (localBlock - 0) buf default q stepBlock
      (fun acc lb _ hlb => hblk_miss lb acc q (by omega))
  change ((stepBlock preB localBlock).getD (localRow * nVecs + v) default).lane j = _
  dsimp only [stepBlock]
  rw [htw ((coset <<< step) + localBlock), hrow_conv]
  let rIdx := if rem0 < half then rem0 else rem0 - half
  have hrIdx : rIdx < half := by dsimp only [rIdx]; split <;> omega
  have hrow_miss (cur : Array Vec8) (k : Nat) (hk : k < half) (hne : k ≠ rIdx)
      (q : Nat) (hq : q / nVecs = localBlock * (2 * half) + rIdx ∨
        q / nVecs = localBlock * (2 * half) + rIdx + half) :
      (stepRow (localBlock * (2 * half)) t cur k).getD q default = cur.getD q default := by
    dsimp only [stepRow]
    have hbot : (localBlock * (2 * half) + k) * nVecs + half * nVecs =
        (localBlock * (2 * half) + k + half) * nVecs := by
      rw [← Nat.add_mul]
    rw [hbot]
    apply hvec_miss
    rcases hq with hq1 | hq2 <;> constructor <;> omega
  have hqr_cases : (localRow * nVecs + v) / nVecs = localBlock * (2 * half) + rIdx ∨
      (localRow * nVecs + v) / nVecs = localBlock * (2 * half) + rIdx + half := by
    rw [hq_div localRow v hv]
    dsimp only [rIdx]
    split
    · left; omega
    · right; omega
  rw [foldl_range'_hit 0 half preB default (localRow * nVecs + v) rIdx (Nat.zero_le _) (by omega)
    (stepRow (localBlock * (2 * half)) t)
    (fun cur k _ hk hne => hrow_miss cur k (by omega) hne _ hqr_cases)]
  let preR := (List.range' 0 (rIdx - 0)).foldl (stepRow (localBlock * (2 * half)) t) preB
  have hpreR_sz : preR.size = buf.size := by
    dsimp only [preR]
    rw [foldl_range'_size 0 (rIdx - 0) preB _ (fun a _ => vecPairLoop_size _ _ _ _ _ a), hpreB_sz]
  let topR := localBlock * (2 * half) + rIdx
  let botR := topR + half
  have hbotR_lt : botR < 2 ^ logRows := by
    have hstep1 : botR < localBlock * (2 * half) + (2 * half) := by dsimp only [botR, topR]; omega
    have hstep2 : localBlock * (2 * half) + 1 * (2 * half) = (localBlock + 1) * (2 * half) :=
      (Nat.add_mul localBlock 1 (2 * half)).symm
    rw [Nat.one_mul] at hstep2
    calc botR < (localBlock + 1) * (2 * half) := by rw [← hstep2]; exact hstep1
      _ ≤ (1 <<< step) * (2 * half) := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ logRows := hprod
  have htop_preR : preR.getD (topR * nVecs + v) default = buf.getD (topR * nVecs + v) default := by
    have h1 : preR.getD (topR * nVecs + v) default = preB.getD (topR * nVecs + v) default :=
      foldl_range'_miss 0 (rIdx - 0) preB default (topR * nVecs + v) _
        (fun cur k _ hk => hrow_miss cur k (by omega) (by omega) _ (Or.inl (hq_div topR v hv)))
    rw [h1]
    apply hpreB_same
    rw [hq_div topR v hv]
    dsimp only [topR]
    rw [Nat.mul_comm localBlock, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
  have hbot_preR : preR.getD (botR * nVecs + v) default = buf.getD (botR * nVecs + v) default := by
    have h1 : preR.getD (botR * nVecs + v) default = preB.getD (botR * nVecs + v) default :=
      foldl_range'_miss 0 (rIdx - 0) preB default (botR * nVecs + v) _
        (fun cur k _ hk => hrow_miss cur k (by omega) (by omega) _ (Or.inr (hq_div botR v hv)))
    rw [h1]
    apply hpreB_same
    rw [hq_div botR v hv]
    dsimp only [botR, topR]
    have hsum : localBlock * (2 * half) + rIdx + half = localBlock * (2 * half) + (rIdx + half) := by omega
    rw [hsum, Nat.mul_comm localBlock, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
  change ((stepRow (localBlock * (2 * half)) t preR rIdx).getD (localRow * nVecs + v) default).lane j = _
  dsimp only [stepRow]
  have hbot_eq : (localBlock * (2 * half) + rIdx) * nVecs + half * nVecs = botR * nVecs := by
    dsimp only [botR, topR]
    rw [← Nat.add_mul]
  have htop_eq : (localBlock * (2 * half) + rIdx) * nVecs = topR * nVecs := rfl
  rw [hbot_eq, htop_eq]
  have htop_in : topR * nVecs + v < preR.size := by
    rw [hpreR_sz, hsz]
    calc topR * nVecs + v < topR * nVecs + nVecs := by omega
      _ = (topR + 1) * nVecs := by rw [Nat.succ_mul]
      _ ≤ 2 ^ logRows * nVecs := Nat.mul_le_mul_right _ (by omega)
  have hbot_in : botR * nVecs + v < preR.size := by
    rw [hpreR_sz, hsz]
    calc botR * nVecs + v < botR * nVecs + nVecs := by omega
      _ = (botR + 1) * nVecs := by rw [Nat.succ_mul]
      _ ≤ 2 ^ logRows * nVecs := Nat.mul_le_mul_right _ (by omega)
  obtain ⟨hu, hv_out⟩ := vecPairLoop_lane topR botR t nVecs preR v j hv hj hnvecs_pos (by omega)
    htop_in hbot_in
  rw [htop_preR, hbot_preR] at hu hv_out
  split
  · rename_i hlt_rem
    have hr_top : localRow = topR := by
      dsimp only [topR, rIdx]
      rw [if_pos hlt_rem]
      exact hrow_eq
    have hbot_r : botR = localRow + half := by
      dsimp only [botR]
      omega
    rw [hr_top] at *
    rw [hbot_r] at hu
    exact hu
  · rename_i hge_rem
    have hr_bot : botR = localRow := by
      dsimp only [botR, topR, rIdx]
      rw [if_neg hge_rem]
      omega
    have htop_r : topR = localRow - half := by
      have : topR + half = localRow := hr_bot
      omega
    calc ((Model.Pcs.Ntt.vecPairLoop (topR * nVecs) (botR * nVecs) t nVecs 0 preR).getD
            (localRow * nVecs + v) default).lane j
      _ = ((Model.Pcs.Ntt.vecPairLoop (topR * nVecs) (botR * nVecs) t nVecs 0 preR).getD
            (botR * nVecs + v) default).lane j := by rw [hr_bot]
      _ = (Spec.Pcs.Ntt.butterfly ((buf.getD (topR * nVecs + v) default).lane j)
            ((buf.getD (botR * nVecs + v) default).lane j) t).snd := hv_out
      _ = (Spec.Pcs.Ntt.butterfly ((buf.getD ((localRow - half) * nVecs + v) default).lane j)
            ((buf.getD (localRow * nVecs + v) default).lane j) t).snd := by rw [htop_r, hr_bot]

private theorem subtreeRoot_congr (f g : Nat → Model.Merkle.Digest32) (k base : Nat)
    (h : ∀ i < 2 ^ k, f (base + i) = g (base + i)) :
    subtreeRoot f k base = subtreeRoot g k base := by
  induction k generalizing base with
  | zero => simpa [subtreeRoot_zero] using h 0 (by decide)
  | succ k ih =>
    simp only [subtreeRoot_succ, Nat.shiftLeft_eq, Nat.one_mul]
    rw [ih base (fun i hi => h i (by omega))]
    rw [ih (base + 2 ^ k) (fun i hi => by
      have heq : base + 2 ^ k + i = base + (2 ^ k + i) := by omega
      rw [heq]
      exact h (2 ^ k + i) (by omega))]

private theorem range'_succ_right (s n : Nat) :
    List.range' s (n + 1) = List.range' s n ++ [s + n] := by
  induction n generalizing s with
  | zero =>
    rw [Nat.add_zero]
    rfl
  | succ n ih =>
    rw [List.range'_succ, ih (s + 1), List.range'_succ, List.cons_append]
    have heq : s + 1 + n = s + (n + 1) := by omega
    rw [heq]

private theorem cosetStepLoop_succ_right (table : Array K)
    (nVecs logRows logInvRate coset rem s : Nat) (data : Array Vec8) :
    Model.Pcs.Ntt.cosetStepLoop table nVecs logRows logInvRate coset (rem + 1) s data =
      Model.Pcs.Ntt.encodeCosetLayerVec8 table
        (Model.Pcs.Ntt.cosetStepLoop table nVecs logRows logInvRate coset rem s data)
        nVecs logRows logInvRate coset (s + rem) := by
  unfold Model.Pcs.Ntt.cosetStepLoop
  induction rem generalizing s data with
  | zero =>
    rw [foldRangeLoop_succ, foldRangeLoop_zero, foldRangeLoop_zero, Nat.add_zero]
  | succ rem ih =>
    rw [foldRangeLoop_succ, ih (s + 1), foldRangeLoop_succ]
    have heq : s + 1 + rem = s + (rem + 1) := by omega
    rw [heq]

theorem encode_size (data : Array K) (lanes startLayer : Nat) :
    (Spec.Pcs.Ntt.encode data lanes startLayer).size = data.size := by
  unfold Spec.Pcs.Ntt.encode
  dsimp only
  rw [← Array.foldl_toList, array_range_toList]
  exact foldl_range'_size 0 _ data _ (fun a _ => encodeLayer_size a lanes _ _)

theorem encodeMessage_size (message : Array K) (lanes logRows logInvRate : Nat) :
    (Spec.Pcs.Commit.encodeMessage message lanes logRows logInvRate).size =
      2 ^ (logRows + logInvRate) * Spec.Pcs.Commit.rowWords lanes := by
  unfold Spec.Pcs.Commit.encodeMessage
  dsimp only
  rw [encode_size, replicate_size, transpose_size]
  simp only [Nat.shiftLeft_eq]
  simp only [Nat.one_mul]
  rw [Nat.mul_comm (Spec.Pcs.Commit.rowWords lanes) (2 ^ logRows), ← Nat.mul_assoc,
    ← Nat.pow_add, Nat.add_comm]

private theorem cosetStep_lane (message : Array K) (lanes width nVecs logRows logInvRate step coset
    r v j : Nat) (hwidth : width = 8 * nVecs) (hlanes : lanes ≤ width) (hnvecs_pos : 0 < nVecs)
    (hstep : step ≤ logRows) (hcoset : coset < 2 ^ logInvRate) (hr : r < 2 ^ logRows)
    (hv : v < nVecs) (hj : j < 8) :
    let logD := logRows + logInvRate
    let first := Spec.Pcs.Commit.transpose message lanes width logRows
    let data := (List.range' 0 step).foldl
      (fun acc s => Spec.Pcs.Ntt.encodeLayer acc width (logInvRate + s) logD)
      (Spec.Pcs.Commit.replicate first (1 <<< logInvRate))
    let buf := Model.Pcs.Ntt.cosetStepLoop (Model.Pcs.Ntt.evals logD) nVecs logRows logInvRate coset
      step 0 (Model.Pcs.Commit.firstCosetVec8 message lanes nVecs logRows)
    ((buf.getD (r * nVecs + v) default).lane j) =
      data.getD (((coset * 2 ^ logRows + r) * width) + (8 * v + j)) 0 := by
  intro logD first data buf
  induction step generalizing r v j with
  | zero =>
    dsimp only [data, buf]
    change ((Model.Pcs.Commit.firstCosetVec8 message lanes nVecs logRows).getD
        (r * nVecs + v) default).lane j =
      (Spec.Pcs.Commit.replicate first (1 <<< logInvRate)).getD
        (((coset * 2 ^ logRows + r) * width) + (8 * v + j)) 0
    have hfirst_sz : first.size = width * (1 <<< logRows) := transpose_size message lanes width logRows
    have hpow_rows : 1 <<< logRows = 2 ^ logRows := by
      simp only [Nat.shiftLeft_eq]
      simp only [Nat.one_mul]
    have hoff : r * width + (8 * v + j) < first.size := by
      rw [hfirst_sz, hpow_rows, Nat.mul_comm width]
      calc r * width + (8 * v + j) < r * width + width := by rw [hwidth]; omega
        _ = (r + 1) * width := by rw [Nat.succ_mul]
        _ ≤ 2 ^ logRows * width := Nat.mul_le_mul_right _ (by omega)
    have hlanes8 : lanes ≤ 8 * nVecs := by rw [← hwidth]; exact hlanes
    have hr' : r < 1 <<< logRows := by rw [hpow_rows]; exact hr
    rw [firstCosetVec8_lane_eq_transpose message lanes nVecs logRows r v j hlanes8 hr' hv hj]
    rw [← hwidth]
    have hrep : (coset * 2 ^ logRows + r) * width + (8 * v + j) =
        coset * first.size + (r * width + (8 * v + j)) := by
      rw [hfirst_sz, hpow_rows, Nat.mul_comm width (2 ^ logRows), ← Nat.mul_assoc, Nat.add_mul]
      omega
    have hcoset' : coset < 1 <<< logInvRate := by
      simp only [Nat.shiftLeft_eq]
      simp only [Nat.one_mul]
      exact hcoset
    change first.getD (r * width + (8 * v + j)) 0 = _
    rw [hrep, replicate_getD first (1 <<< logInvRate) coset (r * width + (8 * v + j)) hcoset' hoff]
  | succ step ih =>
    have hstep' : step < logRows := by omega
    dsimp only [data, buf]
    rw [range'_succ_right 0 step, List.foldl_append, List.foldl_cons, List.foldl_nil,
      cosetStepLoop_succ_right, Nat.zero_add]
    let prevData := (List.range' 0 step).foldl
      (fun acc s => Spec.Pcs.Ntt.encodeLayer acc width (logInvRate + s) logD)
      (Spec.Pcs.Commit.replicate first (1 <<< logInvRate))
    let prevBuf := Model.Pcs.Ntt.cosetStepLoop (Model.Pcs.Ntt.evals logD) nVecs logRows logInvRate
      coset step 0 (Model.Pcs.Commit.firstCosetVec8 message lanes nVecs logRows)
    have hprev (r' v' j' : Nat) (hr' : r' < 2 ^ logRows) (hv' : v' < nVecs) (hj' : j' < 8) :
        ((prevBuf.getD (r' * nVecs + v') default).lane j') =
          prevData.getD (((coset * 2 ^ logRows + r') * width) + (8 * v' + j')) 0 :=
      ih r' v' j' (by omega) hr' hv' hj'
    have hprev_sz : prevBuf.size = 2 ^ logRows * nVecs := by
      dsimp only [prevBuf]
      rw [cosetStepLoop_size, firstCosetVec8_size]
      simp only [Nat.shiftLeft_eq]
      simp only [Nat.one_mul]
    have hdata_sz : prevData.size = 2 ^ logD * width := by
      dsimp only [prevData]
      rw [foldl_range'_size 0 step _ _ (fun a s => encodeLayer_size a width _ _)]
      rw [replicate_size]
      have hfsz : first.size = width * (1 <<< logRows) := transpose_size message lanes width logRows
      rw [hfsz]
      simp only [Nat.shiftLeft_eq]
      simp only [Nat.one_mul]
      rw [Nat.mul_comm width (2 ^ logRows), ← Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm]
    let half := 1 <<< (logRows - step - 1)
    have hhalf_eq : half = 2 ^ (logRows - step - 1) := by
      dsimp only [half]
      simp only [Nat.shiftLeft_eq]
      simp only [Nat.one_mul]
    have hhalf_pos : 0 < half := by rw [hhalf_eq]; exact Nat.two_pow_pos _
    have hhalf_layer : 1 <<< (logD - (logInvRate + step) - 1) = half := by
      dsimp only [half]
      congr 1
      omega
    have hprod : 2 ^ step * (2 * half) = 2 ^ logRows := by
      rw [hhalf_eq]
      exact pow2_split logRows step hstep'
    have hbase : coset * 2 ^ logRows = (2 * half) * (coset * 2 ^ step) := by
      rw [← hprod]
      calc coset * (2 ^ step * (2 * half))
        _ = (coset * 2 ^ step) * (2 * half) := (Nat.mul_assoc _ _ _).symm
        _ = (2 * half) * (coset * 2 ^ step) := Nat.mul_comm _ _
    have hrow_mod : (coset * 2 ^ logRows + r) % (2 * half) = r % (2 * half) := by
      rw [hbase, Nat.mul_add_mod]
    have hrow_div : (coset * 2 ^ logRows + r) / (2 * half) = coset * 2 ^ step + r / (2 * half) := by
      rw [hbase, Nat.mul_add_div (by omega)]
    have hsh_coset : coset <<< step = coset * 2 ^ step := by
      simp only [Nat.shiftLeft_eq]
    change ((Model.Pcs.Ntt.encodeCosetLayerVec8 (Model.Pcs.Ntt.evals logD) prevBuf nVecs logRows
        logInvRate coset step).getD (r * nVecs + v) default).lane j =
      (Spec.Pcs.Ntt.encodeLayer prevData width (logInvRate + step) logD).getD
        (((coset * 2 ^ logRows + r) * width) + (8 * v + j)) 0
    rw [encodeCosetLayerVec8_lane prevBuf nVecs logRows logInvRate coset step r v j hstep'
      hnvecs_pos hprev_sz hr hv hj]
    rw [encodeLayer_getD prevData width (logInvRate + step) logD (coset * 2 ^ logRows + r)
      (8 * v + j) (by omega) hdata_sz (by
        calc coset * 2 ^ logRows + r < coset * 2 ^ logRows + 2 ^ logRows := by omega
          _ = (coset + 1) * 2 ^ logRows := by rw [Nat.succ_mul]
          _ ≤ 2 ^ logInvRate * 2 ^ logRows := Nat.mul_le_mul_right _ hcoset
          _ = 2 ^ logD := by rw [← Nat.pow_add, Nat.add_comm]) (by rw [hwidth]; omega)]
    rw [hhalf_layer, hrow_mod, hrow_div, hsh_coset]
    change (if r % (2 * half) < half then _ else _) = (if r % (2 * half) < half then _ else _)
    split
    · rename_i hlt
      have hr_div_lt : r / (2 * half) < 2 ^ step := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        calc r < 2 ^ logRows := hr
          _ = 2 ^ step * (2 * half) := hprod.symm
      have hr2 : r + half < 2 ^ logRows := by
        have hdiv := Nat.div_add_mod r (2 * half)
        have hstep1 : r + half < (2 * half) * (r / (2 * half)) + 2 * half := by omega
        have hstep2 : (2 * half) * (r / (2 * half)) + 2 * half =
            (r / (2 * half) + 1) * (2 * half) := by
          rw [Nat.mul_comm (2 * half), Nat.add_mul, Nat.one_mul]
        calc r + half < (r / (2 * half) + 1) * (2 * half) := by rw [← hstep2]; exact hstep1
          _ ≤ 2 ^ step * (2 * half) := Nat.mul_le_mul_right _ (by omega)
          _ = 2 ^ logRows := hprod
      rw [hprev r v j hr hv hj, hprev (r + half) v j hr2 hv hj]
      have hadd_row : coset * 2 ^ logRows + r + half = coset * 2 ^ logRows + (r + half) := by omega
      rw [hadd_row]
    · rename_i hge
      have hr2 : r - half < 2 ^ logRows := by omega
      have hge' : half ≤ r := by
        have hmod : r % (2 * half) ≤ r := Nat.mod_le _ _
        omega
      rw [hprev (r - half) v j hr2 hv hj, hprev r v j hr hv hj]
      have hsub_row : coset * 2 ^ logRows + r - half = coset * 2 ^ logRows + (r - half) := by omega
      rw [hsub_row]

theorem encodeCosetVec8_lane (message : Array K) (lanes nVecs logRows logInvRate coset r v j : Nat)
    (hwidth : Spec.Pcs.Commit.rowWords lanes = 8 * nVecs)
    (hlanes : lanes ≤ Spec.Pcs.Commit.rowWords lanes) (hnvecs_pos : 0 < nVecs)
    (hcoset : coset < 2 ^ logInvRate) (hr : r < 2 ^ logRows) (hv : v < nVecs) (hj : j < 8) :
    ((Model.Pcs.Ntt.encodeCosetVec8 (Model.Pcs.Ntt.evals (logRows + logInvRate))
        (Model.Pcs.Commit.firstCosetVec8 message lanes nVecs logRows) nVecs logRows logInvRate
        coset).getD (r * nVecs + v) default).lane j =
      (Spec.Pcs.Commit.encodeMessage message lanes logRows logInvRate).getD
        (((coset * 2 ^ logRows + r) * Spec.Pcs.Commit.rowWords lanes) + (8 * v + j)) 0 := by
  let width := Spec.Pcs.Commit.rowWords lanes
  have hw_pos : 0 < width := by
    change 0 < Spec.Pcs.Commit.rowWords lanes
    rw [hwidth]
    omega
  have hlog : (Spec.Pcs.Commit.replicate (Spec.Pcs.Commit.transpose message lanes width logRows)
      (1 <<< logInvRate)).size / width = 2 ^ (logRows + logInvRate) := by
    rw [replicate_size, transpose_size]
    simp only [Nat.shiftLeft_eq]
    simp only [Nat.one_mul]
    rw [Nat.mul_comm width (2 ^ logRows), ← Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm,
      Nat.mul_div_cancel _ hw_pos]
  have henc : Spec.Pcs.Ntt.encode
      (Spec.Pcs.Commit.replicate (Spec.Pcs.Commit.transpose message lanes width logRows)
        (1 <<< logInvRate)) width logInvRate =
      (List.range' 0 logRows).foldl
        (fun acc s => Spec.Pcs.Ntt.encodeLayer acc width (logInvRate + s) (logRows + logInvRate))
        (Spec.Pcs.Commit.replicate (Spec.Pcs.Commit.transpose message lanes width logRows)
          (1 <<< logInvRate)) := by
    unfold Spec.Pcs.Ntt.encode
    rw [hlog, log2_pow]
    dsimp only
    rw [Nat.add_sub_cancel, ← Array.foldl_toList, array_range_toList]
  unfold Spec.Pcs.Commit.encodeMessage Model.Pcs.Ntt.encodeCosetVec8
  dsimp only
  change _ = (Spec.Pcs.Ntt.encode
      (Spec.Pcs.Commit.replicate (Spec.Pcs.Commit.transpose message lanes width logRows)
        (1 <<< logInvRate)) width logInvRate).getD
      (((coset * 2 ^ logRows + r) * width) + (8 * v + j)) 0
  rw [henc]
  exact cosetStep_lane message lanes width nVecs logRows logInvRate logRows coset r v j
    hwidth hlanes hnvecs_pos (Nat.le_refl _) hcoset hr hv hj

private theorem cosetRootsLoop_eq (table : Array K) (first : Array Vec8)
    (st1 st2 st3 : Model.Keccak.State25) (nVecs logRows logInvRate rem base : Nat)
    (acc : Array Model.Merkle.Digest32) :
    Model.Pcs.Commit.cosetRootsLoop table first st1 st2 st3 nVecs logRows logInvRate rem base acc =
      acc ++ ((List.range' base rem).map (fun c =>
        Model.Pcs.Commit.subtreeRootBuf st1 st2 st3
          (Model.Pcs.Ntt.encodeCosetVec8 table first nVecs logRows logInvRate c)
          nVecs logRows 0)).toArray := by
  unfold Model.Pcs.Commit.cosetRootsLoop
  induction rem generalizing base acc with
  | zero => simp [foldRangeLoop_zero]
  | succ rem ih =>
    rw [foldRangeLoop_succ, ih (base + 1), List.range'_succ, List.map_cons]
    apply Array.toList_inj.mp
    simp [Array.toList_append, Array.toList_push, List.append_assoc]

private theorem array_getElem?_toList {α : Type} (xs : Array α) (i : Nat) :
    xs[i]? = xs.toList[i]? := by
  by_cases hi : i < xs.size
  · have hiL : i < xs.toList.length := by
      rw [Array.length_toList]
      exact hi
    rw [Array.getElem?_eq_getElem hi, List.getElem?_eq_getElem hiL, Array.getElem_toList]
  · have hiL : xs.toList.length ≤ i := by
      rw [Array.length_toList]
      omega
    rw [Array.getElem?_eq_none (by omega), List.getElem?_eq_none hiL]

private theorem array_getD_extract {α : Type} (xs : Array α) (lo hi i : Nat) (d : α)
    (h : lo + i < hi) :
    (xs.extract lo hi).getD i d = xs.getD (lo + i) d := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    array_getElem?_toList, array_getElem?_toList, array_extract_toList]
  by_cases hlt : lo + i < xs.size
  · have hi_lt : i < min hi xs.size - lo := by omega
    rw [List.getElem?_take_of_lt hi_lt, List.getElem?_drop]
  · have hge_lo : xs.toList.length ≤ lo + i := by
      rw [Array.length_toList]
      omega
    have hlen : ((xs.toList.drop lo).take (min hi xs.size - lo)).length ≤ i := by
      rw [List.length_take]
      omega
    rw [List.getElem?_eq_none hlen, List.getElem?_eq_none hge_lo]

private theorem cosetRoots_getD (message : Array K) (lanes nVecs logRows logInvRate : Nat)
    (hwidth : Spec.Pcs.Commit.rowWords lanes = 8 * nVecs)
    (hlanes : lanes ≤ Spec.Pcs.Commit.rowWords lanes) (hnlo : 1 ≤ nVecs) (hnhi : nVecs ≤ 8)
    (c : Nat) (hc : c < 2 ^ logInvRate) :
    (Model.Pcs.Commit.cosetRootsLoop (Model.Pcs.Ntt.evals (logRows + logInvRate))
      (Model.Pcs.Commit.firstCosetVec8 message lanes nVecs logRows)
      (Model.Pcs.Commit.zeroPrefixState 1) (Model.Pcs.Commit.zeroPrefixState 2)
      (Model.Pcs.Commit.zeroPrefixState 3) nVecs logRows logInvRate (1 <<< logInvRate) 0 #[]
      ).getD c default =
      subtreeRoot (fun i =>
        (Model.Pcs.Commit.leafDigests
          (Spec.Pcs.Commit.encodeMessage message lanes logRows logInvRate)
          (Spec.Pcs.Commit.rowWords lanes)).getD i default) logRows (c * (1 <<< logRows)) := by
  let width := Spec.Pcs.Commit.rowWords lanes
  let codeword := Spec.Pcs.Commit.encodeMessage message lanes logRows logInvRate
  let leaves := Model.Pcs.Commit.leafDigests codeword width
  have hrate : 1 <<< logInvRate = 2 ^ logInvRate := by
    simp only [Nat.shiftLeft_eq]
    simp only [Nat.one_mul]
  rw [cosetRootsLoop_eq, Array.empty_append]
  have hc_lt : c < ((List.range' 0 (1 <<< logInvRate)).map (fun c0 =>
      Model.Pcs.Commit.subtreeRootBuf (Model.Pcs.Commit.zeroPrefixState 1)
        (Model.Pcs.Commit.zeroPrefixState 2) (Model.Pcs.Commit.zeroPrefixState 3)
        (Model.Pcs.Ntt.encodeCosetVec8 (Model.Pcs.Ntt.evals (logRows + logInvRate))
          (Model.Pcs.Commit.firstCosetVec8 message lanes nVecs logRows) nVecs logRows logInvRate c0)
        nVecs logRows 0)).toArray.size := by
    simp [hrate, hc]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hc_lt, Option.getD_some]
  simp only [List.getElem_toArray, List.getElem_map, List.getElem_range', Nat.zero_add, Nat.one_mul]
  let encoded := Model.Pcs.Ntt.encodeCosetVec8 (Model.Pcs.Ntt.evals (logRows + logInvRate))
    (Model.Pcs.Commit.firstCosetVec8 message lanes nVecs logRows) nVecs logRows logInvRate c
  have hszc : codeword.size = 2 ^ (logRows + logInvRate) * width :=
    encodeMessage_size message lanes logRows logInvRate
  have hleaf : ∀ row < 2 ^ logRows,
      Model.Pcs.Commit.hashLeafVec8From (Model.Pcs.Commit.zeroPrefixState 1)
        (Model.Pcs.Commit.zeroPrefixState 2) (Model.Pcs.Commit.zeroPrefixState 3)
        encoded nVecs row =
        leaves.getD (c * 2 ^ logRows + row) default := by
    intro row hrow
    have hpos_lt : c * 2 ^ logRows + row < 2 ^ (logRows + logInvRate) := by
      calc c * 2 ^ logRows + row < c * 2 ^ logRows + 2 ^ logRows := by omega
        _ = (c + 1) * 2 ^ logRows := by rw [Nat.succ_mul]
        _ ≤ 2 ^ logInvRate * 2 ^ logRows := Nat.mul_le_mul_right _ hc
        _ = 2 ^ (logRows + logInvRate) := by rw [← Nat.pow_add, Nat.add_comm]
    let rowK := codeword.extract ((c * 2 ^ logRows + row) * width)
      (((c * 2 ^ logRows + row) + 1) * width)
    have hrowK : rowK.size = width := by
      dsimp only [rowK]
      rw [Array.size_extract]
      have hhi : ((c * 2 ^ logRows + row) + 1) * width ≤ codeword.size := by
        rw [hszc]
        exact Nat.mul_le_mul_right _ hpos_lt
      have hsub : ((c * 2 ^ logRows + row) + 1) * width - (c * 2 ^ logRows + row) * width = width := by
        rw [Nat.succ_mul]
        omega
      omega
    rw [hashLeafVec8From_eq_leafDigest encoded rowK nVecs row hnlo hnhi
      (by rw [hrowK]; exact hwidth) (fun vv hvv jj hjj => by
        rw [encodeCosetVec8_lane message lanes nVecs logRows logInvRate c row vv jj
          hwidth hlanes (by omega) hc hrow hvv hjj]
        have hlt_ext : 8 * vv + jj < width := by
          change 8 * vv + jj < Spec.Pcs.Commit.rowWords lanes
          rw [hwidth]
          omega
        have hex : (c * 2 ^ logRows + row) * width + (8 * vv + jj) <
            ((c * 2 ^ logRows + row) + 1) * width := by
          simp only [Nat.add_mul, Nat.one_mul]
          omega
        exact (array_getD_extract codeword ((c * 2 ^ logRows + row) * width)
          (((c * 2 ^ logRows + row) + 1) * width) (8 * vv + jj) 0 hex).symm)]
    dsimp only [leaves]
    unfold Model.Pcs.Commit.leafDigests
    have hdiv_sz : codeword.size / width = 2 ^ (logRows + logInvRate) := by
      rw [hszc, Nat.mul_div_cancel _ (by change 0 < Spec.Pcs.Commit.rowWords lanes; rw [hwidth]; omega)]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, array_getElem?_range]
    simp only [hdiv_sz, hpos_lt, ↓reduceIte, Option.map_some, Option.getD_some, rowK, width]
  have hsh_rows : 1 <<< logRows = 2 ^ logRows := by
    simp only [Nat.shiftLeft_eq]
    simp only [Nat.one_mul]
  have hsub := subtreeRootBuf_eq_subtreeRoot (Model.Pcs.Commit.zeroPrefixState 1)
    (Model.Pcs.Commit.zeroPrefixState 2) (Model.Pcs.Commit.zeroPrefixState 3)
    encoded nVecs (fun i => leaves.getD (c * 2 ^ logRows + i) default) logRows 0
    (fun i hi => by
      rw [Nat.zero_add]
      exact hleaf i hi)
  change Model.Pcs.Commit.subtreeRootBuf _ _ _ encoded nVecs logRows 0 =
    subtreeRoot (fun i => leaves.getD i default) logRows (c * (1 <<< logRows))
  rw [hsub, hsh_rows]
  have hshift := subtreeRoot_shift (fun i => leaves.getD i default) logRows (c * 2 ^ logRows) 0
  rw [Nat.add_zero] at hshift
  exact hshift.symm

theorem commitRootFast_eq_spec (message : Array K) (lanes logRows logInvRate : Nat)
    (hlo : 1 ≤ lanes) (hhi : lanes ≤ 64) :
    Model.Pcs.Commit.commitRootFast message lanes logRows logInvRate =
      Spec.Pcs.Commit.root message lanes logRows logInvRate := by
  let width := Spec.Pcs.Commit.rowWords lanes
  let nVecs := width / 8
  have hn := nVecs_bounds lanes hlo hhi
  have hwidth8 : width = 8 * nVecs := rowWords_mul8 lanes hlo hhi
  have hlanes : lanes ≤ width := by
    change lanes ≤ Spec.Pcs.Commit.rowWords lanes
    rw [rowWords_of_lanes lanes hlo hhi]
    omega
  unfold Model.Pcs.Commit.commitRootFast Model.Pcs.Commit.rowWords
  dsimp only
  let codeword := Spec.Pcs.Commit.encodeMessage message lanes logRows logInvRate
  let leaves := Model.Pcs.Commit.leafDigests codeword width
  have hszc : codeword.size = 2 ^ (logRows + logInvRate) * width :=
    encodeMessage_size message lanes logRows logInvRate
  have hw_pos : 0 < width := by rw [hwidth8]; omega
  have hleaves : leaves.size = 2 ^ (logRows + logInvRate) := by
    dsimp only [leaves]
    unfold Model.Pcs.Commit.leafDigests
    rw [Array.size_map, Array.size_range, hszc, Nat.mul_div_cancel _ hw_pos]
  have hmap : leaves.map digest32ToSpec = Spec.Pcs.Commit.leaves codeword width := by
    dsimp only [leaves]
    unfold Model.Pcs.Commit.leafDigests Spec.Pcs.Commit.leaves
    apply Array.ext
    · simp
    · intro i hi _
      simp only [Array.getElem_map, array_getElem_range]
      have hi_lt : i < 2 ^ (logRows + logInvRate) := by
        simp only [Array.size_map, Array.size_range, hszc, Nat.mul_div_cancel _ hw_pos] at hi
        exact hi
      have hrow : (codeword.extract (i * width) ((i + 1) * width)).size = width := by
        rw [Array.size_extract]
        have hhi_i : (i + 1) * width ≤ codeword.size := by
          rw [hszc]
          exact Nat.mul_le_mul_right _ hi_lt
        have hsub : (i + 1) * width - i * width = width := by
          rw [Nat.succ_mul]
          omega
        omega
      rw [leafDigest_toSpec _ (by rw [hrow, hwidth8]; omega)]
      rfl
  have hroots := cosetRoots_getD message lanes nVecs logRows logInvRate hwidth8 hlanes hn.1 hn.2
  have hsub : subtreeRoot (fun i =>
      (Model.Pcs.Commit.cosetRootsLoop (Model.Pcs.Ntt.evals (logRows + logInvRate))
        (Model.Pcs.Commit.firstCosetVec8 message lanes nVecs logRows)
        (Model.Pcs.Commit.zeroPrefixState 1) (Model.Pcs.Commit.zeroPrefixState 2)
        (Model.Pcs.Commit.zeroPrefixState 3) nVecs logRows logInvRate (1 <<< logInvRate) 0 #[]
        ).getD i default) logInvRate 0 =
      subtreeRoot (fun i => leaves.getD i default) (logRows + logInvRate) 0 := by
    rw [subtreeRoot_congr _ (fun c => subtreeRoot (fun k => leaves.getD k default) logRows
        (0 + c * (1 <<< logRows))) logInvRate 0 (fun i hi => by
          simp only [Nat.zero_add]
          exact hroots i hi)]
    exact (subtreeRoot_add (fun k => leaves.getD k default) logRows logInvRate 0).symm
  change (subtreeRoot (fun i =>
      (Model.Pcs.Commit.cosetRootsLoop (Model.Pcs.Ntt.evals (logRows + logInvRate))
        (Model.Pcs.Commit.firstCosetVec8 message lanes nVecs logRows)
        (Model.Pcs.Commit.zeroPrefixState 1) (Model.Pcs.Commit.zeroPrefixState 2)
        (Model.Pcs.Commit.zeroPrefixState 3) nVecs logRows logInvRate (1 <<< logInvRate) 0 #[]
        ).getD i default) logInvRate 0).toBytes = _
  rw [hsub, subtreeRoot_eq_treeRoot leaves (logRows + logInvRate) hleaves, hmap]
  rfl

theorem rootBytes_refines_spec (message : Array K) (lanes logRows logInvRate : Nat) :
    Model.Pcs.Commit.rootBytes message lanes logRows logInvRate =
      Spec.Pcs.Commit.root message lanes logRows logInvRate := by
  unfold Model.Pcs.Commit.rootBytes
  split
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact commitRootFast_eq_spec message lanes logRows logInvRate h.1 h.2
  · rfl

end LeanVmXmss.Proofs.Pcs
