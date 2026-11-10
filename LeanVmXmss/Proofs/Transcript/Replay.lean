import Spec.Transcript.Replay
import Proofs.Merkle.Contracts

namespace LeanVmXmss.Proofs.Transcript.Replay

open Spec.Transcript

theorem nextRaw_consumes_one (s t : VerifierState) (x : Spec.Field.E)
    (h : nextRaw s = some (x, t)) : t.scalarOffset = s.scalarOffset + 1 := by
  unfold nextRaw at h
  cases he : s.proof.scalars[s.scalarOffset]? with
  | none => simp [he] at h
  | some value =>
    simp [he] at h
    rcases h with ⟨rfl, rfl⟩
    rfl

theorem nextScalar_binds (s t : VerifierState) (x : Spec.Field.E)
    (h : nextScalar s = some (x, t)) :
    t.scalarOffset = s.scalarOffset + 1 ∧ t.sponge = observe s.sponge x := by
  unfold nextScalar at h
  cases hr : nextRaw s with
  | none => simp [hr] at h
  | some p =>
    rcases p with ⟨value, next⟩
    simp [hr] at h
    rcases h with ⟨rfl, rfl⟩
    constructor
    · exact nextRaw_consumes_one s next value hr
    · unfold nextRaw at hr
      cases he : s.proof.scalars[s.scalarOffset]? with
      | none => simp [he] at hr
      | some value =>
        simp [he] at hr
        rcases hr with ⟨rfl, rfl⟩
        rfl

theorem finish_exact (s : VerifierState) :
    (finish s).isSome = true ↔
      s.scalarOffset = s.proof.scalars.size ∧ s.openingOffset = s.proof.openings.size := by
  unfold finish
  split <;> simp_all

theorem appended_scalar_replays (before after : Array Spec.Field.E) (x : Spec.Field.E)
    (sponge : Sponge) (openings : Array Spec.Merkle.PrunedMerklePaths)
    (openingOffset : Nat) (paths : Array Spec.Merkle.MerklePath) :
    let state : VerifierState :=
      ⟨⟨before ++ #[x] ++ after, openings⟩, sponge, before.size, openingOffset, paths⟩
    nextScalar state = some (x, {state with
      scalarOffset := before.size + 1, sponge := observe sponge x}) := by
  dsimp only
  unfold nextScalar nextRaw
  have lookup : (before ++ #[x] ++ after)[before.size]? = some x := by
    rw [Array.getElem?_append_left (by simp only [Array.size_append, Array.size_singleton]; omega)]
    rw [Array.getElem?_append_right (by omega)]
    simp only [Nat.sub_self]
    rfl
  rw [lookup]
  rfl

theorem prover_scalar_verifier_refinement (prover : ProverState) (x : Spec.Field.E)
    (after : Array Spec.Field.E) (openings : Array Spec.Merkle.PrunedMerklePaths)
    (openingOffset : Nat) (paths : Array Spec.Merkle.MerklePath) :
    let sent := addScalar prover x
    let verifier : VerifierState :=
      ⟨⟨sent.stream ++ after, openings⟩, prover.sponge, prover.stream.size, openingOffset, paths⟩
    nextScalar verifier = some (x, {verifier with
      scalarOffset := sent.stream.size, sponge := sent.sponge}) := by
  dsimp only [addScalar]
  have appended := appended_scalar_replays prover.stream after x prover.sponge openings openingOffset paths
  simpa only [Array.push_eq_append, Array.size_append, Array.size_singleton] using appended

theorem appended_scalars_replay (before xs after : Array Spec.Field.E)
    (sponge : Sponge) (openings : Array Spec.Merkle.PrunedMerklePaths)
    (openingOffset : Nat) (paths : Array Spec.Merkle.MerklePath) :
    let state : VerifierState :=
      ⟨⟨before ++ xs ++ after, openings⟩, sponge, before.size, openingOffset, paths⟩
    nextScalars xs.size state = some (xs, {state with
      scalarOffset := before.size + xs.size, sponge := xs.foldl observe sponge}) := by
  rw [← Array.toArray_toList (xs := xs)]
  generalize xs.toList = values
  induction values generalizing before sponge with
  | nil => simpa using
      (show nextScalars 0
        (⟨⟨before ++ after, openings⟩, sponge, before.size, openingOffset, paths⟩ : VerifierState) =
        some (#[], ⟨⟨before ++ after, openings⟩, sponge, before.size, openingOffset, paths⟩) from rfl)
  | cons x tail ih =>
    rw [List.toArray_cons]
    have length : (#[x] ++ tail.toArray).size = tail.length + 1 := by simp
    rw [length]
    change (do
      let (value, middle) ← nextScalar _
      let (values, last) ← nextScalars tail.length middle
      some (#[value] ++ values, last)) = _
    have first := appended_scalar_replays before (tail.toArray ++ after) x sponge
      openings openingOffset paths
    simp only [Array.append_assoc] at first ⊢
    rw [first]
    simp only [Bind.bind, Option.bind]
    have rest := ih (before ++ #[x]) (observe sponge x)
    simp only [Array.size_append, Array.append_assoc, List.size_toArray,
      List.length_cons, List.length_nil, Nat.zero_add] at rest
    rw [rest]
    simp [Nat.add_comm, Nat.add_left_comm]

theorem addScalars_state (prover : ProverState) (xs : Array Spec.Field.E) :
    addScalars prover xs =
      {prover with stream := prover.stream ++ xs, sponge := xs.foldl observe prover.sponge} := by
  rw [← Array.toArray_toList (xs := xs)]
  generalize xs.toList = values
  induction values generalizing prover with
  | nil => simp [addScalars]
  | cons x tail ih =>
    have step : addScalars prover (x :: tail).toArray =
        addScalars (addScalar prover x) tail.toArray := by
      simp [addScalars]
    rw [step, ih]
    have observed : (x :: tail).toArray.foldl observe prover.sponge =
        tail.toArray.foldl observe (observe prover.sponge x) := by simp
    rw [observed, List.toArray_cons]
    simp only [addScalar, Array.push_eq_append, Array.append_assoc]

theorem prover_scalars_verifier_refinement (prover : ProverState) (xs after : Array Spec.Field.E)
    (openings : Array Spec.Merkle.PrunedMerklePaths) (openingOffset : Nat)
    (paths : Array Spec.Merkle.MerklePath) :
    let sent := addScalars prover xs
    let verifier : VerifierState :=
      ⟨⟨sent.stream ++ after, openings⟩, prover.sponge, prover.stream.size, openingOffset, paths⟩
    nextScalars xs.size verifier = some (xs, {verifier with
      scalarOffset := sent.stream.size, sponge := sent.sponge}) := by
  dsimp only
  rw [addScalars_state]
  simpa only [Array.size_append] using
    appended_scalars_replay prover.stream xs after prover.sponge openings openingOffset paths

theorem prover_scalars_finish_refinement (prover : ProverState)
    (xs : Array Spec.Field.E) (openings : Array Spec.Merkle.PrunedMerklePaths)
    (paths : Array Spec.Merkle.MerklePath) :
    let sent := addScalars prover xs
    let verifier : VerifierState :=
      ⟨⟨sent.stream, openings⟩, prover.sponge, prover.stream.size, openings.size, paths⟩
    ∃ replayed,
      nextScalars xs.size verifier = some (xs, replayed) ∧
      replayed.sponge = sent.sponge ∧ finish replayed = some paths := by
  dsimp only
  have replay := prover_scalars_verifier_refinement prover xs #[] openings openings.size paths
  simp only [Array.append_empty] at replay
  refine ⟨_, replay, rfl, ?_⟩
  simp only [finish, and_self, ite_true]

theorem prover_scalars_challenge_refinement (prover : ProverState)
    (xs after : Array Spec.Field.E) (openings : Array Spec.Merkle.PrunedMerklePaths)
    (openingOffset : Nat) (paths : Array Spec.Merkle.MerklePath) :
    let sent := addScalars prover xs
    let verifier : VerifierState :=
      ⟨⟨sent.stream ++ after, openings⟩, prover.sponge, prover.stream.size, openingOffset, paths⟩
    ∃ replayed,
      nextScalars xs.size verifier = some (xs, replayed) ∧
      (verifierSample replayed).1 = (sample sent).1 ∧
      (verifierSample replayed).2.sponge = (sample sent).2.sponge ∧
      (verifierSample replayed).2.scalarOffset = sent.stream.size ∧
      (verifierSample replayed).2.proof = verifier.proof := by
  dsimp only
  refine ⟨_, prover_scalars_verifier_refinement prover xs after openings openingOffset paths,
    ?_, ?_, ?_, ?_⟩ <;> rfl

theorem roundPoly_transmitted_scalars (prover : ProverState)
    (coeffs : Array Spec.Field.E) (eq : Bool) :
    addRoundPoly prover coeffs eq = addScalars prover
      (((Array.range coeffs.size).filter fun i => i != (if eq then 0 else 1)).map
        fun i => coeffs[i]?.getD ⟨0, 0, 0⟩) := by
  unfold addRoundPoly addScalars
  generalize ((Array.range coeffs.size).filter fun i => i != (if eq then 0 else 1)) = indices
  rw [← Array.toArray_toList (xs := indices)]
  generalize indices.toList = values
  induction values generalizing prover with
  | nil => simp
  | cons i tail ih => simpa using ih (addScalar prover (coeffs[i]?.getD ⟨0, 0, 0⟩))

theorem prover_roundPoly_stream_refinement (prover : ProverState)
    (coeffs after : Array Spec.Field.E) (eq : Bool)
    (openings : Array Spec.Merkle.PrunedMerklePaths) (openingOffset : Nat)
    (paths : Array Spec.Merkle.MerklePath) :
    let transmitted := ((Array.range coeffs.size).filter
      fun i => i != (if eq then 0 else 1)).map fun i => coeffs[i]?.getD ⟨0, 0, 0⟩
    let sent := addRoundPoly prover coeffs eq
    let verifier : VerifierState :=
      ⟨⟨sent.stream ++ after, openings⟩, prover.sponge, prover.stream.size, openingOffset, paths⟩
    nextScalars transmitted.size verifier = some (transmitted, {verifier with
      scalarOffset := sent.stream.size, sponge := sent.sponge}) := by
  dsimp only
  rw [roundPoly_transmitted_scalars]
  exact prover_scalars_verifier_refinement prover _ after openings openingOffset paths

theorem range_successor_map (n : Nat) :
    Array.range (n + 1) = #[0] ++ (Array.range n).map Nat.succ := by
  apply Array.toList_inj.mp
  simp only [Array.toList_append, Array.toList_map,
    Proofs.Merkle.Contracts.range_toList, List.range_succ_eq_map]
  rfl

theorem range_omit_zero (n : Nat) :
    (Array.range (n + 1)).filter (fun i => i != 0) =
      (Array.range n).map Nat.succ := by
  rw [range_successor_map]
  rw [Array.filter_append (by simp)]
  change #[] ++ ((Array.range n).map Nat.succ).filter (fun i => i != 0) = _
  rw [Array.empty_append, Array.filter_map]
  have keep : (Array.range n).filter ((fun i => i != 0) ∘ Nat.succ) = Array.range n := by
    apply Array.filter_eq_self.mpr
    intro i _
    simp
  rw [keep]

theorem range_omit_one (n : Nat) :
    (Array.range (n + 2)).filter (fun i => i != 1) =
      #[0] ++ (Array.range n).map (fun i => i + 2) := by
  rw [show n + 2 = (n + 1) + 1 by omega, range_successor_map]
  rw [Array.filter_append (by simp)]
  change #[0] ++ ((Array.range (n + 1)).map Nat.succ).filter (fun i => i != 1) = _
  rw [Array.filter_map]
  have predicate : ((fun i => i != 1) ∘ Nat.succ) = (fun i => i != 0) := by
    funext i
    simp
  rw [predicate, range_omit_zero, Array.map_map]
  rfl

theorem roundPoly_eq_stream (prover : ProverState) (coeffs : Array Spec.Field.E)
    (domain : 2 ≤ coeffs.size) :
    addRoundPoly prover coeffs true = addScalars prover
      ((Array.range (coeffs.size - 1)).map fun i => coeffs[i + 1]?.getD ⟨0, 0, 0⟩) := by
  rw [roundPoly_transmitted_scalars]
  simp only [reduceIte]
  have shape : coeffs.size = (coeffs.size - 1) + 1 := by omega
  have indices : (Array.range coeffs.size).filter (fun i => i != 0) =
      (Array.range (coeffs.size - 1)).map Nat.succ := by
    rw [shape]
    simpa only [Nat.add_sub_cancel] using range_omit_zero (coeffs.size - 1)
  rw [indices, Array.map_map]
  rfl

theorem roundPoly_plain_stream (prover : ProverState) (coeffs : Array Spec.Field.E)
    (domain : 2 ≤ coeffs.size) :
    addRoundPoly prover coeffs false = addScalars prover
      (#[coeffs[0]?.getD ⟨0, 0, 0⟩] ++
        (Array.range (coeffs.size - 2)).map fun i => coeffs[i + 2]?.getD ⟨0, 0, 0⟩) := by
  rw [roundPoly_transmitted_scalars]
  simp only [Bool.false_eq_true, reduceIte]
  have shape : coeffs.size = (coeffs.size - 2) + 2 := by omega
  have indices : (Array.range coeffs.size).filter (fun i => i != 1) =
      #[0] ++ (Array.range (coeffs.size - 2)).map (fun i => i + 2) := by
    rw [shape]
    simpa only [Nat.add_sub_cancel] using range_omit_one (coeffs.size - 2)
  rw [indices, Array.map_append, Array.map_map]
  simp only [Array.map_singleton, Function.comp_def]

theorem sumcheck_eq_replay_complete (before tail after : Array Spec.Field.E)
    (sponge : Sponge) (claimed factor : Spec.Field.E)
    (openings : Array Spec.Merkle.PrunedMerklePaths) (openingOffset : Nat)
    (paths : Array Spec.Merkle.MerklePath) (positive : 1 ≤ tail.size) :
    let state : VerifierState :=
      ⟨⟨before ++ tail ++ after, openings⟩, sponge, before.size, openingOffset, paths⟩
    sumcheckRoundPoly state tail.size claimed (some factor) =
      some (#[Spec.Field.eadd claimed
        (Spec.Field.emul factor (tail.foldl Spec.Field.eadd Spec.Field.zero))] ++ tail,
        {state with scalarOffset := before.size + tail.size, sponge := tail.foldl observe sponge}) := by
  dsimp only
  unfold sumcheckRoundPoly
  rw [ite_eq_right (by omega)]
  rw [appended_scalars_replay before tail after sponge openings openingOffset paths]
  rfl

theorem sumcheck_plain_replay_complete (before tail after : Array Spec.Field.E)
    (c0 claimed : Spec.Field.E) (sponge : Sponge)
    (openings : Array Spec.Merkle.PrunedMerklePaths) (openingOffset : Nat)
    (paths : Array Spec.Merkle.MerklePath) :
    let state : VerifierState :=
      ⟨⟨before ++ #[c0] ++ tail ++ after, openings⟩, sponge, before.size, openingOffset, paths⟩
    sumcheckRoundPoly state (tail.size + 1) claimed none =
      some (#[c0, Spec.Field.eadd claimed (tail.foldl Spec.Field.eadd Spec.Field.zero)] ++ tail,
        {state with scalarOffset := before.size + 1 + tail.size, sponge := tail.foldl observe (observe sponge c0)}) := by
  dsimp only
  unfold sumcheckRoundPoly
  rw [ite_eq_right (by omega)]
  simp only [Nat.add_sub_cancel]
  have first := appended_scalar_replays before (tail ++ after) c0 sponge
    openings openingOffset paths
  simp only [Array.append_assoc] at first ⊢
  rw [first]
  simp only [Bind.bind, Option.bind]
  have rest := appended_scalars_replay (before ++ #[c0]) tail after
    (observe sponge c0) openings openingOffset paths
  simp only [Array.size_append, Array.size_singleton, Array.append_assoc] at rest
  rw [rest]

theorem prover_roundPoly_eq_verifier_refinement (prover : ProverState)
    (coeffs after : Array Spec.Field.E) (claimed factor : Spec.Field.E)
    (openings : Array Spec.Merkle.PrunedMerklePaths) (openingOffset : Nat)
    (paths : Array Spec.Merkle.MerklePath) (domain : 2 ≤ coeffs.size) :
    let tail := (Array.range (coeffs.size - 1)).map
      fun i => coeffs[i + 1]?.getD ⟨0, 0, 0⟩
    let sent := addRoundPoly prover coeffs true
    let verifier : VerifierState :=
      ⟨⟨sent.stream ++ after, openings⟩, prover.sponge, prover.stream.size, openingOffset, paths⟩
    sumcheckRoundPoly verifier (coeffs.size - 1) claimed (some factor) =
      some (#[Spec.Field.eadd claimed
        (Spec.Field.emul factor (tail.foldl Spec.Field.eadd Spec.Field.zero))] ++ tail,
        {verifier with scalarOffset := sent.stream.size, sponge := sent.sponge}) := by
  dsimp only
  rw [roundPoly_eq_stream prover coeffs domain, addScalars_state]
  have positive : 1 ≤ ((Array.range (coeffs.size - 1)).map
      fun i => coeffs[i + 1]?.getD (⟨0, 0, 0⟩ : Spec.Field.E)).size := by
    simp only [Array.size_map, Array.size_range]
    omega
  simpa only [Array.size_map, Array.size_range, Array.size_append] using
    sumcheck_eq_replay_complete prover.stream _ after prover.sponge claimed factor
      openings openingOffset paths positive

theorem prover_roundPoly_plain_verifier_refinement (prover : ProverState)
    (coeffs after : Array Spec.Field.E) (claimed : Spec.Field.E)
    (openings : Array Spec.Merkle.PrunedMerklePaths) (openingOffset : Nat)
    (paths : Array Spec.Merkle.MerklePath) (domain : 2 ≤ coeffs.size) :
    let c0 := coeffs[0]?.getD (⟨0, 0, 0⟩ : Spec.Field.E)
    let tail := (Array.range (coeffs.size - 2)).map
      fun i => coeffs[i + 2]?.getD ⟨0, 0, 0⟩
    let sent := addRoundPoly prover coeffs false
    let verifier : VerifierState :=
      ⟨⟨sent.stream ++ after, openings⟩, prover.sponge, prover.stream.size, openingOffset, paths⟩
    sumcheckRoundPoly verifier (coeffs.size - 1) claimed none =
      some (#[c0, Spec.Field.eadd claimed (tail.foldl Spec.Field.eadd Spec.Field.zero)] ++ tail,
        {verifier with scalarOffset := sent.stream.size, sponge := sent.sponge}) := by
  dsimp only
  rw [roundPoly_plain_stream prover coeffs domain, addScalars_state]
  have degree : coeffs.size - 1 = (coeffs.size - 2) + 1 := by omega
  have replay := sumcheck_plain_replay_complete prover.stream
    ((Array.range (coeffs.size - 2)).map fun i => coeffs[i + 2]?.getD ⟨0, 0, 0⟩)
    after (coeffs[0]?.getD ⟨0, 0, 0⟩) claimed prover.sponge openings openingOffset paths
  simpa [Array.append_assoc, degree, Nat.add_assoc] using replay

theorem coefficient_suffix_stream (front tail : Array Spec.Field.E) :
    ((Array.range tail.size).map fun i =>
      (front ++ tail)[i + front.size]?.getD (⟨0, 0, 0⟩ : Spec.Field.E)) = tail := by
  apply Array.ext
  · simp only [Array.size_map, Array.size_range]
  · intro i left right
    simp only [Array.getElem_map, Array.range]
    rw [Proofs.Merkle.Contracts.ofFn_lookup]
    rw [Array.getElem?_append_right (show front.size ≤ i + front.size by omega)]
    simp only [Nat.add_sub_cancel_right]
    rw [Array.getElem?_eq_getElem right]
    rfl

theorem prover_sumcheck_eq_original (prover : ProverState)
    (c0 claimed factor : Spec.Field.E) (tail after : Array Spec.Field.E)
    (openings : Array Spec.Merkle.PrunedMerklePaths) (openingOffset : Nat)
    (paths : Array Spec.Merkle.MerklePath) (positive : 1 ≤ tail.size)
    (compatible : c0 = Spec.Field.eadd claimed
      (Spec.Field.emul factor (tail.foldl Spec.Field.eadd Spec.Field.zero))) :
    let coeffs := #[c0] ++ tail
    let sent := addRoundPoly prover coeffs true
    let verifier : VerifierState :=
      ⟨⟨sent.stream ++ after, openings⟩, prover.sponge, prover.stream.size, openingOffset, paths⟩
    sumcheckRoundPoly verifier tail.size claimed (some factor) =
      some (coeffs, {verifier with scalarOffset := sent.stream.size, sponge := sent.sponge}) := by
  have stream := coefficient_suffix_stream #[c0] tail
  simp only [Array.size_singleton] at stream
  have domain : 2 ≤ (#[c0] ++ tail).size := by
    simp only [Array.size_append, Array.size_singleton]
    omega
  have replay := prover_roundPoly_eq_verifier_refinement prover (#[c0] ++ tail) after
    claimed factor openings openingOffset paths domain
  simpa only [Array.size_append, Array.size_singleton, Nat.add_sub_cancel_left,
    stream, ← compatible] using replay

theorem prover_sumcheck_plain_original (prover : ProverState)
    (c0 c1 claimed : Spec.Field.E) (tail after : Array Spec.Field.E)
    (openings : Array Spec.Merkle.PrunedMerklePaths) (openingOffset : Nat)
    (paths : Array Spec.Merkle.MerklePath)
    (compatible : c1 = Spec.Field.eadd claimed (tail.foldl Spec.Field.eadd Spec.Field.zero)) :
    let coeffs := #[c0, c1] ++ tail
    let sent := addRoundPoly prover coeffs false
    let verifier : VerifierState :=
      ⟨⟨sent.stream ++ after, openings⟩, prover.sponge, prover.stream.size, openingOffset, paths⟩
    sumcheckRoundPoly verifier (tail.size + 1) claimed none =
      some (coeffs, {verifier with scalarOffset := sent.stream.size, sponge := sent.sponge}) := by
  have stream := coefficient_suffix_stream #[c0, c1] tail
  change ((Array.range tail.size).map fun i =>
    (#[c0, c1] ++ tail)[i + 2]?.getD (⟨0, 0, 0⟩ : Spec.Field.E)) = tail at stream
  have domain : 2 ≤ (#[c0, c1] ++ tail).size := by
    simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil] 
    omega
  have size : (#[c0, c1] ++ tail).size = 2 + tail.size := by simp
  have degree : 2 + tail.size - 1 = tail.size + 1 := by omega
  have length : 2 + tail.size - 2 = tail.size := by omega
  have first : (#[c0, c1] ++ tail)[0]?.getD (⟨0, 0, 0⟩ : Spec.Field.E) = c0 := by
    rw [Array.getElem?_append_left (by change 0 < 2; omega)]
    rfl
  have replay := prover_roundPoly_plain_verifier_refinement prover (#[c0, c1] ++ tail)
    after claimed openings openingOffset paths domain
  simpa only [size, degree, length, stream, first, ← compatible] using replay

theorem eadd_cancel_right (a b : Spec.Field.E) :
    Spec.Field.eadd (Spec.Field.eadd a b) b = a := by
  cases a
  cases b
  unfold Spec.Field.eadd Spec.Field.add
  congr 1 <;> apply UInt64.toBitVec_inj.mp <;>
    simp only [UInt64.toBitVec_xor, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem sumcheck_omitted_compatibility (omitted contribution claimed : Spec.Field.E) :
    claimed = Spec.Field.eadd omitted contribution ↔
      omitted = Spec.Field.eadd claimed contribution := by
  constructor
  · intro relation
    rw [relation, eadd_cancel_right]
  · intro relation
    rw [relation, eadd_cancel_right]

theorem prover_sumcheck_eq_claim (prover : ProverState)
    (c0 claimed factor : Spec.Field.E) (tail after : Array Spec.Field.E)
    (openings : Array Spec.Merkle.PrunedMerklePaths) (openingOffset : Nat)
    (paths : Array Spec.Merkle.MerklePath) (positive : 1 ≤ tail.size)
    (claim : claimed = Spec.Field.eadd c0
      (Spec.Field.emul factor (tail.foldl Spec.Field.eadd Spec.Field.zero))) :
    let coeffs := #[c0] ++ tail
    let sent := addRoundPoly prover coeffs true
    let verifier : VerifierState :=
      ⟨⟨sent.stream ++ after, openings⟩, prover.sponge, prover.stream.size, openingOffset, paths⟩
    sumcheckRoundPoly verifier tail.size claimed (some factor) =
      some (coeffs, {verifier with scalarOffset := sent.stream.size, sponge := sent.sponge}) := by
  exact prover_sumcheck_eq_original prover c0 claimed factor tail after openings
    openingOffset paths positive ((sumcheck_omitted_compatibility _ _ _).mp claim)

theorem prover_sumcheck_plain_claim (prover : ProverState)
    (c0 c1 claimed : Spec.Field.E) (tail after : Array Spec.Field.E)
    (openings : Array Spec.Merkle.PrunedMerklePaths) (openingOffset : Nat)
    (paths : Array Spec.Merkle.MerklePath)
    (claim : claimed = Spec.Field.eadd c1 (tail.foldl Spec.Field.eadd Spec.Field.zero)) :
    let coeffs := #[c0, c1] ++ tail
    let sent := addRoundPoly prover coeffs false
    let verifier : VerifierState :=
      ⟨⟨sent.stream ++ after, openings⟩, prover.sponge, prover.stream.size, openingOffset, paths⟩
    sumcheckRoundPoly verifier (tail.size + 1) claimed none =
      some (coeffs, {verifier with scalarOffset := sent.stream.size, sponge := sent.sponge}) := by
  exact prover_sumcheck_plain_original prover c0 c1 claimed tail after openings
    openingOffset paths ((sumcheck_omitted_compatibility _ _ _).mp claim)

theorem finish_rejects_scalar_remainder (s : VerifierState)
    (h : s.scalarOffset < s.proof.scalars.size) : finish s = none := by
  unfold finish
  split
  · next e => omega
  · rfl

theorem finish_rejects_opening_remainder (s : VerifierState)
    (h : s.openingOffset < s.proof.openings.size) : finish s = none := by
  unfold finish
  split
  · next e => omega
  · rfl

theorem checked_coefficients_domain (s : ProverState) (coeffs : Array Spec.Field.E) (eq : Bool) :
    (checkedAddRoundPoly s coeffs eq).isSome = true ↔ coeffs.size ≥ 2 := by
  unfold checkedAddRoundPoly
  split <;> simp_all

theorem nextScalars_consumption_and_binding (count : Nat) (s t : VerifierState)
    (xs : Array Spec.Field.E) (h : nextScalars count s = some (xs, t)) :
    xs.size = count ∧ t.scalarOffset = s.scalarOffset + count ∧
      t.sponge = xs.foldl observe s.sponge := by
  induction count generalizing s t xs with
  | zero =>
    change some (#[], s) = some (xs, t) at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp
  | succ count ih =>
    change (do
      let (x, middle) ← nextScalar s
      let (tail, last) ← nextScalars count middle
      some (#[x] ++ tail, last)) = some (xs, t) at h
    cases first : nextScalar s with
    | none => simp [first] at h
    | some p =>
      rcases p with ⟨x, middle⟩
      cases rest : nextScalars count middle with
      | none => simp [first, rest] at h
      | some p =>
        rcases p with ⟨tail, last⟩
        simp [first, rest] at h
        rcases h with ⟨rfl, rfl⟩
        obtain ⟨length, offset, binding⟩ := ih middle last tail rest
        obtain ⟨step, observed⟩ := nextScalar_binds s middle x first
        constructor
        · simp only [Array.size_append, Array.size_singleton, length]; omega
        constructor
        · omega
        · simpa [Array.foldl_append, observed] using binding

theorem grindCheck_sound (s t : VerifierState) (bits : Nat)
    (accepted : grindCheck s bits = some t) :
    ∃ nonce middle, nextRaw s = some (nonce, middle) ∧
      (verifyPow middle.sponge nonce bits).1 = true ∧
      t.sponge = (verifyPow middle.sponge nonce bits).2 ∧
      t.scalarOffset = s.scalarOffset + 1 := by
  unfold grindCheck at accepted
  cases readNonce : nextRaw s with
  | none => simp [readNonce] at accepted
  | some pair =>
    rcases pair with ⟨nonce, middle⟩
    simp only [readNonce, Bind.bind, Option.bind] at accepted
    split at accepted
    · rename_i valid
      cases accepted
      exact ⟨nonce, middle, rfl, valid, rfl,
        nextRaw_consumes_one s middle nonce readNonce⟩
    · simp at accepted

theorem merkle_acceptance_sound (s t : VerifierState) (root : Spec.Merkle.Digest)
    (depth : Nat) (queries : Array Nat) (rowWords leafWords : Nat)
    (rows : Array (Array UInt64))
    (accepted : merkle s root depth queries rowWords leafWords = some (rows, t)) :
    ∃ batch paths,
      s.proof.openings[s.openingOffset]? = some batch ∧
      Spec.Merkle.expandPruned batch depth queries rowWords leafWords = some (root, paths) ∧
      rows = paths.map (·.leaf) ∧ t.paths = s.paths ++ paths ∧
      t.openingOffset = s.openingOffset + 1 ∧ t.scalarOffset = s.scalarOffset := by
  unfold merkle at accepted
  cases opening : s.proof.openings[s.openingOffset]? with
  | none => simp [opening] at accepted
  | some batch =>
    simp only [opening, Bind.bind, Option.bind] at accepted
    cases expanded : Spec.Merkle.expandPruned batch depth queries rowWords leafWords with
    | none => simp [expanded] at accepted
    | some pair =>
      rcases pair with ⟨computed, paths⟩
      simp only [expanded] at accepted
      split at accepted
      · rename_i sameRoot
        subst computed
        simp only [Option.some.injEq, Prod.mk.injEq] at accepted
        rcases accepted with ⟨rfl, rfl⟩
        exact ⟨batch, paths, rfl, expanded, rfl, rfl, rfl, rfl⟩
      · simp at accepted

theorem sumcheckRoundPoly_shape (s t : VerifierState) (degree : Nat)
    (claimedSum : Spec.Field.E) (eqFactor : Option Spec.Field.E)
    (coeffs : Array Spec.Field.E)
    (accepted : sumcheckRoundPoly s degree claimedSum eqFactor = some (coeffs, t)) :
    1 ≤ degree ∧ coeffs.size = degree + 1 ∧
      t.scalarOffset = s.scalarOffset + degree := by
  unfold sumcheckRoundPoly at accepted
  split at accepted
  · simp at accepted
  · rename_i degreeBound
    have positive : 1 ≤ degree := by omega
    cases eqFactor with
    | none =>
      cases first : nextScalar s with
      | none => simp [first] at accepted
      | some pair =>
        rcases pair with ⟨c0, middle⟩
        simp only [first, Bind.bind, Option.bind] at accepted
        cases rest : nextScalars (degree - 1) middle with
        | none => simp [rest] at accepted
        | some pair =>
          rcases pair with ⟨tail, last⟩
          simp [rest] at accepted
          rcases accepted with ⟨rfl, rfl⟩
          obtain ⟨length, offset, _⟩ := nextScalars_consumption_and_binding
            (degree - 1) middle last tail rest
          have step := (nextScalar_binds s middle c0 first).1
          refine ⟨positive, ?_, ?_⟩
          · simp only [Array.size_append, length]
            change 2 + (degree - 1) = degree + 1
            omega
          · omega
    | some factor =>
      cases rest : nextScalars degree s with
      | none => simp [rest] at accepted
      | some pair =>
        rcases pair with ⟨tail, last⟩
        simp [rest] at accepted
        rcases accepted with ⟨rfl, rfl⟩
        obtain ⟨length, offset, _⟩ := nextScalars_consumption_and_binding degree s last tail rest
        refine ⟨positive, ?_, offset⟩
        simp only [Array.size_append, Array.size_singleton, length]
        omega

theorem sumcheckRoundPoly_reconstruction (s t : VerifierState) (degree : Nat)
    (claimedSum : Spec.Field.E) (eqFactor : Option Spec.Field.E)
    (coeffs : Array Spec.Field.E)
    (accepted : sumcheckRoundPoly s degree claimedSum eqFactor = some (coeffs, t)) :
    match eqFactor with
    | none => ∃ c0 middle tail,
        nextScalar s = some (c0, middle) ∧
        nextScalars (degree - 1) middle = some (tail, t) ∧
        coeffs = #[c0, Spec.Field.eadd claimedSum (tail.foldl Spec.Field.eadd Spec.Field.zero)] ++ tail ∧
        t.sponge = tail.foldl observe (observe s.sponge c0)
    | some factor => ∃ tail,
        nextScalars degree s = some (tail, t) ∧
        coeffs = #[Spec.Field.eadd claimedSum
          (Spec.Field.emul factor (tail.foldl Spec.Field.eadd Spec.Field.zero))] ++ tail ∧
        t.sponge = tail.foldl observe s.sponge := by
  unfold sumcheckRoundPoly at accepted
  split at accepted
  · simp at accepted
  · cases eqFactor with
    | none =>
      cases first : nextScalar s with
      | none => simp [first] at accepted
      | some pair =>
        rcases pair with ⟨c0, middle⟩
        simp only [first, Bind.bind, Option.bind] at accepted
        cases rest : nextScalars (degree - 1) middle with
        | none => simp [rest] at accepted
        | some pair =>
          rcases pair with ⟨tail, last⟩
          simp [rest] at accepted
          rcases accepted with ⟨rfl, rfl⟩
          have binding := (nextScalars_consumption_and_binding (degree - 1) middle last tail rest).2.2
          have observed := (nextScalar_binds s middle c0 first).2
          exact ⟨c0, middle, tail, rfl, rest, rfl, observed ▸ binding⟩
    | some factor =>
      cases rest : nextScalars degree s with
      | none => simp [rest] at accepted
      | some pair =>
        rcases pair with ⟨tail, last⟩
        simp [rest] at accepted
        rcases accepted with ⟨rfl, rfl⟩
        exact ⟨tail, rfl, rfl,
          (nextScalars_consumption_and_binding degree s last tail rest).2.2⟩

theorem proverNew_verifierNew_sync (proof : ReplayProof) (iv publicInput : ByteArray) :
    let p := proverNew iv publicInput
    let v := verifierNew proof iv publicInput
    v.sponge = p.sponge ∧ v.scalarOffset = p.stream.size ∧
      v.openingOffset = 0 ∧ v.paths = #[] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem fromHalves_hashToScalars (d : ByteArray) (hsize : d.size = 32) :
    let halves := Spec.Merkle.hashToScalars d
    Spec.Merkle.fromHalves halves.1 halves.2 = some (Spec.Merkle.toDigest d) := by
  dsimp only [Spec.Merkle.hashToScalars, Spec.Merkle.fromHalves]
  rw [ite_eq_left ⟨rfl, rfl⟩]
  rw [Proofs.Merkle.Contracts.wordsBytes_four_roundtrip d hsize]
  unfold Spec.Merkle.checkedDigest
  rw [ite_eq_left hsize]

theorem prover_addRoot_verifier_refinement (prover : ProverState)
    (d : ByteArray) (hsize : d.size = 32) (after : Array Spec.Field.E)
    (openings : Array Spec.Merkle.PrunedMerklePaths) (openingOffset : Nat)
    (paths : Array Spec.Merkle.MerklePath) :
    let sent := addRoot prover d
    let verifier : VerifierState :=
      ⟨⟨sent.stream ++ after, openings⟩, prover.sponge, prover.stream.size, openingOffset, paths⟩
    ∃ low v1 high v2,
      nextScalar verifier = some (low, v1) ∧
      nextScalar v1 = some (high, v2) ∧
      Spec.Merkle.fromHalves low high = some (Spec.Merkle.toDigest d) ∧
      v2 = {verifier with scalarOffset := sent.stream.size, sponge := sent.sponge} := by
  dsimp only
  let halves := Spec.Merkle.hashToScalars d
  have htwo : (#[halves.1, halves.2] : Array Spec.Field.E) = #[halves.1] ++ #[halves.2] := rfl
  have hstream : (addRoot prover d).stream = prover.stream ++ #[halves.1] ++ #[halves.2] := by
    simp only [addRoot, addScalar, halves, Array.push_eq_append, Array.append_assoc]
  have hsponge : (addRoot prover d).sponge = observe (observe prover.sponge halves.1) halves.2 := rfl
  have step1 := appended_scalar_replays prover.stream (#[halves.2] ++ after) halves.1
    prover.sponge openings openingOffset paths
  have step2 := appended_scalar_replays (prover.stream ++ #[halves.1]) after halves.2
    (observe prover.sponge halves.1) openings openingOffset paths
  dsimp only at step1 step2
  have eqStreams : (addRoot prover d).stream ++ after =
      prover.stream ++ #[halves.1] ++ (#[halves.2] ++ after) := by
    rw [hstream, Array.append_assoc]
  have eqStreams2 : prover.stream ++ #[halves.1] ++ #[halves.2] ++ after =
      (addRoot prover d).stream ++ after := by
    rw [hstream]
  let verifier0 : VerifierState :=
    ⟨⟨(addRoot prover d).stream ++ after, openings⟩, prover.sponge, prover.stream.size, openingOffset, paths⟩
  let v1 : VerifierState :=
    {verifier0 with scalarOffset := prover.stream.size + 1, sponge := observe prover.sponge halves.1}
  let v2 : VerifierState :=
    ⟨⟨(addRoot prover d).stream ++ after, openings⟩,
      observe (observe prover.sponge halves.1) halves.2,
      (prover.stream ++ #[halves.1]).size + 1, openingOffset, paths⟩
  have hs1 : nextScalar verifier0 = some (halves.1, v1) := by
    dsimp only [verifier0, v1]
    simpa only [eqStreams] using step1
  have hs2 : nextScalar v1 = some (halves.2, v2) := by
    dsimp only [verifier0, v1, v2]
    simpa only [Array.size_append, Array.size_singleton, eqStreams2] using step2
  refine ⟨halves.1, v1, halves.2, v2, hs1, hs2, fromHalves_hashToScalars d hsize, ?_⟩
  dsimp only [v2, verifier0]
  rw [hstream, hsponge]
  simp only [Array.size_append, Array.size_singleton, Nat.add_assoc]

theorem searchNonce_powBitsOk (s : Sponge) (bits fuel : Nat) (start nonce : UInt64)
    (h : searchNonce s bits fuel start = some nonce) :
    powBitsOk s ⟨nonce, 0, 0⟩ bits = true := by
  induction fuel generalizing start with
  | zero => simp [searchNonce] at h
  | succ fuel ih =>
    simp only [searchNonce] at h
    cases hc : powBitsOk s ⟨start, 0, 0⟩ bits with
    | true =>
      rw [hc] at h
      simp only [ite_true, Option.some.injEq] at h
      subst h
      exact hc
    | false =>
      rw [hc] at h
      simp only [Bool.false_eq_true, ite_false] at h
      exact ih _ h

theorem powGrinding_verifyPow_accepted (s : Sponge) (bits fuel : Nat)
    (n : UInt64) (fs : Sponge) (hg : powGrinding s bits fuel = some (n, fs)) :
    verifyPow s ⟨n, 0, 0⟩ bits = (true, fs) := by
  unfold powGrinding at hg
  cases hc64 : decide (bits ≥ 64) with
  | true =>
    rw [ite_eq_left (of_decide_eq_true hc64)] at hg
    simp at hg
  | false =>
    rw [ite_eq_right (of_decide_eq_false hc64)] at hg
    cases bits with
    | zero =>
      have hz : (0 == 0) = true := rfl
      rw [hz] at hg
      simp only [ite_true, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hg
      rcases hg with ⟨rfl, rfl⟩
      rfl
    | succ k =>
      have hne : (k + 1 == 0) = false := rfl
      rw [hne] at hg
      simp only [Bool.false_eq_true, ite_false] at hg
      cases hs : searchNonce s (k + 1) fuel 0 with
      | none => simp [hs] at hg
      | some found =>
        rw [hs] at hg
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hg
        rcases hg with ⟨rfl, rfl⟩
        have hok := searchNonce_powBitsOk s (k + 1) fuel 0 found hs
        unfold verifyPow
        rw [hne]
        simp only [Bool.false_eq_true, ite_false]
        unfold powBitsOk at hok
        exact Prod.ext hok rfl

theorem prover_grind_verifier_refinement (prover sent : ProverState)
    (bits fuel : Nat) (n : UInt64) (after : Array Spec.Field.E)
    (openings : Array Spec.Merkle.PrunedMerklePaths) (openingOffset : Nat)
    (paths : Array Spec.Merkle.MerklePath)
    (hg : grind prover bits fuel = some (n, sent)) :
    let verifier : VerifierState :=
      ⟨⟨sent.stream ++ after, openings⟩, prover.sponge, prover.stream.size, openingOffset, paths⟩
    grindCheck verifier bits =
      some {verifier with scalarOffset := sent.stream.size, sponge := sent.sponge} := by
  dsimp only
  unfold grind at hg
  cases hp : powGrinding prover.sponge bits fuel with
  | none => simp [hp] at hg
  | some pair =>
    rcases pair with ⟨nonce, fs⟩
    rw [hp] at hg
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hg
    rcases hg with ⟨rfl, rfl⟩
    have hacc := powGrinding_verifyPow_accepted prover.sponge bits fuel nonce fs hp
    unfold grindCheck nextRaw
    have hlookup : (prover.stream.push ⟨nonce, 0, 0⟩ ++ after)[prover.stream.size]? =
        some ⟨nonce, 0, 0⟩ := by
      rw [Array.push_eq_append]
      rw [Array.getElem?_append_left (by simp only [Array.size_append, Array.size_singleton]; omega)]
      rw [Array.getElem?_append_right (by omega)]
      simp only [Nat.sub_self]
      rfl
    rw [hlookup]
    simp only [Bind.bind, Option.bind, hacc, ite_true, Array.size_push]

theorem prover_merkle_verifier_refinement
    (scalars : Array Spec.Field.E) (sponge : Sponge) (scalarOffset : Nat)
    (beforeOpenings afterOpenings : Array Spec.Merkle.PrunedMerklePaths)
    (batch : Spec.Merkle.PrunedMerklePaths)
    (root : Spec.Merkle.Digest) (depth : Nat) (queries : Array Nat)
    (rowWords leafWords : Nat) (paths openedPaths : Array Spec.Merkle.MerklePath)
    (hexp : Spec.Merkle.expandPruned batch depth queries rowWords leafWords =
      some (root, openedPaths)) :
    let verifier : VerifierState :=
      ⟨⟨scalars, beforeOpenings ++ #[batch] ++ afterOpenings⟩,
        sponge, scalarOffset, beforeOpenings.size, paths⟩
    merkle verifier root depth queries rowWords leafWords =
      some (openedPaths.map (·.leaf),
        {verifier with openingOffset := beforeOpenings.size + 1, paths := paths ++ openedPaths}) := by
  dsimp only
  unfold merkle
  have hlookup : (beforeOpenings ++ #[batch] ++ afterOpenings)[beforeOpenings.size]? = some batch := by
    rw [Array.getElem?_append_left (by simp only [Array.size_append, Array.size_singleton]; omega)]
    rw [Array.getElem?_append_right (by omega)]
    simp
  rw [hlookup]
  simp only [Bind.bind, Option.bind, hexp, ite_true]

theorem prover_session_verifier_refinement
    (iv publicInput rootBytes : ByteArray) (hroot : rootBytes.size = 32)
    (xs : Array Spec.Field.E)
    (c0Eq claimedEq factorEq c0Plain c1Plain claimedPlain : Spec.Field.E)
    (tailEq tailPlain : Array Spec.Field.E) (hposEq : 1 ≤ tailEq.size)
    (hclaimEq : claimedEq = Spec.Field.eadd c0Eq
      (Spec.Field.emul factorEq (tailEq.foldl Spec.Field.eadd Spec.Field.zero)))
    (hclaimPlain : claimedPlain = Spec.Field.eadd c1Plain
      (tailPlain.foldl Spec.Field.eadd Spec.Field.zero))
    (bits fuel : Nat) (nonce : UInt64)
    (batch : Spec.Merkle.PrunedMerklePaths) (merkleRoot : Spec.Merkle.Digest)
    (depth : Nat) (queries : Array Nat) (rowWords leafWords : Nat)
    (openedPaths : Array Spec.Merkle.MerklePath)
    (hexp : Spec.Merkle.expandPruned batch depth queries rowWords leafWords =
      some (merkleRoot, openedPaths))
    (pGrind : ProverState)
    (hgrind : grind
      (sample (addRoundPoly
        (addRoundPoly (addRoot (addScalars (proverNew iv publicInput) xs) rootBytes)
          (#[c0Eq] ++ tailEq) true)
        (#[c0Plain, c1Plain] ++ tailPlain) false)).2
      bits fuel = some (nonce, pGrind)) :
    let p0 := proverNew iv publicInput
    let p1 := addScalars p0 xs
    let p2 := addRoot p1 rootBytes
    let coeffsEq := #[c0Eq] ++ tailEq
    let p3 := addRoundPoly p2 coeffsEq true
    let coeffsPlain := #[c0Plain, c1Plain] ++ tailPlain
    let p4 := addRoundPoly p3 coeffsPlain false
    let (ch1, p5) := sample p4
    let (ch2, p7) := sample pGrind
    let proof : ReplayProof := ⟨p7.stream, #[batch]⟩
    let v0 := verifierNew proof iv publicInput
    ∃ v1 low v1a high v2 v3 v4 v6 v8,
      nextScalars xs.size v0 = some (xs, v1) ∧
      nextScalar v1 = some (low, v1a) ∧
      nextScalar v1a = some (high, v2) ∧
      Spec.Merkle.fromHalves low high = some (Spec.Merkle.toDigest rootBytes) ∧
      sumcheckRoundPoly v2 tailEq.size claimedEq (some factorEq) = some (coeffsEq, v3) ∧
      sumcheckRoundPoly v3 (tailPlain.size + 1) claimedPlain none = some (coeffsPlain, v4) ∧
      (verifierSample v4).1 = ch1 ∧
      grindCheck (verifierSample v4).2 bits = some v6 ∧
      (verifierSample v6).1 = ch2 ∧
      merkle (verifierSample v6).2 merkleRoot depth queries rowWords leafWords =
        some (openedPaths.map (·.leaf), v8) ∧
      v8.sponge = p7.sponge ∧
      finish v8 = some openedPaths := by
  intro p0 p1 p2 coeffsEq p3 coeffsPlain p4
  dsimp only
  let p5 := (sample p4).2
  change grind p5 bits fuel = some (nonce, pGrind) at hgrind
  have hstream7 : (sample pGrind).2.stream = pGrind.stream := rfl
  have hstreamGrind : pGrind.stream = p5.stream.push ⟨nonce, 0, 0⟩ := by
    have hg' := hgrind
    unfold grind at hg'
    cases hp : powGrinding p5.sponge bits fuel with
    | none => simp [hp] at hg'
    | some pair =>
      rw [hp] at hg'
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hg'
      rcases hg' with ⟨hnonce, hst⟩
      rw [← hst, hnonce]
  have hstream5 : p5.stream = p4.stream := rfl
  have hstream4 : p4.stream = p3.stream ++ (#[c0Plain] ++ tailPlain) := by
    have hd : 2 ≤ coeffsPlain.size := by
      simp only [coeffsPlain, Array.size_append, List.size_toArray, List.length_cons, List.length_nil]
      omega
    have hr := roundPoly_plain_stream p3 coeffsPlain hd
    have hfirst : coeffsPlain[0]?.getD ⟨0, 0, 0⟩ = c0Plain := by
      dsimp only [coeffsPlain]
      rw [Array.getElem?_append_left (by change 0 < 2; omega)]
      rfl
    have htail := coefficient_suffix_stream #[c0Plain, c1Plain] tailPlain
    change ((Array.range tailPlain.size).map fun i =>
      coeffsPlain[i + 2]?.getD ⟨0, 0, 0⟩) = tailPlain at htail
    have hsize : coeffsPlain.size - 2 = tailPlain.size := by
      simp [coeffsPlain]
    rw [show p4 = addRoundPoly p3 coeffsPlain false from rfl, hr, addScalars_state,
      hfirst, hsize, htail]
  have hstream3 : p3.stream = p2.stream ++ tailEq := by
    have hd : 2 ≤ coeffsEq.size := by
      simp only [coeffsEq, Array.size_append, Array.size_singleton]
      omega
    have hr := roundPoly_eq_stream p2 coeffsEq hd
    have htail := coefficient_suffix_stream #[c0Eq] tailEq
    simp only [Array.size_singleton] at htail
    have hsize : coeffsEq.size - 1 = tailEq.size := by simp [coeffsEq]
    rw [show p3 = addRoundPoly p2 coeffsEq true from rfl, hr, addScalars_state, hsize, htail]
  have hstream2 : p2.stream = p1.stream ++
      #[(Spec.Merkle.hashToScalars rootBytes).1] ++ #[(Spec.Merkle.hashToScalars rootBytes).2] := by
    simp only [p2, addRoot, addScalar, Array.push_eq_append, Array.append_assoc]
  have hstream1 : p1.stream = xs := by
    simp [p1, p0, proverNew, addScalars_state]
  let nonceElem : Spec.Field.E := ⟨nonce, 0, 0⟩
  let rem1 : Array Spec.Field.E :=
    #[(Spec.Merkle.hashToScalars rootBytes).1] ++ #[(Spec.Merkle.hashToScalars rootBytes).2] ++
      tailEq ++ (#[c0Plain] ++ tailPlain) ++ #[nonceElem]
  let rem2 : Array Spec.Field.E := tailEq ++ (#[c0Plain] ++ tailPlain) ++ #[nonceElem]
  let rem3 : Array Spec.Field.E := (#[c0Plain] ++ tailPlain) ++ #[nonceElem]
  let rem4 : Array Spec.Field.E := #[nonceElem]
  have htotal : pGrind.stream = p1.stream ++ rem1 := by
    rw [hstreamGrind, hstream5, hstream4, hstream3, hstream2, Array.push_eq_append]
    simp only [rem1, nonceElem, Array.append_assoc]
  have htotal2 : pGrind.stream = p2.stream ++ rem2 := by
    rw [hstreamGrind, hstream5, hstream4, hstream3, Array.push_eq_append]
    simp only [rem2, nonceElem, Array.append_assoc]
  have htotal3 : pGrind.stream = p3.stream ++ rem3 := by
    rw [hstreamGrind, hstream5, hstream4, Array.push_eq_append]
    simp only [rem3, nonceElem, Array.append_assoc]
  have htotal4 : pGrind.stream = p4.stream ++ rem4 := by
    rw [hstreamGrind, hstream5, Array.push_eq_append]
  let vs1 : VerifierState := ⟨⟨p1.stream ++ rem1, #[batch]⟩, p0.sponge, p0.stream.size, 0, #[]⟩
  have s1 := prover_scalars_verifier_refinement p0 xs rem1 #[batch] 0 #[]
  dsimp only at s1
  change nextScalars xs.size vs1 =
    some (xs, {vs1 with scalarOffset := p1.stream.size, sponge := p1.sponge}) at s1
  have hv0 : vs1 = verifierNew ⟨(sample pGrind).2.stream, #[batch]⟩ iv publicInput := by
    dsimp only [vs1]
    rw [hstream7, htotal]
    rfl
  rw [hv0] at s1
  let vs2 : VerifierState := ⟨⟨p2.stream ++ rem2, #[batch]⟩, p1.sponge, p1.stream.size, 0, #[]⟩
  obtain ⟨low, v1a, high, v2, s2a, s2b, s2halves, hv2⟩ :=
    prover_addRoot_verifier_refinement p1 rootBytes hroot rem2 #[batch] 0 #[]
  change nextScalar vs2 = some (low, v1a) at s2a
  change v2 = {vs2 with scalarOffset := p2.stream.size, sponge := p2.sponge} at hv2
  have hv1eq : ({verifierNew ⟨(sample pGrind).2.stream, #[batch]⟩ iv publicInput with
      scalarOffset := p1.stream.size, sponge := p1.sponge} : VerifierState) = vs2 := by
    dsimp only [vs2]
    rw [hstream7, htotal2]
    rfl
  rw [← hv1eq] at s2a hv2
  let vs3 : VerifierState := ⟨⟨p3.stream ++ rem3, #[batch]⟩, p2.sponge, p2.stream.size, 0, #[]⟩
  have s3 := prover_sumcheck_eq_claim p2 c0Eq claimedEq factorEq tailEq rem3 #[batch] 0 #[]
    hposEq hclaimEq
  dsimp only at s3
  change sumcheckRoundPoly vs3 tailEq.size claimedEq (some factorEq) =
    some (coeffsEq, {vs3 with scalarOffset := p3.stream.size, sponge := p3.sponge}) at s3
  have hv2eq : v2 = vs3 := by
    dsimp only [vs3]
    rw [hv2, hstream7, htotal3]
    rfl
  rw [← hv2eq] at s3
  let vs4 : VerifierState := ⟨⟨p4.stream ++ rem4, #[batch]⟩, p3.sponge, p3.stream.size, 0, #[]⟩
  have s4 := prover_sumcheck_plain_claim p3 c0Plain c1Plain claimedPlain tailPlain rem4 #[batch] 0 #[]
    hclaimPlain
  dsimp only at s4
  change sumcheckRoundPoly vs4 (tailPlain.size + 1) claimedPlain none =
    some (coeffsPlain, {vs4 with scalarOffset := p4.stream.size, sponge := p4.sponge}) at s4
  have hv3eq : ({v2 with scalarOffset := p3.stream.size, sponge := p3.sponge} : VerifierState) = vs4 := by
    rw [hv2eq]
    dsimp only [vs3, vs4]
    rw [← htotal3, htotal4]
  rw [← hv3eq] at s4
  let v3 : VerifierState := {v2 with scalarOffset := p3.stream.size, sponge := p3.sponge}
  let v4 : VerifierState := {v3 with scalarOffset := p4.stream.size, sponge := p4.sponge}
  let vs5 : VerifierState := ⟨⟨pGrind.stream, #[batch]⟩, p5.sponge, p5.stream.size, 0, #[]⟩
  have s6 := prover_grind_verifier_refinement p5 pGrind bits fuel nonce #[] #[batch] 0 #[] hgrind
  dsimp only at s6
  simp only [Array.append_empty] at s6
  change grindCheck vs5 bits =
    some {vs5 with scalarOffset := pGrind.stream.size, sponge := pGrind.sponge} at s6
  have hv5eq : (verifierSample v4).2 = vs5 := by
    unfold verifierSample
    dsimp only [v4, v3, vs5]
    rw [hv2, hstream7, hstream5]
    rfl
  rw [← hv5eq] at s6
  let v6 : VerifierState := {(verifierSample v4).2 with
    scalarOffset := pGrind.stream.size, sponge := pGrind.sponge}
  let vs7 : VerifierState :=
    ⟨⟨pGrind.stream, #[batch]⟩, (sample pGrind).2.sponge, pGrind.stream.size, 0, #[]⟩
  have s8 := prover_merkle_verifier_refinement pGrind.stream (sample pGrind).2.sponge
    pGrind.stream.size #[] #[] batch merkleRoot depth queries rowWords leafWords #[] openedPaths hexp
  dsimp only at s8
  simp only [Array.empty_append, Array.append_empty, Array.size_empty, Nat.zero_add] at s8
  change merkle vs7 merkleRoot depth queries rowWords leafWords =
    some (openedPaths.map (·.leaf), {vs7 with openingOffset := 1, paths := openedPaths}) at s8
  have hv7eq : (verifierSample v6).2 = vs7 := by
    unfold verifierSample
    dsimp only [v6, vs7]
    rw [hv5eq]
    rfl
  rw [← hv7eq] at s8
  let v8 : VerifierState := {(verifierSample v6).2 with
    openingOffset := 1, paths := openedPaths}
  refine ⟨_, low, v1a, high, v2, v3, v4, v6, v8,
    s1, s2a, s2b, s2halves, s3, s4, rfl, s6, rfl, s8, rfl, ?_⟩
  unfold finish
  have hfin : v8.scalarOffset = v8.proof.scalars.size ∧ v8.openingOffset = v8.proof.openings.size := by
    dsimp only [v8]
    rw [hv7eq]
    exact ⟨rfl, rfl⟩
  rw [ite_eq_left hfin]

end LeanVmXmss.Proofs.Transcript.Replay
