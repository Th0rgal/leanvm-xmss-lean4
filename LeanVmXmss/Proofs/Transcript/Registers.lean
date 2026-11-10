import Model.Transcript.Registers
import Proofs.Keccak.Registers
import Proofs.Transcript.Minimality

namespace LeanVmXmss.Proofs.Transcript.Registers

open Model.Transcript.Registers

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem elem_ext (a b : Spec.Field.E) (h0 : a.c0 = b.c0) (h1 : a.c1 = b.c1)
    (h2 : a.c2 = b.c2) : a = b := by
  cases a
  cases b
  simp_all

theorem sponge_ext (a b : Spec.Transcript.Sponge) (h0 : a.state = b.state)
    (h1 : a.pending = b.pending) : a = b := by
  cases a
  cases b
  simp_all

theorem duplex_refines (s : Sponge) :
    ((duplex s).1, toSpec (duplex s).2) = Spec.Transcript.duplex (toSpec s) := by
  have perm := Proofs.Keccak.registers_permutation_refines_spec (input s)
  rw [Proofs.Keccak.spec_rounds_eq_permute] at perm
  have h0 := congrArg (fun a : Spec.Keccak.State => a[0]!) perm
  have h1 := congrArg (fun a : Spec.Keccak.State => a[1]!) perm
  have h2 := congrArg (fun a : Spec.Keccak.State => a[2]!) perm
  apply Prod.ext
  · apply elem_ext
    · simpa [duplex, Model.Keccak.State25.toSpec, Spec.Transcript.duplex, toSpec] using h0
    · simpa [duplex, Model.Keccak.State25.toSpec, Spec.Transcript.duplex, toSpec] using h1
    · simpa [duplex, Model.Keccak.State25.toSpec, Spec.Transcript.duplex, toSpec] using h2
  · apply sponge_ext
    · change (input (duplex s).2).toSpec =
        (Array.range 25).map (fun i => if i < 16 then (0 : UInt64) else (Spec.Keccak.permute (input s).toSpec)[i]!)
      rw [← perm]
      simp only [duplex]
      generalize Model.Keccak.keccakF1600 (input s) = a
      change (input {s with state := a, pending := 0}).toSpec =
        (Array.range 25).map (fun i => if i < 16 then (0 : UInt64) else a.toSpec[i]!)
      apply Array.ext
      · simp [input, Model.Keccak.State25.toSpec, -Array.getElem_range,
          Proofs.Keccak.range_twenty_five]
      · intro i hi hj
        have bound : i < 25 := by simpa [input, Model.Keccak.State25.toSpec] using hi
        have choices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
            i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨
            i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 := by omega
        rcases choices with h | h | h | h | h | h | h | h | h | h | h | h |
          h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst i <;>
          simp [input, Model.Keccak.State25.toSpec, -Array.getElem_range,
            Proofs.Keccak.range_twenty_five]
    · simp [toSpec, duplex, Spec.Transcript.duplex]

theorem sample_refines (s : Sponge) :
    ((sample s).1, toSpec (sample s).2) = Spec.Transcript.challenge (toSpec s) :=
  duplex_refines s

theorem absorb_partial_refines (s : Sponge) (x : Spec.Field.E) (tag : UInt64)
    (h : s.pending < 4) :
    toSpec (absorb s x tag) = Spec.Transcript.absorb (toSpec s) x tag := by
  have cases : s.pending = 0 ∨ s.pending = 1 ∨ s.pending = 2 ∨ s.pending = 3 := by omega
  rcases cases with h | h | h | h
  all_goals
    apply sponge_ext
    · simp [toSpec, absorb, input, Spec.Transcript.absorb, Model.Keccak.State25.toSpec, h]
    · simp [toSpec, absorb, Spec.Transcript.absorb, h]

theorem duplex_pending (s : Sponge) : (duplex s).2.pending = 0 := rfl

theorem absorb_refines (s : Sponge) (x : Spec.Field.E) (tag : UInt64)
    (h : s.pending ≤ 4) :
    toSpec (absorb s x tag) = Spec.Transcript.absorb (toSpec s) x tag := by
  by_cases full : s.pending = 4
  · have dp := duplex_refines s
    have state := congrArg Prod.snd dp
    change toSpec (duplex s).2 = (Spec.Transcript.duplex (toSpec s)).2 at state
    have step := absorb_partial_refines (duplex s).2 x tag (by rw [duplex_pending]; omega)
    rw [state] at step
    simp only [absorb, full, ite_true, duplex_pending, Spec.Transcript.absorb,
      Spec.Transcript.duplex, toSpec] at step ⊢
    exact step
  · exact absorb_partial_refines s x tag (by omega)

theorem observe_refines (s : Sponge) (x : Spec.Field.E) (h : s.pending ≤ 4) :
    toSpec (observe s x) = Spec.Transcript.observe (toSpec s) x := by
  exact absorb_refines s x 1 h

theorem init_refines (iv publicInput : ByteArray) :
    toSpec (init iv publicInput) = Spec.Transcript.init iv publicInput := by
  let initial : Model.Keccak.State25 :=
    ⟨Spec.Keccak.wordAt iv 0, Spec.Keccak.wordAt iv 8,
      Spec.Keccak.wordAt iv 16, Spec.Keccak.wordAt iv 24,
      Spec.Keccak.wordAt publicInput 0, Spec.Keccak.wordAt publicInput 8,
      Spec.Keccak.wordAt publicInput 16, Spec.Keccak.wordAt publicInput 24,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  have seed : initial.toSpec = (Array.range 25).map (fun i =>
      if i < 4 then Spec.Keccak.wordAt iv (8 * i)
      else if i < 8 then Spec.Keccak.wordAt publicInput (8 * (i - 4)) else 0) := by
    simp [initial, Model.Keccak.State25.toSpec, -Array.getElem_range,
      Proofs.Keccak.range_twenty_five]
  have perm := Proofs.Keccak.registers_permutation_refines_spec initial
  rw [Proofs.Keccak.spec_rounds_eq_permute, seed] at perm
  apply sponge_ext
  · change (input (init iv publicInput)).toSpec =
      (Array.range 25).map (fun i => if i < 16 then (0 : UInt64) else
        (Spec.Keccak.permute ((Array.range 25).map (fun j =>
          if j < 4 then Spec.Keccak.wordAt iv (8 * j)
          else if j < 8 then Spec.Keccak.wordAt publicInput (8 * (j - 4)) else 0)))[i]!)
    rw [← perm]
    change (input ⟨Model.Keccak.keccakF1600 initial, default, default, default, default, 0⟩).toSpec = _
    generalize Model.Keccak.keccakF1600 initial = a
    apply Array.ext
    · simp [input, Model.Keccak.State25.toSpec, -Array.getElem_range,
        Proofs.Keccak.range_twenty_five]
    · intro i hi hj
      have bound : i < 25 := by simpa [input, Model.Keccak.State25.toSpec] using hi
      have choices : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
          i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨
          i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 := by omega
      rcases choices with h | h | h | h | h | h | h | h | h | h | h | h |
        h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst i <;>
        simp [input, Model.Keccak.State25.toSpec, -Array.getElem_range,
          Proofs.Keccak.range_twenty_five]
  · rfl

theorem nonceProbe_refines (s : Sponge) (nonce : Spec.Field.E) (h : s.pending ≤ 4) :
    ((nonceProbe s nonce).1, toSpec (nonceProbe s nonce).2) =
      Spec.Transcript.nonceProbe (toSpec s) nonce := by
  have step := sample_refines (absorb s nonce 4)
  rw [absorb_refines s nonce 4 h] at step
  exact step

theorem powBitsOk_refines (s : Sponge) (nonce : Spec.Field.E) (bits : Nat)
    (h : s.pending ≤ 4) :
    powBitsOk s nonce bits = Spec.Transcript.powBitsOk (toSpec s) nonce bits := by
  have step := congrArg Prod.fst (nonceProbe_refines s nonce h)
  unfold powBitsOk Spec.Transcript.powBitsOk
  rw [show (nonceProbe s nonce).1 = (Spec.Transcript.nonceProbe (toSpec s) nonce).1 from step]

theorem verifyPow_refines (s : Sponge) (nonce : Spec.Field.E) (bits : Nat)
    (h : s.pending ≤ 4) :
    ((verifyPow s nonce bits).1, toSpec (verifyPow s nonce bits).2) =
      Spec.Transcript.verifyPow (toSpec s) nonce bits := by
  have step := nonceProbe_refines s nonce h
  have first := congrArg Prod.fst step
  have second := congrArg Prod.snd step
  apply Prod.ext
  · by_cases hz : bits = 0
    · subst bits
      simp only [verifyPow, Spec.Transcript.verifyPow, ite_true]
      congr 1
      apply propext
      constructor
      · intro e
        cases e
        exact ⟨rfl, rfl, rfl⟩
      · intro e
        exact elem_ext _ _ e.1 e.2.1 e.2.2
    · simp only [verifyPow, Spec.Transcript.verifyPow, ite_false,
        beq_iff_eq, hz]
      rw [first]
  · exact second

theorem searchNonce_refines (s : Sponge) (bits fuel : Nat) (start : UInt64)
    (h : s.pending ≤ 4) :
    searchNonce s bits fuel start = Spec.Transcript.searchNonce (toSpec s) bits fuel start := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
    simp only [searchNonce, Spec.Transcript.searchNonce, powBitsOk_refines s _ bits h]

theorem grind_refines (s : Sponge) (bits fuel : Nat) (h : s.pending ≤ 4) :
    (grind s bits fuel).map (fun p => (p.1, toSpec p.2)) =
      Spec.Transcript.powGrinding (toSpec s) bits fuel := by
  unfold grind Spec.Transcript.powGrinding
  by_cases large : bits ≥ 64
  · simp only [large, ite_true, Option.map_none]
  · simp only [large, ite_false]
    rw [searchNonce_refines s bits fuel 0 h]
    by_cases hz : bits = 0
    · subst bits
      change some (0, toSpec (nonceProbe s ⟨0, 0, 0⟩).2) =
        some (0, (Spec.Transcript.nonceProbe (toSpec s) ⟨0, 0, 0⟩).2)
      congr 1
      exact congrArg (fun a => (0, a)) (congrArg Prod.snd (nonceProbe_refines s _ h))
    · simp only [beq_iff_eq, hz, ite_false]
      cases Spec.Transcript.searchNonce (toSpec s) bits fuel 0 with
      | none => rfl
      | some n =>
        change some (n, toSpec (nonceProbe s ⟨n, 0, 0⟩).2) =
          some (n, (Spec.Transcript.nonceProbe (toSpec s) ⟨n, 0, 0⟩).2)
        congr 1
        exact congrArg (fun a => (n, a)) (congrArg Prod.snd (nonceProbe_refines s _ h))

theorem search_first_success (s : Sponge) (bits fuel : Nat) (start nonce : UInt64)
    (domain : s.pending ≤ 4) (found : searchNonce s bits fuel start = some nonce) :
    ∃ k, k < fuel ∧ nonce = Proofs.Transcript.advance k start ∧
      powBitsOk s ⟨nonce, 0, 0⟩ bits = true ∧
      ∀ j, j < k → powBitsOk s ⟨Proofs.Transcript.advance j start, 0, 0⟩ bits = false := by
  rw [searchNonce_refines s bits fuel start domain] at found
  obtain ⟨k, bound, value, good, before⟩ :=
    Proofs.Transcript.search_first_success (toSpec s) bits fuel start nonce found
  refine ⟨k, bound, value, ?_, ?_⟩
  · rw [powBitsOk_refines s _ bits domain]
    exact good
  · intro j hj
    rw [powBitsOk_refines s _ bits domain]
    exact before j hj

theorem zero_bits_grinding_nonce (s : Sponge) (fuel : Nat) :
    (grind s 0 fuel).map Prod.fst = some 0 := by
  rfl

end LeanVmXmss.Proofs.Transcript.Registers
