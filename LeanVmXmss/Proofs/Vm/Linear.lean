import Model.Vm.Linear
import Proofs.Vm.RuntimePowers
import Proofs.Field.NativeKernel

namespace LeanVmXmss.Proofs.Vm

open Spec.Vm
open Spec.Field (E)
open LeanVmXmss.Model.Vm
open LeanVmXmss.Proofs.Field (nativeMul_correct nativeKaratsuba_correct)

set_option maxRecDepth 8192

theorem cellAt_eq_get (m : Memory) (address : Nat) :
    cellAt m.cells address = m.get address := by
  simp only [cellAt, Memory.get]
  split
  · rename_i h
    simp [h]
  · rename_i h
    simp [h]

theorem wordBEq_eq_true_iff (a b : E) : wordBEq a b = true ↔ a = b := by
  cases a with
  | mk a0 a1 a2 =>
    cases b with
    | mk b0 b1 b2 =>
      simp only [wordBEq, Bool.and_eq_true, beq_iff_eq, Spec.Field.E.mk.injEq,
        UInt64.toNat_inj]
      exact ⟨fun ⟨⟨h0, h1⟩, h2⟩ => ⟨h0, h1, h2⟩, fun ⟨h0, h1, h2⟩ => ⟨⟨h0, h1⟩, h2⟩⟩

theorem wordBEq_eq_false_iff (a b : E) : wordBEq a b = false ↔ a ≠ b := by
  cases h : wordBEq a b
  · constructor
    · intro _ heq
      have ht := (wordBEq_eq_true_iff a b).mpr heq
      rw [h] at ht
      contradiction
    · intro _
      rfl
  · constructor
    · intro hf
      contradiction
    · intro hne
      exfalso
      exact hne ((wordBEq_eq_true_iff a b).mp h)

theorem ensureLinear_eq (m : Memory) (address : Nat) :
    ensureLinear m address = m.ensure address := by
  cases m
  rfl

theorem storeLinear_eq (m : Memory) (address : Nat) (value : E) :
    storeLinear m address value = m.store address value := by
  simp only [storeLinear, Memory.store, ensureLinear_eq]
  cases hm : m.ensure address with
  | error fault => rfl
  | ok ensured =>
    cases ensured with
    | mk cells links ur used =>
      dsimp only
      rw [cellAt_eq_get ⟨cells, links, ur, used⟩ address]
      by_cases hw : (Memory.get ⟨cells, links, ur, used⟩ address).written = true
      · by_cases hne : (Memory.get ⟨cells, links, ur, used⟩ address).word ≠ value
        · have hwb : wordBEq (Memory.get ⟨cells, links, ur, used⟩ address).word value = false :=
            (wordBEq_eq_false_iff _ _).mpr hne
          simp [hw, hne, hwb]
        · have heq : (Memory.get ⟨cells, links, ur, used⟩ address).word = value :=
            Decidable.of_not_not hne
          have hwb : wordBEq value value = true := (wordBEq_eq_true_iff value value).mpr rfl
          simp [hw, heq, hwb]
      · simp [hw]

theorem spreadLinear_eq (fuel : Nat) (todo : List Nat) (initial : Memory) (value : E) :
    spreadLinear fuel todo initial value = spread fuel todo initial value := by
  simp only [spreadLinear, spread, cellAt_eq_get, storeLinear_eq]
  rfl

theorem spread_empty_links (address : Nat) (next : Memory) (value : E)
    (hempty : next.links.size = 0) :
    spread 1 [address] next value = .ok next := by
  cases next with
  | mk cells links ur used =>
    have he : links = #[] := Array.eq_empty_of_size_eq_zero hempty
    subst he
    with_unfolding_all rfl

theorem store_preserves_links (m : Memory) (address : Nat) (value : E) (next : Memory)
    (hs : m.store address value = .ok next) : next.links = m.links := by
  simp only [Memory.store] at hs
  cases hm : m.ensure address with
  | error fault => simp [hm] at hs
  | ok ensured =>
    simp only [hm] at hs
    have hel : ensured.links = m.links := by
      simp only [Memory.ensure] at hm
      split at hm
      · simp at hm
      · split at hm <;>
        · injection hm with hm'
          rw [← hm']
    split at hs
    · simp at hs
    · injection hs with hs'
      rw [← hs']
      exact hel

theorem putLinear_eq (m : Memory) (address : Nat) (value : E) :
    putLinear m address value = m.put address value := by
  simp only [putLinear, Memory.put, storeLinear_eq, spreadLinear_eq]
  cases hs : m.store address value with
  | error fault => rfl
  | ok next =>
    dsimp only [bind, Except.bind]
    cases hb : m.links.size == 0
    · rfl
    · have hz : m.links.size = 0 := beq_iff_eq.mp hb
      have hnl : next.links.size = 0 := by
        rw [store_preserves_links m address value next hs]
        exact hz
      rw [if_pos rfl, hz, Nat.zero_add]
      exact (spread_empty_links address next value hnl).symm

theorem readLinear_eq (m : Memory) (address : Nat) :
    readLinear m address = m.read address := by
  simp only [readLinear, Memory.read, ensureLinear_eq, bind, Except.bind]
  cases hm : m.ensure address with
  | error fault => rfl
  | ok ensured =>
    cases ensured with
    | mk cells links ur used =>
      dsimp only
      rw [cellAt_eq_get ⟨cells, links, ur, used⟩ address]
      split <;> rfl

theorem bumpLinear_eq (m : Memory) (address : Nat) :
    bumpLinear m address = m.bump address := by
  simp only [bumpLinear, Memory.bump, ensureLinear_eq, bind, Except.bind]
  cases hm : m.ensure address with
  | error fault => rfl
  | ok ensured =>
    cases ensured with
    | mk cells links ur used =>
      dsimp only
      rw [cellAt_eq_get ⟨cells, links, ur, used⟩ address]

theorem linkLinear_eq (m : Memory) (a b : Nat) :
    linkLinear m a b = m.link a b := by
  cases hm1 : m.ensure a with
  | error fault =>
    simp [linkLinear, Memory.link, ensureLinear_eq, hm1, bind, Except.bind]
  | ok m1 =>
    cases hm2 : m1.ensure b with
    | error fault =>
      simp [linkLinear, Memory.link, ensureLinear_eq, hm1, hm2, bind, Except.bind]
    | ok m2 =>
      cases m2
      simp [linkLinear, Memory.link, ensureLinear_eq, hm1, hm2, bind, Except.bind]

theorem inverseLinear_eq (a : E) : inverseLinear a = Spec.Vm.inverse a := by
  simp only [inverseLinear, Spec.Vm.inverse, nativeKaratsuba_correct]

theorem extendLinear_eq (g : GPow) : extendLinear g = g.extend := by
  cases g with
  | mk powers coarse =>
    simp only [extendLinear, GPow.extend, scalarGeneratorStep_eq, generatorStep]

theorem extendManyLinear_eq (k : Nat) (g : GPow) :
    extendManyLinear k g = GPow.extendMany k g := by
  simp only [extendManyLinear, GPow.extendMany, extendLinear_eq]

theorem growLinear_eq (g : GPow) (n : Nat) : growLinear g n = g.grow n := by
  simp only [growLinear, GPow.grow]
  split
  · rename_i hlt
    have hz : n + 1 - g.powers.size = 0 := by omega
    rw [hz]
    rfl
  · exact extendManyLinear_eq _ g

theorem powerLinear_eq (g : GPow) (n : Nat) : powerLinear g n = g.power n := rfl

theorem logLinear_eq (g : GPow) (value : E) : logLinear g value = g.log value := rfl

theorem heapBaseLinear_raw_eq (m : Memory) (pc fp nextFree : Nat) (g : GPow)
    (cycles : Nat) (counts : Array Nat) (ptr : Nat) :
    heapBaseLinear m.cells fp g ptr =
      heapBase ⟨m, pc, fp, nextFree, g, cycles, counts⟩ ptr := by
  simp only [heapBaseLinear, heapBase, logLinear_eq, cellAt_eq_get]

theorem bitsBaseLinear_raw_eq (m : Memory) (pc fp nextFree : Nat) (g : GPow)
    (cycles : Nat) (counts : Array Nat) (d : BitsDest) :
    bitsBaseLinear m.cells fp g d =
      bitsBase ⟨m, pc, fp, nextFree, g, cycles, counts⟩ d := by
  cases d with
  | stack base => rfl
  | heap ptr => exact heapBaseLinear_raw_eq m pc fp nextFree g cycles counts ptr

theorem countOfLinear_raw_eq (m : Memory) (pc fp nextFree : Nat) (g : GPow)
    (cycles : Nat) (counts : Array Nat) (value : E) (nbits : Nat) :
    countOfLinear g value nbits =
      countOf ⟨m, pc, fp, nextFree, g, cycles, counts⟩ value nbits := rfl

theorem putValuesLinear_spec (m : Memory) (pc fp nextFree : Nat) (g : GPow)
    (cycles : Nat) (counts : Array Nat) (base : Nat) (values : Array E) :
    putValues ⟨m, pc, fp, nextFree, g, cycles, counts⟩ base values =
      (putValuesLinear m base values >>= fun m' =>
        pure ⟨m', pc, fp, nextFree, g, cycles, counts⟩) := by
  have hloop :
      (forIn [:values.size] m fun i __s => do
        let __x ← putLinear __s (base + i) (values[i]?.getD Spec.Field.zero)
        pure (ForInStep.yield __x)) =
      (forIn [:values.size] m fun i __s => do
        let __x ← __s.put (base + i) (values[i]?.getD Spec.Field.zero)
        pure (ForInStep.yield __x)) := by
    simp only [putLinear_eq]
  unfold putValues putValuesLinear
  dsimp only
  rw [hloop]
  cases (forIn [:values.size] m fun i __s => do
    let __x ← __s.put (base + i) (values[i]?.getD Spec.Field.zero)
    pure (ForInStep.yield __x)) <;> rfl

theorem reserveLinear_eq (s : State) (ptr size : Nat) :
    reserveLinear s ptr size = reserve s ptr size := by
  cases s with
  | mk m pc fp nextFree g cycles counts =>
    simp only [reserveLinear, reserve, cellAt_eq_get, growLinear_eq, ensureLinear_eq,
      powerLinear_eq, putLinear_eq]

theorem popWitnessLinear_eq (r : Runtime) (name : String) (base len : Nat) :
    popWitnessLinear r name base len = popWitness r name base len := by
  rcases r with ⟨⟨m, pc, fp, nextFree, g, cycles, counts⟩, streams⟩
  simp only [popWitnessLinear, popWitness, putValuesLinear_spec]
  cases streams.findIdx? (fun stream => stream.name == name) with
  | none => rfl
  | some index =>
    dsimp only [bind, Except.bind]
    cases streams[index]? with
    | none => rfl
    | some stream =>
      dsimp only
      cases stream.entries[stream.next]? with
      | none => rfl
      | some values =>
        dsimp only
        cases values.size != len with
        | true => rfl
        | false =>
          dsimp only [bind, Except.bind, pure, Except.pure]
          cases putValuesLinear m base values <;> rfl

theorem applyHintLinear_eq (h : RHint) (r : Runtime) :
    applyHintLinear h r = applyHint h r := by
  rcases r with ⟨⟨m, pc, fp, nextFree, g, cycles, counts⟩, streams⟩
  cases h with
  | frameAddress offset =>
    simp only [applyHintLinear, applyHint, growLinear_eq]
  | alloc ptr size =>
    simp only [applyHintLinear, applyHint, reserveLinear_eq]
  | allocDyn ptr size =>
    simp only [applyHintLinear, applyHint, cellAt_eq_get,
      countOfLinear_raw_eq m pc fp nextFree g cycles counts, reserveLinear_eq]
  | allocFrames ptr size endOffset startInverse tail =>
    simp only [applyHintLinear, applyHint, cellAt_eq_get, nativeMul_correct,
      countOfLinear_raw_eq m pc fp nextFree g cycles counts, reserveLinear_eq]
  | witnessStack name base len =>
    simp only [applyHintLinear, applyHint, popWitnessLinear_eq]
  | witnessHeap name ptr lo len =>
    simp only [applyHintLinear, applyHint,
      heapBaseLinear_raw_eq m pc fp nextFree g cycles counts, popWitnessLinear_eq]
  | log2Ceil bits dst nbits floor =>
    simp only [applyHintLinear, applyHint,
      bitsBaseLinear_raw_eq m pc fp nextFree g cycles counts, cellAt_eq_get,
      putValuesLinear_spec, bind, Except.bind, pure, Except.pure]
    cases bitsBase ⟨m, pc, fp, nextFree, g, cycles, counts⟩ bits with
    | error fault => rfl
    | ok base =>
      dsimp only
      cases (forIn [:nbits] 0 fun i value =>
        if (!wordBEq (m.get (base + i)).word Spec.Field.zero) = true then
          Except.ok (ForInStep.yield (value ||| 1 <<< i))
        else Except.ok (ForInStep.yield value)) with
      | error fault => rfl
      | ok val =>
        dsimp only
        cases putValuesLinear m (fp + dst)
          #[Spec.Xmss.count (max (if val ≤ 1 then 0 else (val - 1).log2 + 1) floor)] <;> rfl
  | bitDecompose value bits nbits start =>
    simp only [applyHintLinear, applyHint,
      bitsBaseLinear_raw_eq m pc fp nextFree g cycles counts, cellAt_eq_get,
      putValuesLinear_spec, bind, Except.bind, pure, Except.pure]
    by_cases hgt : start + nbits > 192
    · simp only [hgt, ↓reduceIte]
      rfl
    · simp only [hgt, ↓reduceIte]
      cases bitsBase ⟨m, pc, fp, nextFree, g, cycles, counts⟩ bits with
      | error fault => rfl
      | ok base =>
        dsimp only
        cases putValuesLinear m base
          ((Array.range nbits).map fun i =>
            Spec.Field.embed (if (limbsInteger (m.get (fp + value)).word).testBit (start + i) then 1 else 0)) <;> rfl
  | bitDecomposeExp value bits nbits =>
    simp only [applyHintLinear, applyHint,
      countOfLinear_raw_eq m pc fp nextFree g cycles counts,
      bitsBaseLinear_raw_eq m pc fp nextFree g cycles counts, cellAt_eq_get,
      putValuesLinear_spec, bind, Except.bind, pure, Except.pure]
    cases countOf ⟨m, pc, fp, nextFree, g, cycles, counts⟩ (m.get (fp + value)).word nbits with
    | error fault => rfl
    | ok integer =>
      dsimp only
      cases bitsBase ⟨m, pc, fp, nextFree, g, cycles, counts⟩ bits with
      | error fault => rfl
      | ok base =>
        dsimp only
        cases putValuesLinear m base
          ((Array.range nbits).map fun i => Spec.Field.embed (if integer.testBit i then 1 else 0)) <;> rfl
  | digitDecomposeExp value dst nbits ndigits digitBits start startCell =>
    simp only [applyHintLinear, applyHint,
      countOfLinear_raw_eq m pc fp nextFree g cycles counts,
      bitsBaseLinear_raw_eq m pc fp nextFree g cycles counts, cellAt_eq_get,
      putValuesLinear_spec, bind, Except.bind, pure, Except.pure]
    cases countOf ⟨m, pc, fp, nextFree, g, cycles, counts⟩ (m.get (fp + value)).word nbits with
    | error fault => rfl
    | ok integer =>
      dsimp only
      cases startCell with
      | none =>
        dsimp only
        cases bitsBase ⟨m, pc, fp, nextFree, g, cycles, counts⟩ dst with
        | error fault => rfl
        | ok base =>
          dsimp only
          cases putValuesLinear m base
            ((Array.range ndigits).map fun i =>
              Spec.Xmss.count ((integer >>> (start + digitBits * i)) % 2 ^ digitBits)) <;> rfl
      | some offset =>
        dsimp only
        cases countOf ⟨m, pc, fp, nextFree, g, cycles, counts⟩ (m.get (fp + offset)).word 7 with
        | error fault => rfl
        | ok start' =>
          dsimp only
          cases bitsBase ⟨m, pc, fp, nextFree, g, cycles, counts⟩ dst with
          | error fault => rfl
          | ok base =>
            dsimp only
            cases putValuesLinear m base
              ((Array.range ndigits).map fun i =>
                Spec.Xmss.count ((integer >>> (start' + digitBits * i)) % 2 ^ digitBits)) <;> rfl
  | windowsExp value dest offset start width count =>
    simp only [applyHintLinear, applyHint,
      bitsBaseLinear_raw_eq m pc fp nextFree g cycles counts, cellAt_eq_get,
      putValuesLinear_spec, bind, Except.bind, pure, Except.pure]
    by_cases hgt : start + width * count > 192
    · simp only [hgt, ↓reduceIte]
      rfl
    · simp only [hgt, ↓reduceIte]
      cases bitsBase ⟨m, pc, fp, nextFree, g, cycles, counts⟩ dest with
      | error fault => rfl
      | ok base =>
        dsimp only
        cases putValuesLinear m (base + offset)
          ((Array.range count).map fun i =>
            Spec.Xmss.count (((limbsInteger (m.get (fp + value)).word) >>> (start + width * i)) % 2 ^ width)) <;> rfl
  | fieldLimbs value base len =>
    simp only [applyHintLinear, applyHint, cellAt_eq_get,
      putValuesLinear_spec, bind, Except.bind, pure, Except.pure]
    split
    · rfl
    · cases putValuesLinear m (fp + base)
        ((#[(m.get (fp + value)).word.c0, (m.get (fp + value)).word.c1,
          (m.get (fp + value)).word.c2].extract 0 len).map Spec.Field.embed) with
      | error fault => rfl
      | ok m' => rfl
  | inverse value dst =>
    simp only [applyHintLinear, applyHint, cellAt_eq_get, inverseLinear_eq,
      putValuesLinear_spec, bind, Except.bind, pure, Except.pure]
    cases putValuesLinear m (fp + dst) #[Spec.Vm.inverse (m.get (fp + value)).word] <;> rfl
  | print label cell =>
    rfl

theorem applyHintsLinear_eq (hints : Array RHint) (r : Runtime) :
    applyHintsLinear hints r = applyHints hints r := by
  simp only [applyHintsLinear, applyHints]
  have hfun : (fun r hint => applyHintLinear hint r) = (fun r hint => applyHint hint r) := by
    funext r hint
    exact applyHintLinear_eq hint r
  rw [hfun]

theorem stepBodyLinear_eq (op : Op) (m : Memory) (oldPc oldFp nextFree : Nat)
    (sg : GPow) (cycles : Nat) (opcodeCounts : Array Nat) (g : GPow) :
    stepBodyLinear op m oldPc oldFp opcodeCounts g =
      stepBody op ⟨m, oldPc, oldFp, nextFree, sg, cycles, opcodeCounts⟩ g := by
  simp only [stepBodyLinear, stepBody, putLinear_eq, readLinear_eq, bumpLinear_eq,
    linkLinear_eq, logLinear_eq, powerLinear_eq, inverseLinear_eq, cellAt_eq_get,
    nativeKaratsuba_correct]
  rfl

theorem stepLinear_eq (op : Op) (s : State) :
    stepLinear op s = Spec.Vm.step op s := by
  cases s with
  | mk m oldPc oldFp nextFree g cycles opcodeCounts =>
    simp only [stepLinear, Spec.Vm.step, Spec.Vm.stepWithPowers, growLinear_eq,
      stepBodyLinear_eq op m oldPc oldFp nextFree g cycles opcodeCounts]

theorem scheduledRunLinear_eq (fuel : Nat) (program : Array Op) (hints : Array (Array RHint))
    (r : Runtime) :
    scheduledRunLinear fuel program hints r = scheduledRun fuel program hints r := by
  have hstep : (fun op ready => stepLinear op ready) = (fun op ready => Model.Vm.step op ready) := by
    funext op ready
    rw [stepLinear_eq, step_refines_spec]
  simp only [scheduledRunLinear, scheduledRun, applyHintsLinear_eq, hstep]
  rfl

end LeanVmXmss.Proofs.Vm
