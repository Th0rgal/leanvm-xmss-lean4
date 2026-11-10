import Spec.Vm.Basic
import Model.Vm.Kernel
import Proofs.Vm.Kernel
import Proofs.Field.Powers
import Proofs.Field.Reduction
import Proofs.Field.Extension

namespace LeanVmXmss.Proofs.Vm

open Model.Vm

def generatorStep (x : UInt64) : UInt64 :=
  (x <<< 1) ^^^ (if x.toNat / 2^63 == 0 then 0 else 0x1b)

def generatorLoop : Nat → UInt64 → UInt64 :=
  Nat.rec (motive := fun _ => UInt64 → UInt64) (fun x => x)
    (fun _ previous x => previous (generatorStep x))

theorem generatorLoop_add (m n : Nat) (x : UInt64) :
    generatorLoop (m+n) x = generatorLoop n (generatorLoop m x) := by
  induction m generalizing x with
  | zero => rw [Nat.zero_add]; rfl
  | succ m ih => simpa [Nat.succ_add, generatorLoop] using ih (generatorStep x)

theorem generatorLoop_step (n : Nat) (x : UInt64) :
    generatorLoop n (generatorStep x) = generatorStep (generatorLoop n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simpa [generatorLoop] using ih (generatorStep x)

theorem generatorLoop_count (n : Nat) : generatorLoop n 1 = Spec.Xmss.gpow n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change generatorLoop n (generatorStep 1) = _
    rw [generatorLoop_step, ih]
    rfl

theorem gpow_add (m n : Nat) :
    Spec.Xmss.gpow (m+n) = generatorLoop n (Spec.Xmss.gpow m) := by
  rw [← generatorLoop_count, generatorLoop_add, generatorLoop_count]

theorem scalarGeneratorStep_eq (x : UInt64) :
    Model.Vm.scalarGeneratorStep x = generatorStep x :=
  scalarGeneratorStep_spec x

theorem generatorStep_eq_mul_two (x : UInt64) :
    generatorStep x = Model.Field.mul x 2 := by
  refine Eq.trans ?_ (Proofs.Field.mul_monomial x 1 (by decide)).symm
  unfold Model.Field.reduce generatorStep
  have hlo : ((x.toBitVec.setWidth 128 <<< 1).setWidth 64) = x.toBitVec <<< 1 := by
    apply BitVec.eq_of_toNat_eq
    have hx : x.toNat * 2 < 2 ^ 128 := by
      have h64 : x.toNat < 2 ^ 64 := x.toNat_lt
      omega
    simp [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hx]
  have hhi_nat : (((x.toBitVec.setWidth 128 <<< 1) >>> 64).setWidth 64).toNat = x.toNat / 2 ^ 63 := by
    have h64 : x.toNat < 2 ^ 64 := x.toNat_lt
    have hx : x.toNat * 2 < 2 ^ 128 := by omega
    have hdiv : (x.toNat * 2) / 2 ^ 64 = x.toNat / 2 ^ 63 := by omega
    have hlt : x.toNat / 2 ^ 63 < 2 ^ 64 := by omega
    simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hx, hdiv, Nat.mod_eq_of_lt hlt]
  by_cases h : x.toNat / 2 ^ 63 = 0
  · have hhi : ((x.toBitVec.setWidth 128 <<< 1) >>> 64).setWidth 64 = 0 := by
      apply BitVec.eq_of_toNat_eq
      simpa [h] using hhi_nat
    have hb : (x.toNat / 2 ^ 63 == 0) = true := beq_iff_eq.mpr h
    rw [hlo, hhi, hb]
    simp
  · have h1 : x.toNat / 2 ^ 63 = 1 := by
      have h64 : x.toNat < 2 ^ 64 := x.toNat_lt
      omega
    have hhi : ((x.toBitVec.setWidth 128 <<< 1) >>> 64).setWidth 64 = 1 := by
      apply BitVec.eq_of_toNat_eq
      simpa [h1] using hhi_nat
    have hb : (x.toNat / 2 ^ 63 == 0) = false := beq_false_of_ne h
    have hc :
        (let spill := ((1 : BitVec 64) >>> 63) ^^^ ((1 : BitVec 64) >>> 61) ^^^ ((1 : BitVec 64) >>> 60)
         let v := (1 : BitVec 64) ^^^ spill
         v ^^^ (v <<< 1) ^^^ (v <<< 3) ^^^ (v <<< 4)) = (0x1b : BitVec 64) := by decide
    rw [hlo, hhi, hb]
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply UInt64.toBitVec_inj.mp
    simpa [BitVec.xor_assoc] using congrArg (fun w => (x.toBitVec <<< 1) ^^^ w) hc

theorem gpow_eq_pow (n : Nat) :
    Spec.Xmss.gpow n = Model.Field.pow (2 : Spec.Field.K) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change generatorStep (Spec.Xmss.gpow n) = Model.Field.mul (Model.Field.pow 2 n) 2
    rw [ih]
    exact generatorStep_eq_mul_two (Model.Field.pow 2 n)

theorem gpow_mul (m n : Nat) :
    Spec.Xmss.gpow (m + n) =
      Spec.Field.mul (Spec.Xmss.gpow m) (Spec.Xmss.gpow n) := by
  rw [gpow_eq_pow, gpow_eq_pow, gpow_eq_pow, Proofs.Field.pow_add,
    Proofs.Field.mul_refines_spec]

theorem count_mul (m n : Nat) :
    Spec.Xmss.count (m + n) =
      Spec.Field.emul (Spec.Xmss.count m) (Spec.Xmss.count n) := by
  change Spec.Field.embed (Spec.Xmss.gpow (m + n)) =
    Spec.Field.emul (Spec.Field.embed (Spec.Xmss.gpow m)) (Spec.Field.embed (Spec.Xmss.gpow n))
  rw [Proofs.Field.embed_mul, gpow_mul]

theorem power_out_of_bounds (g : Spec.Vm.GPow) (n : Nat) (h : g.powers.size ≤ n) :
    g.power n = .error .badProgram := by
  simp [Spec.Vm.GPow.power, Array.getElem?_eq_none h]

theorem power_refines_count (g : Spec.Vm.GPow) (n : Nat)
    (h : g.powers[n]? = some (Spec.Xmss.gpow n)) :
    g.power n = .ok (Spec.Xmss.count n) := by
  simp [Spec.Vm.GPow.power, h, Spec.Xmss.count]

def PowersValid (g : Spec.Vm.GPow) : Prop :=
  0 < g.powers.size ∧ ∀ i, i < g.powers.size → g.powers[i]? = some (Spec.Xmss.gpow i)

theorem array_push_lookup {α : Type} (xs : Array α) (x : α) (i : Nat) :
    (xs.push x)[i]? = if i = xs.size then some x else xs[i]? := by
  by_cases hi : i < xs.size
  · have hp : i < (xs.push x).size := by simpa only [Array.size_push] using Nat.lt_succ_of_lt hi
    rw [getElem?_pos (xs.push x) i hp, Array.getElem_push, dite_eq_left hi,
      ite_eq_right (Nat.ne_of_lt hi), getElem?_pos xs i hi]
  · by_cases he : i = xs.size
    · subst i
      rw [getElem?_pos (xs.push x) xs.size (by simp only [Array.size_push]; omega),
        Array.getElem_push_eq, ite_eq_left rfl]
    · have hp : ¬ i < (xs.push x).size := by rw [Array.size_push]; omega
      rw [getElem?_neg (xs.push x) i hp, ite_eq_right he, getElem?_neg xs i hi]

theorem extend_size (g : Spec.Vm.GPow) : g.extend.powers.size = g.powers.size+1 := by
  simp [Spec.Vm.GPow.extend]

theorem extend_valid (g : Spec.Vm.GPow) (h : PowersValid g) : PowersValid g.extend := by
  have positive : 0 < g.powers.size := h.1
  constructor
  · rw [extend_size]; omega
  · intro i hi
    rw [extend_size] at hi
    by_cases he : i < g.powers.size
    · simpa [Spec.Vm.GPow.extend, array_push_lookup, he, Nat.ne_of_lt he] using h.2 i he
    · have eq : i = g.powers.size := by omega
      subst i
      have last := h.2 (g.powers.size-1) (by omega)
      have back : g.powers.back?.getD 1 = Spec.Xmss.gpow (g.powers.size-1) := by
        simpa [Array.back?, Nat.ne_of_gt positive] using congrArg (fun x => x.getD 1) last
      simp only [Spec.Vm.GPow.extend, array_push_lookup, ↓reduceIte]
      have sizeEq : g.powers.size = (g.powers.size-1)+1 := by omega
      rw [back]
      have recurrence : Spec.Xmss.gpow g.powers.size =
          (Spec.Xmss.gpow (g.powers.size-1) <<< 1) ^^^
            (if (Spec.Xmss.gpow (g.powers.size-1)).toNat / 2^63 == 0 then 0 else 0x1b) := by
        exact congrArg Spec.Xmss.gpow sizeEq
      exact congrArg some recurrence.symm

theorem extendMany_valid (k : Nat) (g : Spec.Vm.GPow) (h : PowersValid g) :
    PowersValid (Spec.Vm.GPow.extendMany k g) := by
  induction k generalizing g with
  | zero => exact h
  | succ k ih => exact ih g.extend (extend_valid g h)

theorem extendMany_size (k : Nat) (g : Spec.Vm.GPow) :
    (Spec.Vm.GPow.extendMany k g).powers.size = g.powers.size+k := by
  induction k generalizing g with
  | zero => change g.powers.size = g.powers.size + 0; omega
  | succ k ih =>
    change (Spec.Vm.GPow.extendMany k g.extend).powers.size = g.powers.size + (k+1)
    rw [ih, extend_size]
    omega

theorem grow_covers (g : Spec.Vm.GPow) (n i : Nat) (h : PowersValid g) (hi : i ≤ n) :
    (g.grow n).power i = .ok (Spec.Xmss.count i) := by
  apply power_refines_count
  apply (extendMany_valid (n+1-g.powers.size) g h).2
  rw [extendMany_size]
  omega

theorem power_mul (g : Spec.Vm.GPow) (m n : Nat) (h : PowersValid g)
    (hmn : m + n < g.powers.size) :
    g.power (m + n) = (do
      let pm ← g.power m
      let pn ← g.power n
      pure (Spec.Field.emul pm pn)) := by
  have hm : m < g.powers.size := by omega
  have hn : n < g.powers.size := by omega
  rw [power_refines_count g (m + n) (h.2 (m + n) hmn),
    power_refines_count g m (h.2 m hm),
    power_refines_count g n (h.2 n hn)]
  exact congrArg Except.ok (count_mul m n)

theorem default_powers_valid : PowersValid ({} : Spec.Vm.GPow) := by
  constructor
  · decide
  · intro i hi
    have eq : i = 0 := by simpa using hi
    subst i
    rfl

theorem grow_valid (g : Spec.Vm.GPow) (n : Nat) (h : PowersValid g) :
    PowersValid (g.grow n) :=
  extendMany_valid (n+1-g.powers.size) g h

theorem frame_power_coverage (g : Spec.Vm.GPow) (pc fp : Nat) (h : PowersValid g) :
    (g.grow (max (pc+2) fp)).power (pc+2) = .ok (Spec.Xmss.count (pc+2)) ∧
    (g.grow (max (pc+2) fp)).power fp = .ok (Spec.Xmss.count fp) := by
  exact ⟨grow_covers g _ _ h (Nat.le_max_left _ _),
    grow_covers g _ _ h (Nat.le_max_right _ _)⟩

theorem allocation_power_coverage (g : Spec.Vm.GPow) (nextFree size : Nat)
    (h : PowersValid g) :
    (g.grow (nextFree+size)).power nextFree = .ok (Spec.Xmss.count nextFree) := by
  apply grow_covers g _ _ h
  omega

theorem initial_table_coverage (programSize mainFrame i : Nat)
    (hi : i ≤ max (programSize+2) (max mainFrame 65536)) :
    (({} : Spec.Vm.GPow).grow (max (programSize+2) (max mainFrame 65536))).power i =
      .ok (Spec.Xmss.count i) := by
  exact grow_covers _ _ _ default_powers_valid hi

end LeanVmXmss.Proofs.Vm
