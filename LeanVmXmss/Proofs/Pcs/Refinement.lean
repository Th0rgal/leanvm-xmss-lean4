import Model.Pcs.Ntt
import Proofs.Field.NativeKernel

namespace LeanVmXmss.Proofs.Pcs

set_option maxHeartbeats 0

open Spec.Field (K)

theorem nativeMul_eq_spec (a b : K) :
    Model.Field.nativeMul a b = Spec.Field.mul a b := by
  rw [Proofs.Field.nativeMul_correct, Proofs.Field.mul_refines_spec]

theorem nativeInv_eq_spec (a : K) :
    Model.Field.nativeInv a = Spec.Field.inv a := by
  rw [Proofs.Field.nativeInv_correct, Proofs.Field.inv_refines_spec]

theorem basis_refines (dim : Nat) :
    Model.Pcs.Ntt.basis dim = Spec.Pcs.Ntt.basis dim := rfl

theorem nextRow_refines (prev : Array K) :
    Model.Pcs.Ntt.nextRow prev = Spec.Pcs.Ntt.nextRow prev := by
  unfold Model.Pcs.Ntt.nextRow Spec.Pcs.Ntt.nextRow
  simp only [nativeMul_eq_spec]

theorem scaleRow_refines (row : Array K) :
    Model.Pcs.Ntt.scaleRow row = Spec.Pcs.Ntt.scaleRow row := by
  unfold Model.Pcs.Ntt.scaleRow Spec.Pcs.Ntt.scaleRow
  dsimp only
  have hfn : Model.Field.nativeMul (Model.Field.nativeInv (row.getD 0 0)) =
      Spec.Field.mul (Spec.Field.inv (row.getD 0 0)) := by
    funext x
    rw [nativeInv_eq_spec, nativeMul_eq_spec]
  rw [hfn]

theorem rowList_refines (dim : Nat) :
    Model.Pcs.Ntt.rowList dim = Spec.Pcs.Ntt.rowList dim := by
  unfold Model.Pcs.Ntt.rowList Spec.Pcs.Ntt.rowList
  rw [basis_refines]
  congr 1
  funext acc _
  cases acc.getLast? <;> simp [nextRow_refines]

theorem evals_refines (dim : Nat) :
    Model.Pcs.Ntt.evals dim = Spec.Pcs.Ntt.evals dim := by
  unfold Model.Pcs.Ntt.evals Spec.Pcs.Ntt.evals
  rw [rowList_refines]
  simp only [scaleRow_refines]

theorem rowFromEvals_refines (dim i : Nat) :
    Model.Pcs.Ntt.rowFromEvals (Model.Pcs.Ntt.evals dim) dim i =
      Spec.Pcs.Ntt.row dim i := by
  unfold Model.Pcs.Ntt.rowFromEvals Spec.Pcs.Ntt.row
  rw [evals_refines]
  rfl

theorem row_refines (dim i : Nat) :
    Model.Pcs.Ntt.row dim i = Spec.Pcs.Ntt.row dim i :=
  rowFromEvals_refines dim i

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

theorem array_range_toList (n : Nat) :
    (Array.range n).toList = List.range' 0 n := by
  unfold Array.range Array.ofFn
  rw [ofFn_go_toList]
  have hemp : (Array.emptyWithCapacity n : Array Nat).toList = [] := rfl
  rw [hemp, List.nil_append, Nat.sub_self]

@[simp] theorem foldRangeLoop_zero {α : Type} (f : α → Nat → α) (idx : Nat) (acc : α) :
    Model.Pcs.Ntt.foldRangeLoop f 0 idx acc = acc := rfl

@[simp] theorem foldRangeLoop_succ {α : Type} (f : α → Nat → α) (rem idx : Nat) (acc : α) :
    Model.Pcs.Ntt.foldRangeLoop f (rem + 1) idx acc =
      Model.Pcs.Ntt.foldRangeLoop f rem (idx + 1) (f acc idx) := by
  unfold Model.Pcs.Ntt.foldRangeLoop
  rw [Fin.foldl_succ]
  simp only [Fin.val_zero, Nat.add_zero]
  congr 1
  funext a k
  simp only [Fin.val_succ]
  have h : idx + (k.val + 1) = idx + 1 + k.val := by omega
  rw [h]

theorem foldRangeLoop_eq_range' {α : Type} (f : α → Nat → α) (rem idx : Nat) (acc : α) :
    Model.Pcs.Ntt.foldRangeLoop f rem idx acc =
      (List.range' idx rem).foldl f acc := by
  induction rem generalizing idx acc with
  | zero => rfl
  | succ rem ih =>
    rw [foldRangeLoop_succ, ih, List.range'_succ, List.foldl_cons]

theorem foldRange_eq {α : Type} (n : Nat) (f : α → Nat → α) (acc : α) :
    Model.Pcs.Ntt.foldRange n f acc = (Array.range n).foldl f acc := by
  unfold Model.Pcs.Ntt.foldRange
  rw [foldRangeLoop_eq_range', ← Array.foldl_toList, array_range_toList]

theorem twiddleLoop_eq_range' (values : Array K) (block rem j : Nat) (acc : K) :
    Model.Pcs.Ntt.twiddleLoop values block rem j acc =
      (List.range' j rem).foldl (fun a i =>
        if Nat.testBit block i then Spec.Field.add a (values.getD (i + 1) 0) else a) acc := by
  unfold Model.Pcs.Ntt.twiddleLoop
  exact foldRangeLoop_eq_range' _ rem j acc

theorem twiddleFromRow_eq (values : Array K) (block : Nat) :
    Model.Pcs.Ntt.twiddleFromRow values block =
      (Array.range (values.size - 1)).foldl (fun acc j =>
        if Nat.testBit block j then Spec.Field.add acc (values.getD (j + 1) 0) else acc) 0 := by
  unfold Model.Pcs.Ntt.twiddleFromRow
  rw [twiddleLoop_eq_range', ← Array.foldl_toList, array_range_toList]

theorem twiddle_refines (dim layer block : Nat) :
    Model.Pcs.Ntt.twiddle dim layer block = Spec.Pcs.Ntt.twiddle dim layer block := by
  unfold Model.Pcs.Ntt.twiddle Spec.Pcs.Ntt.twiddle
  rw [twiddleFromRow_eq, row_refines]

theorem butterfly_refines (top bot t : K) :
    Model.Pcs.Ntt.butterfly top bot t = Spec.Pcs.Ntt.butterfly top bot t := by
  unfold Model.Pcs.Ntt.butterfly Spec.Pcs.Ntt.butterfly
  rw [nativeMul_eq_spec]

theorem encodeLayerWithEvals_refines (data : Array K) (lanes layer logD : Nat) :
    Model.Pcs.Ntt.encodeLayerWithEvals (Model.Pcs.Ntt.evals logD) data lanes layer logD =
      Spec.Pcs.Ntt.encodeLayer data lanes layer logD := by
  unfold Model.Pcs.Ntt.encodeLayerWithEvals Spec.Pcs.Ntt.encodeLayer
  rw [rowFromEvals_refines]
  simp only [foldRange_eq, butterfly_refines, twiddleFromRow_eq]
  rfl

theorem encodeLayer_refines (data : Array K) (lanes layer logD : Nat) :
    Model.Pcs.Ntt.encodeLayer data lanes layer logD =
      Spec.Pcs.Ntt.encodeLayer data lanes layer logD :=
  encodeLayerWithEvals_refines data lanes layer logD

theorem encode_refines (data : Array K) (lanes startLayer : Nat) :
    Model.Pcs.Ntt.encode data lanes startLayer = Spec.Pcs.Ntt.encode data lanes startLayer := by
  unfold Model.Pcs.Ntt.encode Spec.Pcs.Ntt.encode
  simp only [foldRange_eq, encodeLayerWithEvals_refines]

end LeanVmXmss.Proofs.Pcs
