import Model.KeccakGkr.Flat
namespace LeanVmXmss.Proofs.KeccakGkr
open Model.KeccakGkr
open Model.Field (eadd nativeKaratsuba)
open Model.Pcs.Ntt (foldRange)
open Spec.Field (E)
open Spec.KeccakGkr (bitCount)
/-- Fold pairs of rows from `tape.cur` into `tape.nxt` in place, then swap buffers. -/
@[noinline] def foldRowsReference (tape : RoundETape) (activeRows : Nat) (challenge : E) :
    RoundETape :=
  let half := activeRows / 2
  let nxt := foldRange half
    (fun dst index =>
      let lowBase := (2 * index) * bitCount
      let highBase := (2 * index + 1) * bitCount
      let dstBase := index * bitCount
      foldRange bitCount
        (fun inner pos =>
          let lo := planarEGet tape.cur (lowBase + pos)
          let hi := planarEGet tape.cur (highBase + pos)
          planarESet inner (dstBase + pos) (eadd lo (nativeKaratsuba challenge (eadd lo hi))))
        dst)
    tape.nxt
  ⟨nxt, tape.cur⟩

/-- Exact prior semantics for every tape, including aliases and truncated buffers. -/
theorem foldRowsFlat_refines_reference (tape : RoundETape) (activeRows : Nat) (challenge : E) :
    foldRowsFlat tape activeRows challenge = foldRowsReference tape activeRows challenge := by
  cases tape
  rfl
end LeanVmXmss.Proofs.KeccakGkr
