import Proofs.Layout.Basic

namespace LeanVmXmss.Tests.Layout

open Spec.Field (K E)
open Spec.Layout
open Model.Layout

set_option maxRecDepth 40000
set_option maxHeartbeats 0

def tinyOps : Array Spec.Vm.Op :=
  #[.xor 2 3 4,
    .mul 5 6 7,
    .set 8 ⟨11, 22, 33⟩,
    .deref 2 3 9 .cell,
    .deref 2 1 10 .pc,
    .deref 4 2 11 .fp,
    .jump 2 7 0,
    .keccak #[1, 3, 5, 7] 9 11 13 15 true false]

def posLayout : PublicLayout :=
  buildPublicLayout 16 3 #[0, 1, 2, 3, 4, 5]

def wrongVersionTag : ByteArray :=
  ByteArray.mk #[0x6c, 0x65, 0x61, 0x6e, 0x76, 0x6d, 0x2d, 0x76, 0x30]

def wrongVersionPreimage (table : Array K) : ByteArray :=
  wrongVersionTag ++ wordsBytesFast table

def specIvPreimage (table : Array K) : ByteArray :=
  versionTag ++ wordsBytesFast table

def wrongMinKeccakLog (rows : Fin nTables → Nat) (t : Fin nTables) : Nat :=
  log2Ceil (rows t)

theorem positive_valid_sizes :
    validateSizes 16 3 1 #[0, 1, 2, 3, 4, 5] = true := by
  decide

theorem positive_keccak_floor :
    posLayout.taus[5]? = some 9 := by
  decide

theorem positive_committed_shape :
    posLayout.shape = { mu := 19, nLanes := 38 } ∧ posLayout.placed = 308394 := by
  decide

theorem negative_below_min_mem_rejected :
    validateSizes 15 3 1 #[0, 1, 2, 3, 4, 5] = false := by
  decide

theorem negative_bad_rate_rejected :
    validateSizes 16 3 5 #[0, 1, 2, 3, 4, 5] = false := by
  decide

theorem negative_missing_keccak_floor_mutant :
    wrongMinKeccakLog (fun _ => 5) ⟨5, by decide⟩ ≠
      tableLog (fun _ => 5) ⟨5, by decide⟩ := by
  decide

theorem negative_wrong_version_iv_mutant :
    (wrongVersionPreimage #[0, 1]).data[8]! ≠ (specIvPreimage #[0, 1]).data[8]! := by
  decide

theorem negative_output_lane_uncommitted :
    posLayout.placements[111]? = some none := by
  decide

end LeanVmXmss.Tests.Layout
