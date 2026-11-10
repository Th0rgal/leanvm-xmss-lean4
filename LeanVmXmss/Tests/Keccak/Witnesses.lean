import Proofs.Keccak.Refinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LeanVmXmss.Tests.Keccak

theorem posWitness : (Spec.Keccak.finalBlock ByteArray.empty)[0]! = 1 := by decide

theorem negWitness : (Spec.Keccak.finalBlock ByteArray.empty 6)[0]! ≠
    (Spec.Keccak.finalBlock ByteArray.empty 1)[0]! := by decide

theorem final_bit_witness : (Spec.Keccak.finalBlock ByteArray.empty)[135]! = 128 := by decide

theorem boundary_padding_witness :
    (Spec.Keccak.finalBlock (ByteArray.mk (Array.replicate 135 0)))[135]! = 129 := by decide

end LeanVmXmss.Tests.Keccak
