import Proofs.Transcript.Refinement
import Tests.Keccak.Witnesses
import Tests.Merkle.Witnesses

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace LeanVmXmss.Tests.Transcript

def posWitness : Spec.Transcript.Sponge :=
  Spec.Transcript.observe ⟨Spec.Keccak.zero, 0⟩ ⟨7, 8, 9⟩

def negWitness : Spec.Transcript.Sponge :=
  Spec.Transcript.absorb ⟨Spec.Keccak.zero, 0⟩ ⟨7, 8, 9⟩ 0

theorem observe_domain_witness : posWitness.state[3]! = 1 := by decide

theorem missing_domain_witness : posWitness.state[3]! ≠ negWitness.state[3]! := by decide

theorem overwrite_witness :
    (Spec.Transcript.observe ⟨Array.replicate 25 5, 0⟩ ⟨7, 8, 9⟩).state[0]! = 7 := by decide

theorem xor_mutant_witness :
    (Spec.Transcript.observe ⟨Array.replicate 25 5, 0⟩ ⟨7, 8, 9⟩).state[0]! ≠ (5 ^^^ 7 : UInt64) := by decide

theorem insufficient_pow_window_witness :
    (8 : UInt64) &&& Spec.Transcript.mask 3 = 0 ∧ (8 : UInt64) &&& Spec.Transcript.mask 4 ≠ 0 := by decide

end LeanVmXmss.Tests.Transcript
