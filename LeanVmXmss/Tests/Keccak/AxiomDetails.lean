import Lean
import Proofs.Keccak.Registers
import Proofs.Transcript.Registers
import Proofs.Transcript.Minimality
import Spec.Merkle.Pruned

#print axioms LeanVmXmss.Proofs.Keccak.registers_round_refines_spec
#print axioms LeanVmXmss.Proofs.Keccak.round_constant_refines
#print axioms LeanVmXmss.Proofs.Keccak.registers_rounds_refines
#print axioms LeanVmXmss.Proofs.Transcript.Registers.duplex_refines
#print axioms LeanVmXmss.Proofs.Transcript.Registers.elem_ext
#print axioms LeanVmXmss.Proofs.Transcript.search_first_success
#print axioms Array.ext
#print axioms Array.getElem_setIfInBounds
#print axioms Array.getElem_map

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let name := `LeanVmXmss.Spec.Merkle.verifyPruned
  let some info := env.find? name | throwError "Missing declaration"
  let some value := info.value? true | throwError "Missing proof"
  for dep in value.getUsedConstants do
    let axs ← Lean.collectAxioms dep
    if axs.contains `Classical.choice then logInfo m!"CHOICE_DEP {dep}"
