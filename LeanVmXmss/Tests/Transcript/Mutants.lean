import Proofs.Transcript.Registers
import Model.Merkle.Scalar

namespace LeanVmXmss.Tests.Transcript.Mutants

def run : IO Unit := do
  let check := fun (label : String) (different : Bool) =>
    if different then IO.println label else throw (IO.userError label)
  check "mutant_sha3_domain"
    (Spec.Keccak.keccak256 "abc".toUTF8 != Spec.Keccak.hashWithDomain "abc".toUTF8 6)
  let left := Model.Merkle.hashRow #[1, 11] 5
  let right := Model.Merkle.hashRow #[2, 22] 5
  let root := Model.Merkle.compress left right
  check "mutant_swapped_children"
    (Model.Merkle.verifyPath root left 0 [right] &&
      !Model.Merkle.verifyPath (Model.Merkle.compress right left) left 0 [right])
  let seed := Model.Transcript.Registers.init "iv".toUTF8 "public".toUTF8
  let tagged := Model.Transcript.Registers.observe seed ⟨7, 8, 9⟩
  let missing := Model.Transcript.Registers.absorb seed ⟨7, 8, 9⟩ 0
  let challenge := (Model.Transcript.Registers.sample tagged).1
  let badChallenge := (Model.Transcript.Registers.sample missing).1
  check "mutant_missing_observe_domain"
    (challenge.c0.toNat != badChallenge.c0.toNat || challenge.c1.toNat != badChallenge.c1.toNat ||
      challenge.c2.toNat != badChallenge.c2.toNat)
  let occupied := Model.Transcript.Registers.observe seed ⟨5, 6, 7⟩
  let reused := {occupied with pending := 0}
  let correct := Model.Transcript.Registers.observe reused ⟨7, 8, 9⟩
  let input := Model.Transcript.Registers.toSpec occupied
  let xorState := (((input.state.set! 0 (input.state[0]! ^^^ 7)).set! 1
    (input.state[1]! ^^^ 8)).set! 2 (input.state[2]! ^^^ 9)).set! 3 1
  let xorChallenge := (Spec.Transcript.challenge ⟨xorState, 1⟩).1
  let overwriteChallenge := (Model.Transcript.Registers.sample correct).1
  check "mutant_xor_instead_of_overwrite"
    (overwriteChallenge.c0.toNat != xorChallenge.c0.toNat ||
      overwriteChallenge.c1.toNat != xorChallenge.c1.toNat ||
      overwriteChallenge.c2.toNat != xorChallenge.c2.toNat)
  let some weak := Model.Transcript.Registers.searchNonce tagged 1 100000 0
    | throw (IO.userError "weak_nonce_search_exhausted")
  check "mutant_insufficient_pow"
    ((Model.Transcript.Registers.verifyPow tagged ⟨weak, 0, 0⟩ 1).1 &&
      !(Model.Transcript.Registers.verifyPow tagged ⟨weak, 0, 0⟩ 8).1)
  check "zero_bits_noncanonical_rejected"
    (!(Model.Transcript.Registers.verifyPow tagged ⟨1, 0, 0⟩ 0).1 &&
      (Model.Transcript.Registers.verifyPow tagged ⟨0, 0, 0⟩ 0).1)

end LeanVmXmss.Tests.Transcript.Mutants

#eval LeanVmXmss.Tests.Transcript.Mutants.run
