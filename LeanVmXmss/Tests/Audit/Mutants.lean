/-
W5 Maxwell · Negative mutants & 34-mutant soundness suite for LeanVmXmss
=========================================================================
1. `run` (preserved): Wave 1 Category 4 interpreter negative mutants (executed via `#eval`).
2. `runMutantSuite34`: Wave 3 34-mutant end-to-end soundness harness over the pure-Lean
   verifier (`Model.Aggregate.Verify.verifyEthereumBytes`, refined to `Spec.Aggregate.Verify`),
   mirroring the 34 deterministic mutations checked by the unmodified Rust verifier.
-/
import Spec.Vm.Basic
import Model.Vm.Interpreter
import Model.Cli.Inputs
import Model.Cli.E2E
import Model.Aggregate.Verify

namespace LeanVmXmss.Tests.Audit.Mutants

open LeanVmXmss.Spec.Vm
open LeanVmXmss.Model.Vm

abbrev E := Spec.Field.E

def v (x : UInt64) : E := ⟨x, 0, 0⟩
def k (n : Nat) : E := ⟨(2^n : UInt64), 0, 0⟩

def runProgram (fuel : Nat) (program : Array Op) (pi : Array E) : Except Fault State :=
  match initial 2 pi program.size with
  | .error f => .error f
  | .ok s => run fuel program s

def jsonEscape (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\"" "\\\"" |>.replace "\n" "\\n"

structure Mutant where
  name : String
  rejected : Bool
  detail : String

def mutantJson (_m : Mutant) : String :=
  "{\"name\":\"" ++ jsonEscape _m.name ++ "\",\"rejected\":" ++
    (if _m.rejected then "true" else "false") ++
    ",\"detail\":\"" ++ jsonEscape _m.detail ++ "\"}"

def run : IO Unit := do
  let baseProgram : Array Op := #[.set 2 (v 5), .xor 0 2 3, .set 4 (v 9)]
  match runProgram 16 baseProgram #[v 7, v 2] with
  | .error f => throw (IO.userError s!"w5-4 baseline faulted: {repr f}")
  | .ok baseState =>
    let baseWord := baseState.memory.get 3 |>.word
    if baseWord.c0 != 2 then
      throw (IO.userError s!"w5-4 baseline mem[3].c0 = {baseWord.c0} (expected 2)")
    let mut out : Array String := #[]
    let mut failures : Nat := 0

    let semProgram : Array Op := #[.set 2 (v 5), .mul 0 2 3, .set 4 (v 9)]
    match runProgram 16 semProgram #[v 7, v 2] with
    | .error f =>
      out := out.push (mutantJson ⟨"c4a_opcode_mul_replaces_xor", false, s!"unexpected fault {repr f}"⟩)
      failures := failures + 1
    | .ok s =>
      let w := s.memory.get 3 |>.word
      if w.c0 != baseWord.c0 then
        out := out.push (mutantJson ⟨"c4a_opcode_mul_replaces_xor", true, s!"honest={baseWord.c0} mutated={w.c0}"⟩)
      else
        out := out.push (mutantJson ⟨"c4a_opcode_mul_replaces_xor", false, "result unchanged"⟩)
        failures := failures + 1

    let arityProgram : Array Op := #[.keccak #[0, 1, 2] 13 26 39 52 false false, .set 2 (v 5)]
    match runProgram 16 arityProgram #[v 7, v 2] with
    | .error f =>
      if f == Fault.badProgram then
        out := out.push (mutantJson ⟨"c4a_keccak_arity_bad_program", true, "fault badProgram"⟩)
      else
        out := out.push (mutantJson ⟨"c4a_keccak_arity_bad_program", false, s!"wrong fault {repr f}"⟩)
        failures := failures + 1
    | .ok _ =>
      out := out.push (mutantJson ⟨"c4a_keccak_arity_bad_program", false, "ran to completion"⟩)
      failures := failures + 1

    let freeProgram : Array Op := #[.set 2 (v 5), .xor 4 4 3, .set 5 (v 9)]
    match runProgram 16 freeProgram #[v 7, v 2] with
    | .error f =>
      out := out.push (mutantJson ⟨"c4b_unconstrained_read", false, s!"unexpected fault {repr f}"⟩)
      failures := failures + 1
    | .ok s =>
      let reads := s.memory.unconstrainedReads
      if reads.size == 1 && reads[0]? == some 4 then
        out := out.push (mutantJson ⟨"c4b_unconstrained_read", true, s!"unconstrainedReads=[4] size={reads.size}"⟩)
      else
        out := out.push (mutantJson ⟨"c4b_unconstrained_read", false, s!"unconstrainedReads size={reads.size}"⟩)
        failures := failures + 1

    let badPcProgram : Array Op := #[.set 2 (v 5), .jump 1 1 0, .xor 0 2 3]
    match runProgram 16 badPcProgram #[v 1, k 6] with
    | .error f =>
      if f == Fault.badProgram then
        out := out.push (mutantJson ⟨"c4c_jump_out_of_range", true, "fault badProgram"⟩)
      else
        out := out.push (mutantJson ⟨"c4c_jump_out_of_range", false, s!"wrong fault {repr f}"⟩)
        failures := failures + 1
    | .ok _ =>
      out := out.push (mutantJson ⟨"c4c_jump_out_of_range", false, "ran to completion"⟩)
      failures := failures + 1

    let loopProgram : Array Op := #[.jump 0 1 0, .set 9 (v 0)]
    match runProgram 10 loopProgram #[v 1, v 1] with
    | .error f =>
      if f == Fault.stepLimit then
        out := out.push (mutantJson ⟨"c4c_jump_loop_step_limit", true, "fault stepLimit"⟩)
      else
        out := out.push (mutantJson ⟨"c4c_jump_loop_step_limit", false, s!"wrong fault {repr f}"⟩)
        failures := failures + 1
    | .ok _ =>
      out := out.push (mutantJson ⟨"c4c_jump_loop_step_limit", false, "ran to completion"⟩)
      failures := failures + 1

    if failures != 0 then throw (IO.userError s!"w5-4: {failures} category-4 mutant(s) accepted")
    let envOut ← IO.getEnv "W5_AUDIT_OUT"
    let envTmp ← IO.getEnv "TMPDIR"
    let dir := envOut.getD (envTmp.getD "/tmp/w5-audit")
    IO.FS.createDirAll (System.FilePath.mk dir)
    let json := "{\"shard\":\"W5\",\"category\":4,\"baseline\":{\"program\":\"set-xor-set\",\"mem3\":2},\"mutant_count\":" ++
      toString out.size ++ ",\"accepted_count\":0,\"all_rejected\":true,\"mutants\":[" ++
      String.intercalate "," out.toList ++ "]}\n"
    IO.FS.writeFile (System.FilePath.mk (dir ++ "/mutants-lean.json")) json
    IO.println s!"W5_LEAN_MUTANTS_DONE path={dir}/mutants-lean.json"

/-! ### Wave 3: Deterministic 34-Mutant End-to-End Soundness Suite -/

structure SoundnessMutantSpec where
  id : Nat
  group : String
  name : String
  mutate : ByteArray → Spec.Aggregate.Wire.EthereumProof → ByteArray

structure SoundnessMutantResult where
  id : Nat
  group : String
  name : String
  baselineAccepted : Bool
  mutatedRejected : Bool
  mutatedBytes : Nat

def flipByteAt (b : ByteArray) (idx : Nat) (mask : UInt8 := 1) : ByteArray :=
  if idx < b.size then
    b.set! idx ((b.get! idx) ^^^ mask)
  else
    b

def setStreamElem (eth : Spec.Aggregate.Wire.EthereumProof) (idx : Nat) (f : E → E) :
    ByteArray :=
  let s := eth.proof.stream
  let v0 := s.getD idx Spec.Field.zero
  let s' := s.setIfInBounds idx (f v0)
  Spec.Aggregate.Wire.EthereumProof.toBytes { eth with proof := { eth.proof with stream := s' } }

def swapStreamElems (eth : Spec.Aggregate.Wire.EthereumProof) (i j : Nat) : ByteArray :=
  let s := eth.proof.stream
  let vi := s.getD i Spec.Field.zero
  let vj := s.getD j Spec.Field.zero
  let s' := (s.setIfInBounds i vj).setIfInBounds j vi
  Spec.Aggregate.Wire.EthereumProof.toBytes { eth with proof := { eth.proof with stream := s' } }

def rotateStreamLeft1 (eth : Spec.Aggregate.Wire.EthereumProof) : ByteArray :=
  let s := eth.proof.stream
  let s' :=
    if s.isEmpty then s
    else (s.extract 1 s.size).push (s.getD 0 Spec.Field.zero)
  Spec.Aggregate.Wire.EthereumProof.toBytes { eth with proof := { eth.proof with stream := s' } }

def flipMerkleLeafWord (eth : Spec.Aggregate.Wire.EthereumProof) (batch rowIdx wordIdx : Nat) :
    ByteArray :=
  let m := eth.proof.merkle
  let ph := m.getD batch ⟨#[], #[]⟩
  let row := ph.rows.getD rowIdx #[]
  let w0 := row.getD wordIdx 0
  let row' := row.setIfInBounds wordIdx (w0 ^^^ 1)
  let ph' : Spec.Merkle.PrunedMerklePaths := { ph with rows := ph.rows.setIfInBounds rowIdx row' }
  let m' := m.setIfInBounds batch ph'
  Spec.Aggregate.Wire.EthereumProof.toBytes { eth with proof := { eth.proof with merkle := m' } }

def flipMerkleSiblingByte (eth : Spec.Aggregate.Wire.EthereumProof) (batch sibIdx byteIdx : Nat) :
    ByteArray :=
  let m := eth.proof.merkle
  let ph := m.getD batch ⟨#[], #[]⟩
  let d := ph.siblings.getD sibIdx default
  let d' : Spec.Merkle.Digest :=
    Vector.ofFn fun i : Fin 32 =>
      if i.val = byteIdx then (d[i.val]) ^^^ 1 else d[i.val]
  let ph' : Spec.Merkle.PrunedMerklePaths := { ph with siblings := ph.siblings.setIfInBounds sibIdx d' }
  let m' := m.setIfInBounds batch ph'
  Spec.Aggregate.Wire.EthereumProof.toBytes { eth with proof := { eth.proof with merkle := m' } }

def build34MutantSpecs : Array SoundnessMutantSpec := #[
  -- Group 1 (1..5): Public input / message digest / root tampering
  ⟨1, "public_input_statement", "m01_claim_message_digest_bit", fun wire _ =>
    flipByteAt wire (8 + 32 + 5) 1⟩,
  ⟨2, "public_input_statement", "m02_claim_pubkey_root_bit", fun wire _ =>
    flipByteAt wire (8 + 1) 1⟩,
  ⟨3, "public_input_statement", "m03_unsorted_signer_claims", fun _ eth =>
    let xs := eth.claims.xmss
    let p0 := xs.getD 0 default
    let p1 := xs.getD 1 default
    let xs' := (xs.setIfInBounds 0 p1).setIfInBounds 1 p0
    Spec.Aggregate.Wire.EthereumProof.toBytes { eth with claims := { eth.claims with xmss := xs' } }⟩,
  ⟨4, "public_input_statement", "m04_da_commitment_root_some", fun _ eth =>
    let fakeRoot := ByteArray.mk (Array.replicate 32 0x42)
    Spec.Aggregate.Wire.EthereumProof.toBytes { eth with daRoot := some fakeRoot }⟩,
  ⟨5, "public_input_statement", "m05_deferred_bytecode_point_coord", fun _ eth =>
    let pt := eth.defer.bytecodePoint
    let v0 := pt.getD 0 Spec.Field.zero
    let pt' := pt.setIfInBounds 0 ⟨v0.c0 ^^^ 1, v0.c1, v0.c2⟩
    Spec.Aggregate.Wire.EthereumProof.toBytes { eth with defer := { eth.defer with bytecodePoint := pt' } }⟩,

  -- Group 2 (6..10): Transcript Fiat-Shamir / PoW grinding / length truncation & trailing byte injection
  ⟨6, "transcript_pow_wire", "m06_fiat_shamir_scalar_swap", fun _ eth =>
    swapStreamElems eth 1984 1985⟩,
  ⟨7, "transcript_pow_wire", "m07_fiat_shamir_stream_rotate", fun _ eth =>
    rotateStreamLeft1 eth⟩,
  ⟨8, "transcript_pow_wire", "m08_whir_pow_grinding_nonce", fun _ eth =>
    setStreamElem eth 2031 (fun x => ⟨x.c0 ^^^ 1, x.c1, x.c2⟩)⟩,
  ⟨9, "transcript_pow_wire", "m09_wire_truncated_bytes", fun wire _ =>
    wire.extract 0 (wire.size - 17)⟩,
  ⟨10, "transcript_pow_wire", "m10_wire_trailing_byte_injection", fun wire _ =>
    wire.push 0x00⟩,

  -- Group 3 (11..16): PCS commitment root & Merkle authentication path bit-flips across rounds
  ⟨11, "pcs_merkle_rounds", "m11_l0_commitment_root_bit", fun _ eth =>
    setStreamElem eth 8 (fun x => ⟨x.c0 ^^^ 1, x.c1, x.c2⟩)⟩,
  ⟨12, "pcs_merkle_rounds", "m12_l0_commitment_root_nonzero_c2", fun _ eth =>
    setStreamElem eth 9 (fun x => ⟨x.c0, x.c1, 1⟩)⟩,
  ⟨13, "pcs_merkle_rounds", "m13_l0_merkle_leaf_word_bit", fun _ eth =>
    flipMerkleLeafWord eth 0 0 0⟩,
  ⟨14, "pcs_merkle_rounds", "m14_l0_merkle_sibling_digest_bit", fun _ eth =>
    flipMerkleSiblingByte eth 0 0 0⟩,
  ⟨15, "pcs_merkle_rounds", "m15_whir_round1_commitment_root_bit", fun _ eth =>
    setStreamElem eth 1975 (fun x => ⟨x.c0 ^^^ 1, x.c1, x.c2⟩)⟩,
  ⟨16, "pcs_merkle_rounds", "m16_whir_deeper_round_merkle_sibling_bit", fun _ eth =>
    flipMerkleSiblingByte eth 2 3 7⟩,

  -- Group 4 (17..22): Bus / logUp GKR fraction sumcheck claim, round poly, and final eval tampering
  ⟨17, "bus_logup_gkr", "m17_bus_gkr_shared_root_claim", fun _ eth =>
    setStreamElem eth 10 (fun x => ⟨x.c0 ^^^ 1, x.c1, x.c2⟩)⟩,
  ⟨18, "bus_logup_gkr", "m18_bus_gkr_zero_count_root", fun _ eth =>
    setStreamElem eth 11 (fun _ => Spec.Field.zero)⟩,
  ⟨19, "bus_logup_gkr", "m19_bus_gkr_round_poly_coeff", fun _ eth =>
    setStreamElem eth 25 (fun x => ⟨x.c0 ^^^ 1, x.c1, x.c2⟩)⟩,
  ⟨20, "bus_logup_gkr", "m20_bus_gkr_layer_child_eval", fun _ eth =>
    setStreamElem eth 485 (fun x => ⟨x.c0 ^^^ 1, x.c1, x.c2⟩)⟩,
  ⟨21, "bus_logup_gkr", "m21_bus_memory_fingerprint_eval", fun _ eth =>
    setStreamElem eth 492 (fun x => ⟨x.c0 ^^^ 1, x.c1, x.c2⟩)⟩,
  ⟨22, "bus_logup_gkr", "m22_table_sumcheck_final_column_eval", fun _ eth =>
    setStreamElem eth 600 (fun x => ⟨x.c0 ^^^ 1, x.c1, x.c2⟩)⟩,

  -- Group 5 (23..28): Keccak-f[1600] GKR round sumcheck, theta/rho/pi/chi/iota & bit-constraint tampering
  ⟨23, "keccak_f1600_gkr", "m23_keccak_committed_segment_claim", fun _ eth =>
    setStreamElem eth 699 (fun x => ⟨x.c0 ^^^ 1, x.c1, x.c2⟩)⟩,
  ⟨24, "keccak_f1600_gkr", "m24_keccak_rmfe_bit_product_poly", fun _ eth =>
    setStreamElem eth 705 (fun x => ⟨x.c0 ^^^ 1, x.c1, x.c2⟩)⟩,
  ⟨25, "keccak_f1600_gkr", "m25_keccak_instance_round_sumcheck", fun _ eth =>
    setStreamElem eth 848 (fun x => ⟨x.c0 ^^^ 1, x.c1, x.c2⟩)⟩,
  ⟨26, "keccak_f1600_gkr", "m26_keccak_theta_rho_pi_chi_local_t", fun _ eth =>
    setStreamElem eth 1280 (fun x => ⟨x.c0 ^^^ 1, x.c1, x.c2⟩)⟩,
  ⟨27, "keccak_f1600_gkr", "m27_keccak_output_slot_opening_word", fun _ eth =>
    setStreamElem eth 1876 (fun x => ⟨x.c0 ^^^ 1, x.c1, x.c2⟩)⟩,
  ⟨28, "keccak_f1600_gkr", "m28_keccak_input_pack_slice_eval", fun _ eth =>
    setStreamElem eth 1920 (fun x => ⟨x.c0 ^^^ 1, x.c1, x.c2⟩)⟩,

  -- Group 6 (29..34): WHIR folding round polys, OOD samples, stir queries, RingSwitch claims, final poly
  ⟨29, "whir_ringswitch_pcs", "m29_ringswitch_stacked_initial_quad", fun _ eth =>
    setStreamElem eth 1961 (fun x => ⟨x.c0 ^^^ 1, x.c1, x.c2⟩)⟩,
  ⟨30, "whir_ringswitch_pcs", "m30_whir_l0_fold_round_poly", fun _ eth =>
    setStreamElem eth 1967 (fun x => ⟨x.c0 ^^^ 1, x.c1, x.c2⟩)⟩,
  ⟨31, "whir_ringswitch_pcs", "m31_whir_ood_sample_eval", fun _ eth =>
    setStreamElem eth 1977 (fun x => ⟨x.c0 ^^^ 1, x.c1, x.c2⟩)⟩,
  ⟨32, "whir_ringswitch_pcs", "m32_whir_stir_query_intro_poly", fun _ eth =>
    setStreamElem eth 1997 (fun x => ⟨x.c0 ^^^ 1, x.c1, x.c2⟩)⟩,
  ⟨33, "whir_ringswitch_pcs", "m33_whir_tail_sumcheck_round_poly", fun _ eth =>
    setStreamElem eth 2034 (fun x => ⟨x.c0 ^^^ 1, x.c1, x.c2⟩)⟩,
  ⟨34, "whir_ringswitch_pcs", "m34_whir_final_residual_poly_coeff", fun _ eth =>
    setStreamElem eth 2025 (fun x => ⟨x.c0 ^^^ 1, x.c1, x.c2⟩)⟩
]

def soundnessRowJson (r : SoundnessMutantResult) : String :=
  "{\"id\":" ++ toString r.id ++
  ",\"group\":\"" ++ jsonEscape r.group ++ "\"" ++
  ",\"name\":\"" ++ jsonEscape r.name ++ "\"" ++
  ",\"baseline_accepted\":" ++ (if r.baselineAccepted then "true" else "false") ++
  ",\"mutated_rejected\":" ++ (if r.mutatedRejected then "true" else "false") ++
  ",\"mutated_bytes\":" ++ toString r.mutatedBytes ++ "}"

def runMutantSuite34 (oracleDir coreProofPath outJsonPath : String)
    (dumpDirOpt : Option String := none) : IO Unit := do
  let base := System.FilePath.mk oracleDir
  let program ← Model.Cli.loadBytecode (Model.Cli.childPath base "bytecode.bin")
  let seedBytes ← Model.Cli.loadSeed (Model.Cli.childPath base "seed.bin")
  let rawRecords ← Model.Cli.loadRawInputs (Model.Cli.childPath base "xmss-inputs.bin")
  let coreBytes ← IO.FS.readBinFile (System.FilePath.mk coreProofPath)

  let guest ← match Model.Aggregate.Verify.prepareBytecodeFast program with
    | some bc => pure bc
    | none => throw (IO.userError "prepareBytecodeFast failed on guest bytecode")
  let seed : E × E := (Spec.Xmss.packCell seedBytes, Spec.Xmss.packCell seedBytes 16)
  let claims : Spec.Aggregate.Wire.SignatureClaims := ⟨Model.Cli.signatureClaimsOf rawRecords, #[]⟩
  let bcVal : E := ⟨guest.table.getD 0 0, 0, 0⟩

  let ethBase ← match Model.Aggregate.Wire.EthereumProof.fromBytesWithoutPubkeys coreBytes claims bcVal with
    | some e => pure e
    | none => throw (IO.userError "failed to decode baseline xmss4.ethproof")

  let baselineWire := Model.Aggregate.Wire.EthereumProof.toBytes ethBase
  match dumpDirOpt with
  | some d =>
    IO.FS.createDirAll (System.FilePath.mk d)
    IO.FS.writeBinFile (System.FilePath.mk (d ++ "/baseline.ethwire")) baselineWire
  | none => pure ()

  let specs := build34MutantSpecs
  if specs.size != 34 then
    throw (IO.userError s!"expected 34 mutant specs, got {specs.size}")

  let t0 ← IO.monoMsNow
  let mut results : Array SoundnessMutantResult := #[]
  let mut baselinePassCount : Nat := 0
  let mut mutatedRejectCount : Nat := 0

  for spec in specs do
    let baseOk := Model.Aggregate.Verify.verifyEthereumBytes guest seed baselineWire
    if baseOk then
      baselinePassCount := baselinePassCount + 1
    let mutBytes := spec.mutate baselineWire ethBase
    match dumpDirOpt with
    | some d =>
      let pad := if spec.id < 10 then "0" ++ toString spec.id else toString spec.id
      IO.FS.writeBinFile (System.FilePath.mk (d ++ "/mutant_" ++ pad ++ ".ethwire")) mutBytes
    | none => pure ()
    let mutAccepted := Model.Aggregate.Verify.verifyEthereumBytes guest seed mutBytes
    let mutRejected := !mutAccepted
    if mutRejected then
      mutatedRejectCount := mutatedRejectCount + 1
    results := results.push ⟨spec.id, spec.group, spec.name, baseOk, mutRejected, mutBytes.size⟩

  let elapsedMs := (← IO.monoMsNow) - t0
  let allOk := decide (baselinePassCount = 34 ∧ mutatedRejectCount = 34)
  let rowsJson := String.intercalate ",\n    " (results.toList.map soundnessRowJson)
  let json := "{\n" ++
    "  \"verifier\": \"lean_pure\",\n" ++
    "  \"refinement_theorem\": \"LeanVmXmss.Proofs.Aggregate.Verify.verifyEthereumBytes_refines\",\n" ++
    "  \"mutant_total\": 34,\n" ++
    "  \"baseline_accepted_count\": " ++ toString baselinePassCount ++ ",\n" ++
    "  \"mutated_rejected_count\": " ++ toString mutatedRejectCount ++ ",\n" ++
    "  \"all_passed\": " ++ (if allOk then "true" else "false") ++ ",\n" ++
    "  \"elapsed_ms\": " ++ toString elapsedMs ++ ",\n" ++
    "  \"baseline_wire_bytes\": " ++ toString baselineWire.size ++ ",\n" ++
    "  \"mutants\": [\n    " ++ rowsJson ++ "\n  ]\n}\n"

  IO.FS.writeFile (System.FilePath.mk outJsonPath) json
  IO.println s!"LEAN_MUTANT34_DONE baseline={baselinePassCount}/34 rejected={mutatedRejectCount}/34 elapsed_ms={elapsedMs} out={outJsonPath}"
  unless allOk do
    throw (IO.userError s!"Lean 34-mutant suite failed: baseline={baselinePassCount}/34 rejected={mutatedRejectCount}/34")

end LeanVmXmss.Tests.Audit.Mutants

#eval LeanVmXmss.Tests.Audit.Mutants.run
