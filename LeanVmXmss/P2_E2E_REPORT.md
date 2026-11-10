# Phase P2 Pure-Lean End-to-End Prover Report (`5607f25`)

- **Base commit**: `5607f253bf1e61127df287e54821e9a` (`/tmp/repo`, hub `$HUB/LeanVmXmss`)
- **Reference commits**: `leanVM` `59c2984df79cc9ff1914e547c5d5d390fffc8f3e`, `turbo-lean` `29d85f7da2d963750f77d76d5323408a73386f14`
- **Binaries**: `/tmp/p2-bins/{e2e-aggregate,e2e-check,cli-check,keccakcheck,whircheck}`, `$CARGO_TARGET_DIR/release/{e2e-oracle,whir-oracle,mutant-suite}`
- **Proof artifacts**: `/tmp/p2-proofs/`

## Summary of Changes

| File | Status | Role |
| --- | --- | --- |
| `Model/Cli/E2E.lean` | Added | Pure-Lean end-to-end `proveVmRun` (`Model.Witness` -> `Model.KeccakGkr.proveKeccakGkr` -> `Registers.toSpec` -> `Model.Pcs.StackOpen.proveStackedPcs` -> `Cursor.phase`) and `proveLeafEthereum` (XMSS verify, `sortedUnique` signer set, 23-coord zero deferred claim, `EthereumProof.statement` check, `toBytesWithoutPubkeys`) |
| `Model/Cli/Aggregate.lean` | Modified | Added `ProofArtifact.wireBytes`, `e2eProver`, `proverOf "e2e"`, binary `--out-proof` output when `wireBytes` is non-empty (preserving `vmWitnessProver` and `stubProver`) |
| `Model/Cli/E2EMain.lean` | Added | Standalone `e2e-aggregate` native executable entry point |
| `Tests/Cli/E2ECheck.lean` | Added | Gate 1/2 driver (`prove-syn`, `check-prepcs`, `permute-inputs`, `aggregate`) |
| `Tests/Pcs/WhirCheck.lean` | Modified | Added `wire` parity cases (`23`-var deferred point) matching `whir-oracle all` while keeping `whircheck splice` intact |
| `Tests/Cli/AxiomAudit.lean` | Modified | Extended strict CLI axiom audit with `Model.Cli.E2E` (`174` declarations, `0` rejections) |
| `Tests/Audit/WholeRepoAxiomAudit.lean` | Modified | Extended whole-repo strict axiom audit across all W1–W4 + P2 modules including `Model.Cli.*`, `Model.KeccakGkr.Scalar`, `Model.Pcs.{RingSwitch,StackOpen,Whir}`, `Model.Aggregate.Wire`, `Proofs.*`, `Spec.*`, and `Tests.Cli.E2ECheck` (`6802` declarations across `38` module groups, `0` rejections) |

---

## Gate 1 — Pure-Lean Synthetic `VmProof` & Pre-PCS Transcript Bridge (`PASS`)

### Pre-PCS Transcript Bridge (`syn_tiny`)
```text
SPLICE_DUMP|syn_tiny|stream=1797|slots=141|ring_vars=15
E2E_PREPCS_BRIDGE|PASS|case=syn_tiny|stream=1797|pending=4|ops=2153
```

### Pure-Lean Synthetic `VmProof` Emission & Unchanged Rust `leanvm_core::cpu::verify` (3x each)
```text
E2E_VM_PROOF|case=syn_tiny|path=/tmp/p2-proofs/syn_tiny.vmproof|bytes=204736|stream=1886|merkle=3|mu=19|cycles=15|ms=3406
VERIFY_VM|case=syn_tiny|path=/tmp/p2-proofs/syn_tiny.vmproof|proof_bytes=204736
VERIFY_VM|PASS|pass=1|ms=9|keccak_scalars_len=1238
VERIFY_VM|PASS|pass=2|ms=7|keccak_scalars_len=1238
VERIFY_VM|PASS|pass=3|ms=7|keccak_scalars_len=1238

E2E_VM_PROOF|case=syn_jump|path=/tmp/p2-proofs/syn_jump.vmproof|bytes=204416|stream=1886|merkle=3|mu=19|cycles=14|ms=2890
VERIFY_VM|case=syn_jump|path=/tmp/p2-proofs/syn_jump.vmproof|proof_bytes=204416
VERIFY_VM|PASS|pass=1|ms=10|keccak_scalars_len=1238
VERIFY_VM|PASS|pass=2|ms=7|keccak_scalars_len=1238
VERIFY_VM|PASS|pass=3|ms=7|keccak_scalars_len=1238

E2E_VM_PROOF|case=syn_deref|path=/tmp/p2-proofs/syn_deref.vmproof|bytes=203648|stream=1886|merkle=3|mu=19|cycles=15|ms=2751
VERIFY_VM|case=syn_deref|path=/tmp/p2-proofs/syn_deref.vmproof|proof_bytes=203648
VERIFY_VM|PASS|pass=1|ms=11|keccak_scalars_len=1238
VERIFY_VM|PASS|pass=2|ms=7|keccak_scalars_len=1238
VERIFY_VM|PASS|pass=3|ms=9|keccak_scalars_len=1238

E2E_VM_PROOF|case=syn_keccak|path=/tmp/p2-proofs/syn_keccak.vmproof|bytes=203912|stream=1886|merkle=3|mu=19|cycles=15|ms=2784
VERIFY_VM|case=syn_keccak|path=/tmp/p2-proofs/syn_keccak.vmproof|proof_bytes=203912
VERIFY_VM|PASS|pass=1|ms=7|keccak_scalars_len=1238
VERIFY_VM|PASS|pass=2|ms=8|keccak_scalars_len=1238
VERIFY_VM|PASS|pass=3|ms=8|keccak_scalars_len=1238
```

---

## Gate 2 — Pure-Lean Leaf `EthereumProof` & Unchanged Rust `EthereumProof::verify` (`PASS`)

Each pure-Lean `.ethproof` uses the 23-coordinate zero leaf deferred claim (`4 + kbc = 4 + 19 = 23`, `kbc = 19` for the unified recursion guest of `524,288` ops) and encodes `EthereumProof.toBytesWithoutPubkeys`. For both `xmss4` and `xmss16`, the embedded `VmProof` bytes (`ethproof[561..]`) are byte-for-byte identical to the Rust-reference `leanvm_core::cpu::prove` output (`xmss4.splice`, `xmss16.splice`).

### `xmss4`
```text
BENCH|impl=lean-cli|prover=e2e|xmss=4|records=4|signers=4|log_inv_rate=1|repeat=0|cooldown_ms=0
WARMUP|nanos=13150753134
LAST|statement=cce03264acda50ea6f9162687d7bdef68e5368e5411f76c96bf321707e098290|hints_keccak256=a40e901f83945c392fd43bbe8fd02a9185433cdb924e7be48fbe5d3f5691fb95|cycles=21465|memory_cells_used=65536|memory_keccak256=495815c4b8475105845846256923c26c367d2d87b1f334f6852581f6c065ce0c
STATS|passes=0|mean_nanos=0
ARTIFACT|path=/tmp/p2-proofs/xmss4.ethproof|bytes=241473

VERIFY_ETH|inputs=/var/lib/orb-node/work/caches/xmss-hub-v3/oracle/xmss4/xmss-inputs.bin|path=/tmp/p2-proofs/xmss4.ethproof|wire_bytes=241473|proof_size=240912|signers=4
VERIFY_ETH|PASS|pass=1|ms=212
VERIFY_ETH|PASS|pass=2|ms=10
VERIFY_ETH|PASS|pass=3|ms=10
```

### `xmss16`
```text
BENCH|impl=lean-cli|prover=e2e|xmss=16|records=16|signers=16|log_inv_rate=1|repeat=0|cooldown_ms=0
WARMUP|nanos=22514067395
LAST|statement=919bb576b61c8209abd656d974df9cc2f3b8cb3276c9f5938257fe8e4e23109d|hints_keccak256=516480ce5972001deac624e9700ab64cb0f7e712b9374c376ab92a0bcd733d1a|cycles=31140|memory_cells_used=117322|memory_keccak256=e7c2d337963bc1db2fe2d5dce2b920d0ca89332383eb661dc1f2401482b2d0c0
STATS|passes=0|mean_nanos=0
ARTIFACT|path=/tmp/p2-proofs/xmss16.ethproof|bytes=279625

VERIFY_ETH|inputs=/var/lib/orb-node/work/caches/xmss-hub-v3/oracle/xmss16/xmss-inputs.bin|path=/tmp/p2-proofs/xmss16.ethproof|wire_bytes=279625|proof_size=279064|signers=16
VERIFY_ETH|PASS|pass=1|ms=242
VERIFY_ETH|PASS|pass=2|ms=11
VERIFY_ETH|PASS|pass=3|ms=11
```

### Fresh Inputs (`seed=424242`, `n=6`) + Permutation Determinism
```text
FRESH_INPUTS|dir=/tmp/p2-proofs/fresh|records=6|sorted_unique=6|cycles=23081|mem_used=65536|statement=f0d3f6930eac5503d4f33c116bc0df3088830e05d35392f4188f166cb450d29d
E2E_PERMUTE_INPUTS|PASS|src=/tmp/p2-proofs/fresh|dst=/tmp/p2-proofs/fresh-perm|records=6

BENCH|impl=lean-cli|prover=e2e|xmss=6|records=6|signers=6|log_inv_rate=1|repeat=0|cooldown_ms=0
WARMUP|nanos=17939117636
LAST|statement=f0d3f6930eac5503d4f33c116bc0df3088830e05d35392f4188f166cb450d29d|hints_keccak256=22d817d48d2cb6f6a96552e8462b286f7b36b3bcc18294f256f4e69008be1ade|cycles=23081|memory_cells_used=65536|memory_keccak256=2446c828fb94a7979fae5a12c61da600c0c3410ea3352684eda59954726eb382
STATS|passes=0|mean_nanos=0
ARTIFACT|path=/tmp/p2-proofs/fresh.ethproof|bytes=248289

BENCH|impl=lean-cli|prover=e2e|xmss=6|records=6|signers=6|log_inv_rate=1|repeat=0|cooldown_ms=0
WARMUP|nanos=17383721526
LAST|statement=f0d3f6930eac5503d4f33c116bc0df3088830e05d35392f4188f166cb450d29d|hints_keccak256=22d817d48d2cb6f6a96552e8462b286f7b36b3bcc18294f256f4e69008be1ade|cycles=23081|memory_cells_used=65536|memory_keccak256=2446c828fb94a7979fae5a12c61da600c0c3410ea3352684eda59954726eb382
STATS|passes=0|mean_nanos=0
ARTIFACT|path=/tmp/p2-proofs/fresh-perm.ethproof|bytes=248289
PERMUTE_IDENTICAL (cmp /tmp/p2-proofs/fresh.ethproof /tmp/p2-proofs/fresh-perm.ethproof == 0)

VERIFY_ETH|inputs=/tmp/p2-proofs/fresh/xmss-inputs.bin|path=/tmp/p2-proofs/fresh.ethproof|wire_bytes=248289|proof_size=247728|signers=6
VERIFY_ETH|PASS|pass=1|ms=281
VERIFY_ETH|PASS|pass=2|ms=14
VERIFY_ETH|PASS|pass=3|ms=12
```

---

## Proof Artifact Inventory (`/tmp/p2-proofs/`)

| Artifact | Bytes | SHA-256 |
| --- | ---: | --- |
| `syn_tiny.vmproof` | `204736` | `2ed3c7fa2be2d8e6d53a07f010520a5d7427008f4c7ab033dab65fdc1c733c06` |
| `syn_jump.vmproof` | `204416` | `7c5996137a656376c13dc766d2575fd1ff1aa43a67a3a0381769e78113e813ca` |
| `syn_deref.vmproof` | `203648` | `175c932bcc0f54501f1f28ca76fc7f24dce50c8cea7090d7fecdcfbe6a3d17f3` |
| `syn_keccak.vmproof` | `203912` | `81acbe680ce1f3ff750950a2075ad707aff61401897ba9b3456323301d41e05e` |
| `xmss4.ethproof` | `241473` | `ca0e390d5fc7364b42ecdd40e433d4b6ae3fb3f80648ab1abc779d4a94320815` |
| `xmss16.ethproof` | `279625` | `bab920905b70a74d4853be3593105d6056b759c9b208005e0fbc234588338dbd` |
| `fresh.ethproof` | `248289` | `b8c9b3252b443907c047be399e9d5edfff4e61cd334c43058ba0fdc763243043` |
| `fresh-perm.ethproof` | `248289` | `b8c9b3252b443907c047be399e9d5edfff4e61cd334c43058ba0fdc763243043` |

---

## Gate 3 — Regressions, Axiom Audits, Spec Tightness, and W5 Mutants (`PASS`)

### Keccak-GKR Parity (`6/6`: `syn_tiny`, `syn_jump`, `syn_deref`, `syn_keccak`, `xmss4`, `xmss16`)
```text
KECCAK_GKR_DUMP_SCALARS=1 /tmp/p2-bins/keccakcheck synthetic -> rc=0 (SYNTHETIC_PARITY|PASS)
/tmp/p2-bins/keccakcheck all $HUB/oracle/xmss4 $HUB/oracle/xmss16 -> rc=0
TIMING_MS|syn_tiny|total=690|iv=0|exec=0|bundle=183|bus_and_gkr=507
TIMING_MS|syn_jump|total=762|iv=0|exec=1|bundle=196|bus_and_gkr=565
TIMING_MS|syn_deref|total=996|iv=0|exec=0|bundle=236|bus_and_gkr=760
TIMING_MS|syn_keccak|total=1042|iv=0|exec=0|bundle=224|bus_and_gkr=818
TIMING_MS|xmss4|total=7126|iv=1811|exec=138|bundle=834|bus_and_gkr=4343
TIMING_MS|xmss16|total=11233|iv=1750|exec=177|bundle=1113|bus_and_gkr=8193
ALL_KECCAK_GKR_PARITY|PASS
```

### WHIR Parity & Splice (`6/6` `SPLICE_OK`)
```text
diff -q <($CARGO_TARGET_DIR/release/whir-oracle all) <(/tmp/p2-bins/whircheck all) -> 0 (WHIR_PARITY_MATCH)
SPLICE_OK|syn_tiny|stream=1886|merkle=3|wire_bytes=205377
SPLICE_OK|syn_jump|stream=1886|merkle=3|wire_bytes=205057
SPLICE_OK|syn_deref|stream=1886|merkle=3|wire_bytes=204289
SPLICE_OK|syn_keccak|stream=1886|merkle=3|wire_bytes=204553
SPLICE_OK|xmss4|stream=2038|merkle=4|wire_bytes=241553
SPLICE_OK|xmss16|stream=2086|merkle=4|wire_bytes=279705
```

### W4 CLI Regression Gate (`cli-check gate`, including `xmss1400` parity without proving `xmss1400`)
```text
CLI_CHECK_ORACLE|PASS|dir=/var/lib/orb-node/work/caches/xmss-hub-v3/oracle/xmss4|records=4|cycles=21465|memory_cells_used=65536|memory_keccak256=495815c4b8475105845846256923c26c367d2d87b1f334f6852581f6c065ce0c
CLI_CHECK_ORACLE|PASS|dir=/var/lib/orb-node/work/caches/xmss-hub-v3/oracle/xmss16|records=16|cycles=31140|memory_cells_used=117322|memory_keccak256=e7c2d337963bc1db2fe2d5dce2b920d0ca89332383eb661dc1f2401482b2d0c0
CLI_CHECK_PARITY|PASS|dir=/var/lib/orb-node/work/caches/xmss-hub-v3/oracle/xmss1400|records=1400|statement_digest=ded8679e548f3d7c810a3c50e1c69b4fed50773b35189e3a67d7728accafe423
CLI_CHECK_FRESH|PASS|dir=/tmp/p2-proofs/fresh|records=6|cycles=23081|memory_cells_used=65536|memory_keccak256=2446c828fb94a7979fae5a12c61da600c0c3410ea3352684eda59954726eb382
CLI_CHECK_GATE|PASS
```

### Constructive Axiom & Spec Tightness Audits (`0 sorryAx`, `0 Classical.choice`)
```text
LEAN_PATH=.lake/build/lib/lean lean Tests/Cli/AxiomAudit.lean
CLI_STRICT_AUDIT_COUNT 174
CLI_STRICT_AUDIT_REJECTIONS 0

W5_AUDIT_OUT=/tmp/p2-logs LEAN_PATH=.lake/build/lib/lean lean Tests/Audit/WholeRepoAxiomAudit.lean
W5_REPO_AUDIT_COUNT 6802
W5_REPO_AUDIT_REJECTIONS 0
W5_REPO_AUDIT_MODULES 38

turbo-lean --json audit-spec --policy strict-proofs Proofs Spec
{"ok": true, "verdict": "specs_audited", "total_specs_audited": 926, "vacuous_specs": 0, "trivial_specs": 0, "stub_defs": [], "shadowed_constants": [], "forbidden_scope_decls": [], "warnings": []}
```

### W5 Negative Mutant Suite (`34/34` rejected: `5` Lean + `29` Rust)
- **Lean Category 4 (`Tests/Audit/Mutants.lean` -> `$HUB/tmp/mutants-lean.json`)**: `mutant_count=5`, `accepted_count=0`, `all_rejected=true`
- **Rust Categories 1, 2, 3, 5, 6, 7, 8, 9, 10 (`mutant-suite` -> `/tmp/p2-logs/g3-rust-mutants.json`)**: `mutant_count=29`, `accepted_count=0`, `all_rejected=true`

---

## Gate 4 — Frozen Baseline Verification vs `/tmp/repo` (`PASS`)

`diff -rq` against `/tmp/repo/LeanVmXmss` confirms **zero** modifications to:
- `lakefile.toml`
- All `Spec/**/*.lean` files (all 15 P1 frozen spec files plus W1/W2/W3 `Spec/KeccakGkr`, `Spec/Pcs`, `Spec/Aggregate`)
- All `Proofs/**/*.lean` files
- `{Spec,Model,Proofs,Tests}/Field/**`
- `Tests/Vm/**`
- `Tests/Hub/{ShardAHw.lean,ShardAHwRefinement.lean,cache_manager.py,mcp_client.py}`
- `Model/Layout/Scalar.lean`, `Model/Bus/Scalar.lean`, `Model/Pcs/{Ntt,Commit}.lean`
