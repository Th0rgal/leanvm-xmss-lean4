# LeanVmXmss — Lean 4 Formalized & Native-Compiled leanVM XMSS-1400 Prover Campaign

Lean 4 (`v4.35.0`) reimplementation and formal refinement campaign for the `leanVM` XMSS-1400 aggregation prover (`leanVM@59c2984df79cc9ff1914e547c5d5d390fffc8f3e`), compiled natively via `lean-native` / `turbo-lean` (`29d85f7da2d963750f77d76d53386f14`) against the unchanged Rust reference verifier.

## Original Goal

Reimplement in pure/native-compiled Lean 4 (zero cryptographic Rust/C FFI) the full proving pipeline exercised by:

```sh
cargo leanvm aggregate --xmss 1400 --log-inv-rate 1 --repeat 3
```

with formal `Spec` / `Model` refinement proofs (`0 sorryAx`, `0 Classical.choice` in strict kernel gates, `turbo-lean audit-spec` tight specs), acceptance of emitted `EthereumProof` wire bytes by the **unmodified Rust reference verifier**, and target Tier B performance `< 1.15 s` mean proving time and `< 8.633 GiB` peak RSS (plus beating same-host Rust in `>= 5` alternating passes on isolated `boat:xlarge`).

## Repository Layout

- `LeanVmXmss/` — Main Lean 4 package (`Spec/`, `Model/`, `Proofs/`, `Tests/`):
  - **P1 Unified Hub (`xmss-hub-v3-warm`)**: Binary tower fields `GF(2^64)` (`K`) and `GF(2^192)` (`E`), `Keccak-f[1600]`, Fiat–Shamir `Transcript`, `Merkle`, `Vm` (exact `1,146,537` cycles and `8,668,972` memory cells on `xmss1400`), `Xmss` encodings & hints, `Layout`, `Witness`, `Pcs/{Ntt,Commit}` (exact L0 WHIR root on `xmss1400`), and `Bus` + `Constraints` sumchecks.
  - **Wave 1 — W1 (`{Spec,Model,Proofs,Tests}/KeccakGkr/**`)**: Segmented `q_keccak` witness, RMFE, Keccak-f[1600] GKR reduction, and `into_pcs_claims` (`347` audited declarations, `0` rejections, `49/49` tight specs, 6-case Rust oracle parity).
  - **Wave 1 — W2 (`{Spec,Model,Proofs,Tests}/Pcs/{RingSwitch,StackOpen,Whir}.lean`, `{Spec,Model,Proofs}/Aggregate/Wire.lean`, `Tests/Pcs/**`)**: `RingSwitch`, single stacked `WHIR` opening, and `EthereumProof` wire codec (`WHIR_STRICT_AUDIT_COUNT 1064`, `REJECTIONS 0`, `85/85` + `18/18` tight specs; 6/6 splice proofs accepted by the unchanged Rust verifier across `syn_tiny`, `syn_jump`, `syn_deref`, `syn_keccak`, `xmss4`, and `xmss16`).
  - **Wave 1 — W3 (`Model/{Witness,Bus}/Flat.lean`, `Model/Bus/Native.lean`, `Proofs/{Witness,Bus}/FlatRefinement.lean`)**: Flat Witness/Bus layer and refinement proofs (parity-verified; currently delegates to boxed scalar arrays pending Wave 2 unboxed SoA SIMD kernels).
  - **Wave 1 — W4 (`Model/Cli/{Aggregate,Inputs}.lean`, `Tests/Cli/**`)**: End-to-end CLI `aggregate` driver, Rust per-challenge trace exporter (`--xmss 4`, `--xmss 16`), and Tier B benchmark runner.
  - **Wave 1 — W5 (`Tests/Audit/**`)**: Whole-repository axiom audit (`5,217` declarations, `0` rejections) and `34/34` rejected negative mutants across Lean and Rust verifiers.
- `meta/` — Compiler P0 patch (`compiler-fix.patch`), frozen P1 spec manifest (`15/15` SHA-256s), and warm hub / shard manifests.
- `oracle/` — Rust differential oracle harness (`shard-c-src/rust-work`) and `xmss1400` fixture hashes (`LARGE_FIXTURES_MANIFEST.json`).
- `turbo-lean-scripts/` — Conformance, kernel-gate, and scalar frontend test scripts.
- `plan.md` & `campaign-state.json` — Full Maxwell/Hindsight execution plan, baselines, and verified artifact ledger.

## Current Status

- **Completed & Verified**: Phases **P0** (Rust baselines & compiler fixes), **P1** (unified hub + frozen specs), and **all 5 Wave 1 protocol/audit shards (`W1`–`W5`)** with zero `sorryAx`, zero `Classical.choice` rejections, `34/34` mutant rejections, and Rust `EthereumProof` splice verification on all 6 synthetic + `xmss4` + `xmss16` vectors.
- **Pending Next Phases**: Final Wave 1 single-binary CLI integration snapshot (`xmss-e2e-green`), followed by Wave 2 (`P3`–`P5`) unboxed SoA `Flat/` + AVX-512/VPCLMULQDQ/GFNI `lean-native` kernels (`K1`–`K5`) and isolated `boat:xlarge` Tier B `< 1.15 s` benchmarking on full `xmss1400`.
