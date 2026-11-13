# Keccak GKR campaign checkpoint — 2026-11-13

Base: 299c689373ef3e98e0f150ff4bec21ca5e3aaea1; branch campaign/keccak-gkr.
Only GKR implementation paths are owned; bus profiling is read-only. No implementation edits yet.

Initial findings:
- E2E imports Model.KeccakGkr.Flat and invokes proveReductionFlat through Model.Cli.E2E.proveKeccakGkrOnlyWq.
- Model/KeccakGkr/Flat.lean imports Scalar only. Standalone Native/Kernels/KeccakGkr kernels are absent from this import/call path.
- Flat has software clmul24Soft, clmulLoSoft/clmulHiSoft and byte-at-a-time planar E buffers. pairSumsRangeFlat repeatedly constructs E and calls nativeKaratsuba. These are candidates, not measured bottleneck claims.
- productRangeFlat scans all 1600 positions for each of 47 product bits for every pack/segment. A potential loop-transposition target, pending measured baseline and parity proof.
- Runtime task wrappers silently map task errors to zero/empty buffers; no changes proposed without considering protocol fidelity.

Environment:
- Initial scope memory.max=8973910016, memory.high=8076517376; root cgroup has no memory.max. Host MemTotal=32863448 kB.
- Raised process scope using user systemd to MemoryMax=26G (27917287424), MemoryHigh=24G (25769803776). This is resource setup, not a performance result.
- turbo-lean build with LEAN_NUM_THREADS=1, TURBO_LEAN_JOBS=1, max-memory-mb=6144 completed (67 jobs). Native island strict audit count=63, rejections=0; entrypoints depend only on propext/Quot.sound.
- Installed lean-native cannot elaborate against Lean 4.35: Init.olean incompatible header. Compatible compiler requested; bootstrap reference checkout being prepared separately from app source.
- Frozen leanVM public clone checked out at 59c2984df79cc9ff1914e547c5d5d390fffc8f3e, clean. Rust dependency build in progress.

Evidence lives at /var/lib/orb-node/work/keccak-gkr-evidence. No matched E2E baseline or allocation measurement yet. Historical figures are not current measurements. All requested acceptance gates remain open. No TTL/lifecycle tools exposed in this session; no credentials or snapshots used.

Acceptance targets remain distinct: <1.15 s / <8.633 GiB; <3 s / <4 GiB; <920 ms / <5.5 GiB. None claimed met.

## Bootstrap and initial gates closed

- Rebuilt turbo-lean@29d85f7 with the already-recorded meta/compiler-fix.patch in /var/lib/orb-node/work/turbo-lean-bootstrap, without new compiler edits. Result SHA256 79b805002e329a6eee167403265daa91b50467a4169c8e735d0e843eca3cc6ba exactly matches historical repaired compiler. No babylon build.
- Reconstructed all four omitted XMSS1400 fixtures; every committed SHA256 matches exactly. Additional XMSS4/16 fixtures are fresh seed 20261113 inputs.
- Baseline application built via recorded cache_manager hardware-field setup and lean-native. Binary SHA256 3f9f92ed09bff8244f2afd209e31714a934534fde40801f80681dcfed85cc567. Exported shard_a_mul disassembly contains scalar 128-bit VPCLMUL. No standalone native GKR symbols in the E2E binary.
- First Rust harness build omitted target-cpu=native because nested leanVM .cargo/config.toml is not inherited from the harness directory. Aborted that comparison and retained its logs under diagnostic-portable-rust-aborted; not an acceptance baseline. Corrected Rust build explicitly uses RUSTFLAGS=-C target-cpu=native. Reference leanVM remains clean.
- Native kernel correctness passed: 128 instances x24 rounds vs Spec, RMFE vs Spec, F192 fold vs Model, transpose, ternary. These are correctness results, not E2E performance gates.
- WholeRepoAxiomAudit passed: 10,316 declarations / 41 modules, 0 rejections; axioms exactly propext and Quot.sound. GKR audit 347 declarations / 0 rejections. Static app purity passed 129 Lean files / no violations.
- External generated-C diagnostic profile on one XMSS4 proving call counted 115,581,312 productRangeFlat constructor allocations, 3,698,600,448 requested object bytes (headers included, allocator rounding excluded). Instrumented productRangeFlat aggregate thread CPU 3.694 s, pairSumsRangeFlat 0.529 s; timers are nested and diagnostic, and a build ran concurrently. Not acceptance timings. Diagnostic proof is byte-identical to the ordinary baseline proof and independently passes Rust verification.

## Matched baseline in progress

Durable user service keccak-gkr-baseline-native.service, MemoryMax26G / MemoryHigh24G, LEAN_NUM_THREADS=1. No builds while timed comparisons run. Runner uses warmup+repeat3 recomputation, fresh processes under time -v, sequential Rust/Lean, independent verify-eth positional inputs proof N 1.

First pair (not final >=5-pair certification):

| XMSS | Lean mean s | GKR mean s | Rust mean s | Lean process peak KiB |
|---|---:|---:|---:|---:|
| 4 | 4.886916880 | 1.027523103 | 0.169739556 | 1356760 |
| 16 | 9.237542754 | 3.174856353 | 0.177125965 | 1457320 |
| 1400 | pending | pending | 3.484690861 | pending |

Small Lean proofs independently verified. XMSS1400 running. Resource samples in baseline-resource-samples.jsonl so far show no memory-high/max/OOM events or memory pressure after scope repair. perf_event_paranoid=4 blocks perf counters. Candidate first edit: explicit structural scalar-UInt64 bucket recursion in existing product-bit loop, proved equal to current foldRange maskedAddE. NOT YET EDITED: waiting for full matched baseline before implementation changes.

## Complete pre-edit baseline and candidate 1

Full baseline completed: all 4/16/1400 proofs independently Rust verified. XMSS1400 timed recomputations 442.641455299, 481.114033886, 562.143011421 seconds; mean 495.299500202 seconds, GKR mean 213.445628139 seconds, bus 51.329203183 seconds, PCS 203.279574811 seconds. Peak RSS 15,736,782,848 bytes; wire 359217 bytes. Native Rust mean 3.4846908617 seconds. Strong pass-to-pass drift requires final alternating pairs; historical 370.612 seconds is not reproduced. All target gaps are retained in baseline-summary.json.

Candidate 1 replaces per-position E accumulation with three scalar UInt64 Fin.foldl loops. An initially proposed explicit recursive loop was rejected by unchanged whole-repo audit for generated ._unsafe_rec; that representation was discarded before native benchmarking. Revised implementation has an all-buffer/all-length/all-offset/all-shift refinement proof checked by Lean. Whole-repo audit zero rejections, candidate strict audit passes; static purity 130 files zero violations; frozen protocol hashes unchanged. Native build and 972-case differential suite pending, as are matched timing/34-mutant/final-pair gates. Generated C scalar worker has UInt64 accumulator and no constructor/UInt64 boxing calls in its loop. This is code-generation evidence, not an E2E performance result.

## Candidate 1 complete; candidate 2 queued correctness/profile

Candidate 1 all 4/16/1400 matched runs completed warmup+repeat3, fresh process RSS, Rust independent positional verification, and proof bytes identical to baseline. Native 972-case differential and native 128x24/RMFE/F192 parity passed. Both Lean and frozen Rust accepted all 34 baseline mutant inputs and rejected all 34 mutations; mutation metadata agrees.

Observed XMSS1400: total 364.016344206 s, GKR 164.780370001 s, peak RSS 16061480960 B, wire 359217 B. Rust control 4.103612655 s versus baseline 3.484690862 s. Unchanged phases also changed substantially (PCS 144.39 s versus 203.28 s); raw total difference is not attributable solely to GKR, and RSS regressed. Small totals 6.995035144 s / 14.053597079 s versus baseline 4.886916881 s / 9.237542755 s, with slower Rust controls. No target met; final alternating pairs still open. Full evidence candidate1/status.json and candidate1-summary.json.

Candidate 2 commit 7866d97 fuses direct limb reads into an E accumulator. Definitional refinement and whole audit pass (10318 declarations, 41 modules, zero rejections); static purity/frozen protocol hashes pass. The isolated generated-C XMSS4 profile disproves the intended ownership reuse: 115507200 inner accumulator constructors remain. Generated C releases the accumulator before buffer-read join points, so constructor reuse does not occur. Diagnostic proof identical and independently verified; no allocation reduction claimed. Full-size read-only bus/GKR diagnostic in progress, controller SIGSTOP deliberately prevents timing overlap and diagnostic finally resumes it. Durable service keccak-gkr-candidate2-campaign.service runs remaining Rust mutants then matched benchmarks.

Outside-app prototype with a noinline scalar-limb accumulation helper emits an exclusive-object reuse path and keeps the accumulator owned through buffer reads. Candidate3 drafts and workflow are prepared in evidence, unapplied and not yet benchmarked. Do not count prototype codegen as an acceptance gate.

Installed turbo-lean rejects documented --policy strict-proofs CLI option. Available per-file audit of both new refinement theorems passes with zero vacuous/trivial specs or warnings. Broader named strict-policy gate remains unsupported, not passed. No lease/lifecycle tools exposed.

## Candidate 2 complete; candidate 3 allocation reduction confirmed

Candidate 2 completed all matched 4/16/1400 warmup+repeat3, byte parity, fresh RSS and positional Rust verification. XMSS1400 total 362.538436913 s, GKR 149.734391740 s, peak RSS 15837421568 B; Rust control 3.963599142 s. Not a decisive total-time improvement over candidate1 (364.016 s) amid large control/phase drift. Full-size diagnostic (not acceptance timing) measured 29,569,843,200 inner constructors / 946,234,982,400 requested object bytes, and 226,492,416,000 potential row-fold COW payload bytes. Bus report is committed separately; no bus edits.

Saved baseline/candidate1/candidate2 native binaries all pass the repository's unchanged Maxwell symbol+ISA gate: zero unexpected undefined/forbidden FFI symbols; each has 2879 ZMM operands and 979 VPCLMULQDQ instructions. These whole-binary counts do not imply vector GKR integration. Rust reference is clean at exact 59c2984df79cc9ff1914e547c5d5d390fffc8f3e.

Candidate3 implementation commit 9935c34 uses a noinline UInt64-limb helper to retain ownership across branching planar reads. Whole audit 10318 declarations / 41 modules / zero rejections; definitional bucket refinement passes; 972-case native differential and existing native kernel parity pass. Actual-module generated-C XMSS4 diagnostic counts ZERO per-position product-loop constructors, with 72192 initial bucket E objects retained. Diagnostic proof byte-identical and independently verified. This is allocation evidence, not a small-case speed gate. Normal native helper disassembly saved.

Active durable workflow: keccak-gkr-candidate3-campaign.service. It runs 34 dual-verifier mutations, unchanged binary audit, then matched 4/16/1400 benchmarks (no overlapping diagnostics). Status candidate3-campaign-status.json; native benchmark status candidate3/status.json when started. Prior candidate2 full diagnostic controller was deliberately stopped with SIGSTOP and automatically resumed in a finally block; it completed cleanly before candidate2 acceptance timings.

Candidate4 drafts outside app: candidate4-Flat.lean (consume tape before fold), candidate4-FoldRows.lean (all-tapes rfl refinement), candidate4-FoldRowsOwnershipCheck.lean (72 native cases), candidate4-campaign.py. Not applied or checked as app. Prototype theorem and generated C checked outside app. Workflow is not started, and requires complete candidate3 plus candidate4-ready.flag for local selection. Review its native test/build when activated; do not claim prototype gates as completed app gates.

Remaining: finish candidate3 full matched gates; assess candidate4 ownership change separately with all gates; full-size final allocation profile to measure actual removal (no extrapolated full-size counts); fresh baseline control for drift; final >=5 alternating same-host Rust/Lean pairs, each warmup+repeat3 and independent verification, with fixed winning binary. Report every target/historical gap. Export final report, bundle, patch, SHA256 and request coordinator harvest before cleanup. Named --policy strict-proofs tool mode remains unsupported; async request for compatible binary pending; continue other gates.
