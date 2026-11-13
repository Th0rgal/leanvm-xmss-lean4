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
