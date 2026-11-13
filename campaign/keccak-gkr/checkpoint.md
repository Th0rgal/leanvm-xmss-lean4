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
