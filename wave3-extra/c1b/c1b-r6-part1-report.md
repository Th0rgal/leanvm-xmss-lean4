All deliverables complete. Final report:

---

# W3-C1b-r6 — Compiler Fix Complete (eqSat/TV-gate hang + loop vectorization/noalias)

## Deliverable 1 — SymbolicTV expression-size budget bailout (hang fix)
`symExecDecl`'s unshared expression trees grow exponentially on long pure-scalar let-chains. Added a fail-closed **estimator** (not touching proof-unfolded `symExecCode` internals) in `Pass.lean` (`estScalarExprNodes`/`estExprNodes`/`estCodeNodesWalk` with 4× seqFor-unroll feedback, peak-tracking, cap `symTvMaxExprNodes := 65536`), wired as bailouts in `ofHybridVerifiedContract` (kernel-proven fallback), `ofCodeTransform` (`CodeRefines.refl`), `gateDeclWithSymbolicTV` (EqSat.lean), and `loopVectorizeOptPass`:

| Input | Before | After |
|---|---|---|
| BK1/BK2/BK3 | 0.36s / 0.42s / 4.74s | 0.68s / 0.44s / 0.69s |
| BK4 | >120s hang | 0.76s |
| BK48 (18,591-line .ll) | infinite hang | 11.1s |

Escape hatch: existing `--verified-kernel-only` / `--baseline` flags cover this role (documented in patch; no redundant `--no-eqsat` added).

## Deliverable 2 — Vectorization emission (`LLVM.lean`)
1. **Width 8**: x86 `!8 = !{!"llvm.loop.vectorize.width", i32 4}` → `i32 8` (`emitMetadataFooter`).
2. **Noalias**: new `EmitState` fields (`aliasScopes`/`aliasNextId`/`aliasLines`), `factsProvePtrDisjoint` + `collectRawMemPtrs` + `setupLoopAliasScopes`; vectorizable `seqFor` bodies assign `!alias.scope`/`!noalias` to `rawLoad`/`rawStore` **only** for pointer pairs proven disjoint by loop-entry `RetainedFact.disjointSlices` (sound; pointers without a proven partner get no metadata). HoistExclusivity already hoists `lean_is_exclusive`/`m_size`/dataPtr to the preheader (verified in emitted IR — loop bodies contain zero calls).

Verified on a canonical `seqFor` probe (2 rawPtr params + `disjointSlices` facts): loop memory ops carry `!alias.scope !19, !noalias !20`, and Clang 23 `-O3 -march=znver5 -mprefer-vector-width=512` emits **32 lanes/iteration (8×4 unroll), `vpaddq %zmm` + `vmovdqu64 %zmm`**, no overlap guard.

## Deliverable 3 — 8-lane pure-Lean ByteArray benchmark + objdump proof
`scripts/fixtures/Vec8Kernels.lean`: `mix8` — 64 `ByteArray.uget` reads (erased proof args via `by simp; omega`), little-endian u64 assembly, `clmul64`/`clmul64Hi`, rotates, Keccak-χ boolean fold. Lowered by `compile-llvm` to a fully straight-line `l_mix8___redArg(ptr)` with **zero `lean_apply_*`/`lean_alloc_*`**. Differential correctness: optimized vs `--baseline` builds produce identical outputs (`0`, `7694775065703651960`).

Objdump proof (`-O3 -march=znver5 -mprefer-vector-width=512`, 71 insns, excerpt):
```asm
vmovdqu64 0x18(%rdi),%zmm1          ; ONE 512-bit load of all 64 ByteArray bytes
vpclmullqlqdq %xmm2,%xmm1,%xmm0     ; carry-less multiply (8 lanes)
vprolq $0x1f,%zmm1,%zmm5            ; vectorized rotates
vpternlogq $0x96,%zmm5,%zmm1,%zmm6  ; chi-fold
vpternlogq $0x96,%zmm6,%zmm3,%zmm13
vextracti64x4 $0x1,%zmm6,%ymm13     ; xor-tree reduction
```
Zero calls of any kind in the kernel body; `lean_apply`/`lean_alloc` count: **0**.

## Regressions (all green)
`lake build` (416 jobs) · `python3 scripts/test_build_exe_p0.py` OK (21.1s) · `Keccak/Native.lean` compile-llvm 1.45s · `Bus/Check.lean` build-exe 6.3s, kernels run correct · gate scan: no `sorry`/`native_decide`/`Classical.choice`/new `@[extern]`/`unsafe` in modified compiler sources.

## SHA-256 manifest
```
ba5c99d8e8bb8f237409c1626a76b1bf42bcb359f92e2b310a535fcf7e2e4899  wave3/c1b/compiler-fix-w3-c1b.patch
aae0ea584b9b00b3e6e94f754ebb1b35af01f654e9425cfce4cb81a00d39a3af  wave3/c1b/vec8-kernel-opt.ll
69e5014b0daa5df1fcb7d3b229cb38e054d2df4a8788a41e8ebd7cc42dec8609  wave3/c1b/noalias-seqfor-probe.ll
19f078460538b1f023fb2b7c5826d0952f0e6505740f306453ed47f110ff029e  wave3/c1b/vec8-mix8-objdump-znver5.txt
20942301ca6c874322135987acbef1ca22a292947fe660c1c7b00e3454bb2034  toolchain/.../Transform/Pass.lean
f48b95aa2282113865005bca8361274942fb22959cbd7d1b915597543e61ad1c  toolchain/.../Transform/EqSat.lean
f898a0cf0ba7de66b897cc9f1b44113e60c4e6875a32d75d23b0050471a9c060  toolchain/.../Transform/LoopVectorizeOpt.lean
9dda07dae000ea1bca9801e5f884e7d3fce447e84b3bbd19319fb65ab864ffd4  toolchain/.../Backend/LLVM.lean
4fbb3a73374214f687a9c9a88562e70ff733d82bec0d4f0c45c7347d91377e37  toolchain/.../fixtures/Vec8Kernels.lean
731cba740fb79059b3622458b246752bdbdf750e7a93dcba8c3b240c20972c56  toolchain/.../fixtures/BuildExeP0.lean
f80d05747e659ae7d3bb4fd730ad3614715f0b2e2806bffbba0b69c5c6fdbcfc  toolchain/.../test_build_exe_p0.py
5bf3307792131732874ad58d1792a090a48025ada6b54ef20fb53fad3e5f93b6  bin/lean-native
```
Patch saved to `$HUB/wave3/c1b/compiler-fix-w3-c1b.patch` (1020 lines, 8 files, +636/−99), binary synced to `$HUB/bin/lean-native`, `sync` done.