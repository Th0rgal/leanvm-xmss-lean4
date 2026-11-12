# Wave 3 C1a (`W3-C1a-r3`) — `lean-native` ZMM + `ByteArray` SIMD Lowering & Imported `LeanVmXmss` Fix

## Summary
- Completed Wave 2/3 `lean-native` ZMM (`<8 x i64>`) + `ByteArray` (`LNIRType.sarray .i8`) SIMD lowering and imported module LCNF lowering in `/var/lib/orb-node/work/caches/xmss-hub-v3/toolchain/turbo-lean`.
- Rebuilt `lean/.lake/build/bin/lean-native` (`lean-native-core` too) and installed `$HUB/bin/lean-native`.
- Verified `python3 scripts/test_build_exe_p0.py` and `python3 scripts/test_p0_trust_boundary.py` pass completely.
- Verified `LeanVmXmss` local and imported modules (`Model.Field.NativeKernel`, `Model.Bus.Native`, `Tests.Field.Native`, `Tests.Field.NativeMulProbe`, `Tests.Hub.ShardAHw`, `Tests.Keccak.LaneRunner`, `Tests.Keccak.ImportedRunner`) build and execute cleanly through `lean-native build-exe --standalone`, lowering to hardware `vpclmulqdq` without software 64-shift `nativeSelect` expansions.

## Root Causes Fixed
1. **Impure LCNF `impureExt` Panic & Ordering (`Bridge.lean`, `BuildExe.lean`)**:
   - Saved and restored `Environment` around `Lean.Compiler.LCNF.toImpure.run` in `ingestLCNFMonoDecl` so `Lean.Compiler.LCNF.emitC` does not see already-populated `impureExt` state, and ordered `emitC` before `ingestBuildExeModuleDecls`.
2. **Imported Module Discovery & `.lake/build/native-c/` Cache Fallback (`BuildExe.lean`, `BridgeHelpers.lean`)**:
   - Checked both `/ir/` and `/native-c/` for `.c.o.export` and `.c.o` objects when linking imported modules cached by `turbo-lean`.
   - Included `@[export]` declarations from imported non-sysroot modules in `emitLeanCFromSourceFile` traversal while limiting hard non-scalar `@[export]` errors in `ingestBuildExeModuleDeclsWith` to local declarations (`isLocalExported`).
   - Bounded `emitModuleTelemetryEvents` to declarations with `d.body.nodeSize <= 64` so large unrolled functions (e.g., `shard_a_inv`, `nodeSize = 1604`) never stall `build-exe` when `SANDBOXED_TELEMETRY_BATCH_ONLY` is unset, while running `runDefaultPipelineDecl` when `d.body.nodeSize <= 128 || (d.body.nodeSize <= 256 && cdHasSeqFor d.body)`.
3. **Trusted GF/SIMD Intrinsic Recognition (`BridgeHelpers.lean`)**:
   - Added `Tests.Field.Intrinsic.{clmul64, clmul64Hi}` (`altClmul64`, `altClmul64Hi`) alongside `LeanNative.IR.*` intrinsics (`clmul64`, `clmul64Hi`, `gf2Affine64`, `gf2AffineInv64`, `ternaryLogic64`).
   - Updated `trustedG0IntrinsicCall?` to accept `@& ByteArray` (`mdata borrowed` type wrappers on `uget64LE`) and `eraseBinderNamesAndPrefix` signature equivalence.
4. **Impure `ByteArray` (`LNIRType.sarray .i8`) & Tail-Recursive ZMM Loop Lowering (`BridgeHelpers.lean`, `LLVM.lean`)**:
   - Extended `rewriteImpureUset64LETypes` to propagate `.sarray .i8` across local helper calls (including `__ln_tailrec_self` and `._redArg`) and ran it after `rewriteImpureSelfFapName`.
   - Allowed `.sarray .i8` in `checkImpureLetTypesM` for impure `let` bindings and join-point parameters/results.
   - Updated `tryLowerBoundedTailRecBody?` to recognize impure LCNF's `uint64_dec_lt` pattern (`let v := select (lt i n) 1 0; let z := eq v 0; ite z exit step`).
   - Extended `evalAffineIdxExpr?` in `LLVM.lean` to fold let-bound constant shift amounts (`let s := 3; shl idx s`) and 64-bit `toUSize` masks (`bitAnd x 0xffffffffffffffff`).
   - Added backward liveness pruning (`liveLetsRev`) in `emitZmmSliceLoopWithRem?` so dead loop-header condition temporaries copied into `preBinds` do not block `<8 x i64>` AVX-512 (`%zmm`) vectorization.

## Verification Evidence
- `python3 scripts/test_build_exe_p0.py`: **PASS** (1 test, 23.4s) — verifies `p0_kmul`, `p0_emul{0,1,2}`, and `p0_zmm_slice_kernel` differential correctness and `objdump -d` disassembly (`vpclmullqlqdq %zmm*`, `vgf2p8affineqb %zmm*`, `vpternlogq %zmm*`, `vmovdqu64 %zmm*`).
- `python3 scripts/test_p0_trust_boundary.py`: **PASS** (12 unit + 20 integration tests).
- `LeanVmXmss` standalone builds & runs:
  - `Model.Bus.Native` + `Model.Field.NativeKernel`: lowered 51 LCNF declarations (`shard_a_mul`, `shard_a_clmul_lo`, `shard_a_clmul_hi` emit `vpclmullqlqdq` with 0 `call` instructions and 0 software 64-shift loops).
  - `Tests.Hub.ShardAHw`: lowered 10 LCNF declarations (`shard_a_mul` emits `vpclmullqlqdq`).
  - `Tests.Field.Native`: lowered 19 LCNF declarations and passed execution check.
  - `Tests.Keccak.LaneRunner` (25 LCNF declarations) and `Tests.Keccak.ImportedRunner` (75 LCNF declarations): built and passed execution checks.

## Deliverables
- Patch: `/var/lib/orb-node/work/caches/xmss-hub-v3/wave3/c1a/compiler-fix-w3-c1a.patch`
- Status: `/var/lib/orb-node/work/caches/xmss-hub-v3/wave3/c1a/STATUS.md`
