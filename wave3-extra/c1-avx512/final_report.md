All state on `mmcnagnedk` has been dumped in full into mission events (zero lines truncated).

### 1. SHA-256 Checksums & Line/Byte Counts
- `/tmp/wave3-c1a-turbo-lean.patch`: **270 lines / 17,070 bytes** — `7c20f10e7c07079760c2b498e5d8f1335ae7224a2f3479ea0d792a3a6b481843` (identical to `/tmp/turbo-lean-bak` baseline; `$HUB/LeanVmXmss` is not a git repo and was untouched)
- `$HUB/meta/compiler-fix.patch`: **481 lines / 27,150 bytes** — `05d8024587ec0046b363a8821a899a5bd7c75a5eea56a68515dd558e1b8d526d`
- `$HUB/bin/lean-native`: `30702b47e3aadfc61f3c509ea7a6821d835131e63b1135eff989194695679e77`
- `$HUB/toolchain/turbo-lean/scripts/test_build_exe_p0.py` (untracked baseline): **145 lines / 7,806 bytes** — `f80d05747e659ae7d3bb4fd730ad3614715f0b2e2806bffbba0b69c5c6fdbcfc`
- `$HUB/toolchain/turbo-lean/scripts/fixtures/BuildExeP0.lean` (untracked baseline): **54 lines / 1,696 bytes** — `731cba740fb79059b3622458b246752bdbdf750e7a93dcba8c3b240c20972c56`
- `/tmp/c1a_ops.py`: `a4537c0f3807fcf46d2266bde3985e487cfd664f48e9cc4dab4ce84dfe187f27` (26 ops)
- `/tmp/c1b_ops.py`: `af35e677af92d36caf0b52b90ca158f272d8f31e4f180eb8d339c921ef562bbf` (21 ops)
- `/tmp/c1c_ops.py`: `79f34a9718534b8c41305d41b40ff8aa0b63ed87e8c4af825e55a18f8007d633` (30 ops)
- `/tmp/apply_c1.py`: **236 lines / 9,289 bytes** — `56487d2ed0bd359919cfa6fe7c5dc128d27461e0f2be08510da3c8fc99950e06`
- `/tmp/c1_map.json`: **126,786 bytes** — `03f998bb845d3e89634d5462d73f6f94c1e4da470e1cb6506547f0af46dc703e`
- `/tmp/dump_slice.py`: **31 lines / 1,137 bytes** — `3efada5de9607740f7bd0456e95aaf450076d0b80d418f68e11aa1cdc627ef54` (printed in full above)
- `/tmp/p0_c1c_bodies.txt`: **345 lines / 26,018 bytes** — `7e22db2fd85a48e1b699313cb604580b1d44b903fc910c2743f10bb1a695679e` (printed in full above)

### 2. Applied State vs. Complete Reconciliation Blueprint
- **Currently in `$HUB/toolchain/turbo-lean`**: Clean baseline (`29d85f7` + Wave 1/2 uncommitted edits to `LLVM.lean`, `BuildExe.lean`, `scripts/fixtures/BuildExeP0.lean`, `scripts/test_build_exe_p0.py`, matching `/tmp/turbo-lean-bak` byte-for-byte). No partial/broken edits were written onto `$HUB/toolchain/turbo-lean`.
- **Complete Reconciliation Blueprint Ready to Apply on Fresh VM**:
  1. **`Pass.lean`, `EqSat.lean`, `LoopVectorizeOpt.lean`**: Apply `c1b#0..5` directly (SymbolicTV AST-size budget `codeSymTvBudgetExceeded` + helper/`.seqFor`/`.sarray .i8` inlining in `EqSat.lean` so specialized `Fin.foldl.loop` helpers inline into exported `p0_zmm_*` wrappers).
  2. **`BuildExe.lean`**: Reconcile `c1a#0` (`.c.o.export` -> `.c.o` fallback), `c1c#2` (`!isTrustedIntrinsicOrHelperDecl` filter in `emitLeanCFromSourceFile`), and `c1a#1` (node-size gated optimization in `buildNativeExecutable`).
  3. **`BridgeHelpers.lean`** (without touching `AST.lean`, `RealLCNFBridge.lean`, `Bridge.lean`, or `Proofs/*.lean`):
     - Reconcile `c1a#2..4`, `c1a#10..13`, `c1a#17` (omitting reverted debug prints `c1a#14..16`/`19..21`) and `c1c#0,1,3,4`.
     - Admit non-borrowed `.sarray .i8` (`ByteArray`) parameters in `ingestImpureDeclViaReal` (`p.borrow = false` in `zmmF192x8`, `zmmNttButterfly`, `zmmKeccakRoundX8`, `zmmGfniRmfeX8`).
     - Lower both `Fin.foldl.loop._at_.zmm*.spec_0` (self-tail-recursive `Nat.decLt` / `USize.ofNat` / `Nat.add` -> `.seqFor`) and the wrapper pattern (`let nNat := USize.toNat n; let z := 0; Fin.foldl.loop ... nNat acc z; dec ...`) directly in `ingestImpureDeclViaReal`, mapping `uget64LE` -> `lean_native_uget64le`, `uset64LE` -> `lean_native_uset64le`, `gf2Affine64` -> `lean_native_gf2affine64`, and `ternaryLogic64` -> `lean_native_ternary64`.
  4. **`LLVM.lean`**:
     - Reconcile `c1b#6..20` (`constU64Bindings`, `!alias.scope`/`!noalias`, scalar GFNI), `c1a#18,22,23`, and `c1c#5..23` (`exclArrVars`, `lean_native_uget64le`/`uset64le`/`gf2affine64`/`ternary64` scalar + `<8 x i64>` `%zmm` loop vectorizer `emitZmmSeqFor`, `findUnsupportedLLVMCallInDecl` admission for `.sarray .i8` and `lean_native_uget64le`/`uset64le`/`gf2affine64`/`ternary64`, LLVM 18 X86 intrinsic `declare`s `@llvm.x86.pclmulqdq[.512]`, `@llvm.x86.avx512.pternlog.q.{128,512}`, `@llvm.x86.vgf2p8affineqb.{128,512}`, `@llvm.fshl.{i64,v8i64}`, and `emitMetadataFooter` `"target-cpu"="x86-64-v2"` + AVX-512/VPCLMULQDQ/GFNI `"target-features"` + `"prefer-vector-width"="512"` `"min-legal-vector-width"="512"`).
  5. **`BuildExeP0.lean` & `test_build_exe_p0.py`**: Apply `c1c#24` directly to baseline `BuildExeP0.lean` (54L -> 376L) and reconcile `c1a#24..25` + `c1c#25..29` onto `test_build_exe_p0.py`.