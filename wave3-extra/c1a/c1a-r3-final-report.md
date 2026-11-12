## W3-C1a-r3 Final Report (`lean-native` ZMM + `ByteArray` SIMD & Imported `LeanVmXmss` Lowering)

### 1. Summary & Artifacts
- **Patch**: `/var/lib/orb-node/work/caches/xmss-hub-v3/wave3/c1a/compiler-fix-w3-c1a.patch` (`249,433` bytes)
  - SHA-256: `c3b93b720d76d5468375f4d30247488382fec23e84983b570aa0002c81417277`
- **Status Report**: `/var/lib/orb-node/work/caches/xmss-hub-v3/wave3/c1a/STATUS.md`
  - SHA-256: `83193be4268625aad06b6f92eeceb44216f6f70f4f021ea8ff9e7229c2daf482`
- **Compiler Binary**: `/var/lib/orb-node/work/caches/xmss-hub-v3/bin/lean-native` (and `lean/.lake/build/bin/lean-native`)
  - SHA-256: `52eca7de3521e1b33ed552fb2af735f52e1fd6be93b041240170fd6f4491f1f0`
- **Owned Files Modified** (`git -C "$HUB/toolchain/turbo-lean" status`):
  - `lean/LeanNative/Backend/LLVM.lean`
  - `lean/LeanNative/Driver/BuildExe.lean`
  - `lean/LeanNative/IR/AST.lean`
  - `lean/LeanNative/IR/Bridge.lean`
  - `lean/LeanNative/IR/BridgeHelpers.lean`
  - `lean/LeanNative/IR/Types.lean`
  - `scripts/fixtures/BuildExeP0.lean`
  - `scripts/test_build_exe_p0.py`
  - Zero edits in `$HUB/LeanVmXmss/**` or `$HUB/references/leanVM/**`, and zero occurrences of `--allow-multiple-definition` in `BuildExe.lean`.

### 2. Test Suite Results
- `python3 scripts/test_build_exe_p0.py`: `Ran 1 test in 23.431s — OK`
- `python3 scripts/test_p0_trust_boundary.py`: `Ran 12 tests in 32.881s — OK` + `Ran 20 tests in 95.050s — OK`
- `LeanVmXmss` standalone builds & execution (`Model.Bus.Native`, `Model.Field.NativeKernel`, `Tests.Hub.ShardAHw`, `Tests.Field.Native`, `Tests.Field.NativeMulProbe`, `Tests.Keccak.LaneRunner`, `Tests.Keccak.ImportedRunner`): all build and pass execution checks cleanly.

### 3. `objdump -d` Disassembly Proof (`%zmm` Vector Loop + Zero Software 64-Shift `nativeSelect` Loops)
- **`p0_zmm_slice_kernel` (`BuildExeP0`)**:
```asm
   4f59a: 62 f2 fd 48 59 05 3c 1b 1f 00  vpbroadcastq 0x1f1b3c(%rip),%zmm0
   4f5b0: 62 b1 fe 48 6f 8c fe 18 00 00 00 vmovdqu64 0x18(%rsi,%r15,8),%zmm1
   4f5bb: 62 b1 fe 48 6f 94 fa 18 00 00 00 vmovdqu64 0x18(%rdx,%r15,8),%zmm2
   4f5c6: 62 f3 75 48 44 da 00           vpclmullqlqdq %zmm2,%zmm1,%zmm3
   4f5cd: 62 f1 7d 48 70 e1 ee           vpshufd $0xee,%zmm1,%zmm4
   4f5d4: 62 f1 7d 48 70 d2 ee           vpshufd $0xee,%zmm2,%zmm2
   4f5db: 62 f3 5d 48 44 d2 00           vpclmullqlqdq %zmm2,%zmm4,%zmm2
   4f5e2: 62 f1 e5 48 6c e2              vpunpcklqdq %zmm2,%zmm3,%zmm4
   4f5e8: 62 f1 e5 48 6d d2              vpunpckhqdq %zmm2,%zmm3,%zmm2
   4f5ee: 62 f1 dd 48 ef d2              vpxorq %zmm2,%zmm4,%zmm2
   4f5f4: 62 f3 ed 48 ce d0 63           vgf2p8affineqb $0x63,%zmm0,%zmm2,%zmm2
   4f5fb: 62 b3 f5 48 25 94 f9 18 00 00 00 96 vpternlogq $0x96,0x18(%rcx,%r15,8),%zmm1,%zmm2
   4f607: 62 b1 fe 48 7f 94 f8 18 00 00 00 vmovdqu64 %zmm2,0x18(%rax,%r15,8)
```
- **`shard_a_mul` / `shard_a_clmul_lo` / `shard_a_clmul_hi` (`Model.Field.NativeKernel` & `Tests.Hub.ShardAHw`)**:
```asm
0000000000068cf0 <shard_a_clmul_lo>:
   68cf0: c4 e1 f9 6e c7       vmovq  %rdi,%xmm0
   68cf5: c4 e1 f9 6e ce       vmovq  %rsi,%xmm1
   68cfa: c4 e3 79 44 c1 00    vpclmullqlqdq %xmm1,%xmm0,%xmm0
   68d00: c4 e1 f9 7e c0       vmovq  %xmm0,%rax
   68d05: c3                   ret
```

<!-- GOAL_COMPLETE -->