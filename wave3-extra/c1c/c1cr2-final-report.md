### 1. Audit-Clean Pure-Lean Surface (`LeanVmXmss/Model/Prim/Slice64.lean` Ready)
These definitions use **zero** `import LeanNative`, **zero** `@[extern]`, **zero** `unsafe`, **zero** `._unsafe_rec` (via `Fin.foldl`), **zero** `sorry` / `native_decide` / `Classical.choice`, **zero** `BEq UInt64` (`==`), and transitive axioms strictly `⊆ {propext, Quot.sound}` (`SLICE64_AUDIT_OK checked=13 unsafe=0 extern=0 unsafe_rec=0 axioms_subset_propext_quotsound=true`):

```lean
set_option autoImplicit false
set_option compiler.ignoreBorrowAnnotation true

namespace LeanVmXmss.Model.Prim.Slice64

/-- Audit-clean pure-Lean carryless 64-bit multiply low (`PCLMULQDQ` low 64 bits). -/
def clmul64 (a b : UInt64) : UInt64 :=
  Fin.foldl 64 (fun acc i =>
    let iu := i.val.toUInt64
    let mask := (0 : UInt64) - ((b >>> iu) &&& 1)
    acc ^^^ ((a <<< iu) &&& mask)) 0

/-- Audit-clean pure-Lean carryless 64-bit multiply high (`PCLMULQDQ` high 64 bits). -/
def clmul64Hi (a b : UInt64) : UInt64 :=
  Fin.foldl 63 (fun acc i =>
    let iu := (i.val + 1).toUInt64
    let mask := (0 : UInt64) - ((b >>> iu) &&& 1)
    acc ^^^ ((a >>> (64 - iu)) &&& mask)) 0

/-- Audit-clean pure-Lean GF(2) 8-bit dot product helper for `gf2Affine64`. -/
def gf2Dot8 (row x : UInt64) : UInt64 :=
  Fin.foldl 8 (fun s j =>
    let ju := j.val.toUInt64
    s ^^^ (((row >>> ju) &&& 1) &&& ((x >>> ju) &&& 1))) 0

/-- Audit-clean pure-Lean packed 8-byte GF(2) affine transform (`VGF2P8AFFINEQB` lane semantics). -/
def gf2Affine64 (x m : UInt64) (imm : UInt8) : UInt64 :=
  let immU := imm.toUInt64
  Fin.foldl 8 (fun out b =>
    let bu := b.val.toUInt64
    let xb := (x >>> (bu * 8)) &&& 0xff
    let yb := Fin.foldl 8 (fun acc i =>
      let iu := i.val.toUInt64
      acc ||| (gf2Dot8 ((m >>> (iu * 8)) &&& 0xff) xb <<< iu)) 0
    out ||| ((yb ^^^ immU) <<< (bu * 8))) 0

/-- Audit-clean pure-Lean 3-input bitwise ternary truth-table operator (`VPTERNLOGQ` lane semantics). -/
def ternaryLogic64 (a b c : UInt64) (imm : UInt8) : UInt64 :=
  let immU := imm.toUInt64
  Fin.foldl 64 (fun acc i =>
    let iu := i.val.toUInt64
    let idx := (((a >>> iu) &&& 1) <<< 2) ||| (((b >>> iu) &&& 1) <<< 1) ||| ((c >>> iu) &&& 1)
    let bit := (immU >>> idx) &&& 1
    acc ||| (bit <<< iu)) 0

/-- Audit-clean pure-Lean little-endian 64-bit word read from `@& ByteArray` at 64-bit word index `wordIdx`. -/
def uget64LE (b : @& ByteArray) (wordIdx : USize) : UInt64 :=
  let base := wordIdx * 8
  if base + 8 <= b.usize && base <= base + 8 then
    (b.get! base.toNat).toUInt64 |||
    ((b.get! (base.toNat + 1)).toUInt64 <<< 8) |||
    ((b.get! (base.toNat + 2)).toUInt64 <<< 16) |||
    ((b.get! (base.toNat + 3)).toUInt64 <<< 24) |||
    ((b.get! (base.toNat + 4)).toUInt64 <<< 32) |||
    ((b.get! (base.toNat + 5)).toUInt64 <<< 40) |||
    ((b.get! (base.toNat + 6)).toUInt64 <<< 48) |||
    ((b.get! (base.toNat + 7)).toUInt64 <<< 56)
  else 0

/-- Audit-clean pure-Lean little-endian 64-bit word write into `ByteArray` at 64-bit word index `wordIdx`. -/
def uset64LE (b : ByteArray) (wordIdx : USize) (val : UInt64) : ByteArray :=
  let base := wordIdx * 8
  if base + 8 <= b.usize && base <= base + 8 then
    let i := base.toNat
    let b := b.set! i val.toUInt8
    let b := b.set! (i + 1) (val >>> 8).toUInt8
    let b := b.set! (i + 2) (val >>> 16).toUInt8
    let b := b.set! (i + 3) (val >>> 24).toUInt8
    let b := b.set! (i + 4) (val >>> 32).toUInt8
    let b := b.set! (i + 5) (val >>> 40).toUInt8
    let b := b.set! (i + 6) (val >>> 48).toUInt8
    b.set! (i + 7) (val >>> 56).toUInt8
  else b

@[inline]
def rol64 (x : UInt64) (s : UInt64) : UInt64 :=
  (x <<< s) ||| (x >>> (64 - s))

@[inline]
def gf64Reduce1B (lo hi : UInt64) : UInt64 :=
  lo ^^^ clmul64 hi 0x1b ^^^ clmul64 (clmul64Hi hi 0x1b) 0x1b
```

---

### 2. Compiler Changes (`$HUB/toolchain/turbo-lean`)
- `lean/LeanNative/IR/Types.lean`: Replaced fuel-recursive helpers on `clmul64`, `clmul64Hi`, `gf2Dot8`, `gf2Affine`, `gf2Affine64`, `ternaryLogic64`, `uget64LE`, and `uset64LE` with structural `Fin.foldl` loops and overflow-guarded `ByteArray` bounds checks (`0 ._unsafe_rec`).
- `lean/LeanNative/IR/BridgeHelpers.lean`: Added suffix-aware standalone intrinsic recognition (`matchesIntrinsicName`) so user-defined `clmul64`, `clmul64Hi`, `gf2Affine64`, `ternaryLogic64`, `uget64LE`, and `uset64LE` in any module/namespace (with zero `LeanNative` imports) lower to `lean_native_*` LNIR calls, and added `Fin.foldl` / `Fin.foldl.loop` specialization lowering directly into `.seqFor`.
- `lean/LeanNative/Backend/LLVM.lean`:
  - Added `<8 x i64>` (`%zmm`) loop auto-vectorization (`analyzeZmmIndexExpr`, `analyzeZmmStepBody`, `emitZmmSeqForLoop`) over `seqFor` loops mutating `ByteArray` via `lean_native_uget64le` / `lean_native_uset64le`.
  - Hoisted `lean_native_ensure_exclusive_e1` once before vector/scalar dispatch and tracked `exclArrVars` in `EmitState` so exclusive `ByteArray` accumulators bypass redundant RC/COW checks in scalar tails and update in-place at `ptr + 24 + wordIdx * 8`.
  - Lowered `clmul64` / `clmul64Hi` to interleaved `<8 x i64>` `@llvm.x86.pclmulqdq.512` pairs (`vpclmullqlqdq` / `vpclmulhqhqdq` / `vpclmulhqlqdq %zmm`), `gf2Affine64` to `@llvm.bswap.v8i64` + `@llvm.x86.vgf2p8affineqb.512` (`vgf2p8affineqb %zmm`), `ternaryLogic64` to `@llvm.x86.avx512.mask.pternlog.q.512` (`vpternlogq %zmm`), and 64-bit rotates to `@llvm.fshl.v8i64` (`vprolq %zmm`).
  - Added grouped affine offset emission (`k * stride`) and single-comparison strided-lane disjointness (`stepVal >= trip`) to eliminate O(N²) alias checks on 25-lane Keccak-f[1600]×8.
- `lean/LeanNative/Driver/BuildExe.lean`: Auto-selects `$HUB/bin/clang` (Clang 23) with `-O3 -march=znver5 -mprefer-vector-width=512` when `znver5` / `avx512vpclmulqdq` are present.
- `scripts/fixtures/BuildExeP0.lean` & `scripts/test_build_exe_p0.py`: Removed `import LeanNative.IR.Types` so the fixture is 100% standalone, added the 4 ZMM slice kernels (`p0_zmm_f192x8`, `p0_zmm_ntt_butterfly`, `p0_zmm_keccak_round_x8`, `p0_zmm_gfni_rmfe_x8`), verified `%zmm` instruction emission via `objdump -d`, and verified bit-for-bit output parity against stock `lean -c` + `leanc`.

---

### 3. `objdump -d` Excerpts Proving Real `%zmm` Instructions
- **`zmm_f192x8_karatsuba`** (`vpclmul*qdq %zmm` + `vpternlogq %zmm` + `vmovdqu64 %zmm`):
```asm
   b9d20: 62 b1 fe 48 6f 9c ff 18 00 00 00  vmovdqu64 0x18(%rdi,%r15,8),%zmm3
   b9d2b: 62 b1 fe 48 6f a4 fe 18 00 00 00  vmovdqu64 0x18(%rsi,%r15,8),%zmm4
   b9d52: 62 f3 65 48 44 d4 00              vpclmullqlqdq %zmm4,%zmm3,%zmm2
   b9d59: 62 f3 65 48 44 ec 11              vpclmulhqhqdq %zmm4,%zmm3,%zmm5
   b9e06: 62 d3 ed 48 25 f4 96              vpternlogq $0x96,%zmm12,%zmm2,%zmm6
   b9e7a: 62 f3 15 48 44 f8 01              vpclmulhqlqdq %zmm0,%zmm13,%zmm7
   b9ec9: 62 b1 fe 48 7f 94 f8 18 00 00 00  vmovdqu64 %zmm2,0x18(%rax,%r15,8)
```
- **`zmm_ntt_butterfly`** (`vpclmul*qdq %zmm` + `vpxorq %zmm` + `vmovdqu64 %zmm`):
```asm
   ba3b0: 62 b1 fe 48 6f 0c c7              vmovdqu64 (%rdi,%r8,8),%zmm1
   ba3b7: 62 b1 fe 48 6f 94 c6 18 00 00 00  vmovdqu64 0x18(%rsi,%r8,8),%zmm2
   ba3c2: 62 f3 75 48 44 da 00              vpclmullqlqdq %zmm2,%zmm1,%zmm3
   ba3c9: 62 f3 75 48 44 d2 11              vpclmulhqhqdq %zmm2,%zmm1,%zmm2
   ba3e4: 62 b1 ed 48 ef 94 c0 18 00 00 00  vpxorq 0x18(%rax,%r8,8),%zmm2,%zmm2
   ba410: 62 f1 ed 48 ef c9                 vpxorq %zmm1,%zmm2,%zmm1
   ba416: 62 b1 fe 48 7f 94 c0 18 00 00 00  vmovdqu64 %zmm2,0x18(%rax,%r8,8)
   ba421: 62 b1 fe 48 7f 0c c7              vmovdqu64 %zmm1,(%rdi,%r8,8)
```
- **`zmm_keccak_round_x8`** (`vpternlogq %zmm` + `vprolq %zmm` + `vmovdqu64 %zmm`):
```asm
   b8952: 62 63 f5 48 25 e7 96              vpternlogq $0x96,%zmm7,%zmm1,%zmm28
   b8965: 62 e3 b5 48 25 d4 96              vpternlogq $0x96,%zmm4,%zmm9,%zmm18
   b89ea: 62 91 85 40 72 cd 01              vprolq $0x1,%zmm29,%zmm31
   b8a06: 62 b1 ed 40 72 ca 01              vprolq $0x1,%zmm18,%zmm18
```
- **`zmm_gfni_rmfe_x8`** (`vgf2p8affineqb %zmm` + `vpternlogq %zmm` + `vmovdqu64 %zmm`):
```asm
   b8260: 62 f1 fe 48 6f 9c df 18 00 00 00  vmovdqu64 0x18(%rdi,%rbx,8),%zmm3
   b826b: 62 f1 fe 48 6f a4 de 18 00 00 00  vmovdqu64 0x18(%rsi,%rbx,8),%zmm4
   b8276: 62 f3 e5 48 ce d8 63              vgf2p8affineqb $0x63,%zmm0,%zmm3,%zmm3
   b827d: 62 f3 dd 48 ce e1 1b              vgf2p8affineqb $0x1b,%zmm1,%zmm4,%zmm4
   b828a: 62 f3 d5 48 ce ea 05              vgf2p8affineqb $0x5,%zmm2,%zmm5,%zmm5
   b8291: 62 f3 dd 48 25 eb 96              vpternlogq $0x96,%zmm3,%zmm4,%zmm5
   b8298: 62 f1 fe 48 7f ac d8 18 00 00 00  vmovdqu64 %zmm5,0x18(%rax,%rbx,8)
```

---

### 4. Zen 5 Benchmark Table (`n = 1024` lanes = `128 × 8` ZMM vectors) & Stock-Lean Parity

| Kernel (`@[noinline, export]`) | Stock `lean -c` + `leanc -O3` | `lean-native` Zen 5 AVX-512 (`%zmm`) | Speedup | Parity (`n ∈ {0,1,7,8,9,15,16,23,64,67}` + COW) |
|---|---:|---:|---:|---|
| `zmm_f192x8_karatsuba` | `18914.33 ns/x8` (`2364.29 ns/elem`) | **`11.28 ns/x8`** (`1.41 ns/elem`) | **1,676×** | Exact match (`15080502310008991599`) |
| `zmm_ntt_butterfly` | `2620.69 ns/x8` (`327.59 ns/bfly`) | **`2.51 ns/x8`** (`0.31 ns/bfly`) | **1,042×** | Exact match (`PARITY_MATCH_OK`) |
| `zmm_keccak_round_x8` | `26224.91 ns/x8` (`3278.11 ns/state`) | **`191.03 ns/x8`** (`23.88 ns/state`) | **137×** | Exact match (`PARITY_MATCH_OK`) |
| `zmm_gfni_rmfe_x8` | `10525.98 ns/x8` (`1315.75 ns/word`) | **`0.50 ns/x8`** (`0.063 ns/word`) | **20,874×** | Exact match (`17667918380244853932`) |

<!-- GOAL_COMPLETE -->