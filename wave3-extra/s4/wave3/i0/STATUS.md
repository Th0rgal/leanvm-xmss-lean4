# Gate G0 Status — I0 (`Master Hub Integrator & xmss1400 Profiler`)

- **Machine**: `xlarge-m` (`managed-mmgnhpsxy5`, 16 vCPU AMD EPYC Zen 5, 32 GiB RAM)
- **Baseline Repo Commit**: `de39fd791908a6b2c4b6752872e9a11b40ec31f4` (`$HUB/LeanVmXmss`)
- **Frozen Rust Reference**: `59c2984df79cc9ff1914e547c5d390fffc8f3e` (`$HUB/references/leanVM`)
- **Wave 2 Harvest Verification**: `17/17` files matched exact bytes, lines, and SHA-256 (`w2-sha256-verified.json`)
- **Whole-Repo Axiom Audit**: `8229` declarations audited across `40` modules, `0` rejections (`axioms <= {propext, Quot.sound}`)
- **End-to-End Rust Oracle Verification (`e2e-oracle`)**:
  - `syn_tiny`, `syn_jump`, `syn_deref`, `syn_keccak`: **4/4 PASS** (`keccak_scalars_len=1238`)
  - `xmss4`: **PASS** (`241,473` B wire, `21,465` cycles)
  - `xmss16`: **PASS** (`279,625` B wire, `31,140` cycles)
  - `xmss1400`: **PASS** (`359,217` B wire, `1,146,537` cycles, `8,668,972` mem cells, statement `ded8679e548f3d7c810a3c50e1c69b4fed50773b35189e3a67d7728accafe423`)

## G0 Timing & Memory Summary (`--log-inv-rate 1`)

| Case | Rust `leanvm` (`znver5`) | Lean `e2e-aggregate` (G0) | Lean `VmHWM` |
|---|---:|---:|---:|
| `xmss4` | `0.221 s` mean (`0.163 s` min) | `7.543 s` | `793 MiB` |
| `xmss16` | `0.258 s` mean (`0.214 s` min) | `11.800 s` | `941 MiB` |
| `xmss1400` | `2.943 s` mean (`2.235 s` min, `5.805 GiB` RSS) | `441.154 s` measured (`545.136 s` warmup) | `13.89 GiB` (`14,913,695,744` B) |

## `xmss1400` Phase Breakdown (Measured Pass)

| Phase | Rust `leanvm --tracing` | Lean `e2e-aggregate` (G0) | Share of Lean Total |
|---|---:|---:|---:|
| `0b_statement_hints` | `0.022 s` | `0.154 s` | `0.03%` |
| `1_execute_witness` | `2.046 s` (`1.70 s` + `0.346 s`) | `25.086 s` | `5.69%` |
| `2_commit_ntt_merkle` | `0.269 s` | `9.055 s` | `2.05%` |
| `3_bus_constraints` | `0.667 s` (`0.584 s` + `0.083 s`) | `33.443 s` | `7.58%` |
| `4_keccak_gkr` | `0.698 s` | `184.661 s` | `41.86%` |
| `5_pcs_open` | `0.420 s` | `188.755 s` | `42.79%` |
| `6_wire_encode` (post-timer) | outside | `0.010 s` | - |
| **Total (`t5 - t0`)** | **`4.100 s`** (`2.943 s` untrace mean) | **`441.154 s`** | **`100.00%`** |

## Fork Readiness

- Frozen `Model/Prim/Slice64.lean` + `Native/Kernels/{FieldSimd,BusSimd,KeccakGkrSimd,NttMerkle,MemSlice}.lean` compiled into `.lake/build` + `.lean-native/obj`.
- Deterministic shard fixtures exported under `$HUB/fixtures/{xmss4,xmss16,xmss1400}/K{1,2,3,4}` (`manifest.json` verified).
