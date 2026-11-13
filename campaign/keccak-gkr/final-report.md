# Keccak GKR campaign final report

Base `299c689373ef3e98e0f150ff4bec21ca5e3aaea1`; branch `campaign/keccak-gkr`; selected implementation `200b18acaebd31571aa4c9b07838ae079f451a2a` (candidate7).

Final XMSS1400 mean E2E **343.263818s**, GKR **97.763919s**, peak RSS **16034304000B** (14.933109GiB). Frozen Rust mean 2.989255s, peak 3964735488B; Lean/Rust mean-time ratio 114.833. The authoritative strict <1 second / <4 GiB (4294967296 bytes) gate remains unmet. All earlier targets are superseded.

## Matched final measurements

Every pair uses sequential Rust then Lean on this host, each a fresh process with one warmup and three timed full recomputations. `/usr/bin/time -v` measures fresh-process peak RSS. Every emitted Lean proof is byte-compared with the pre-edit baseline and independently verified by clean leanVM@59c2984 using positional `verify-eth <xmss-inputs.bin> <proof> N 1`. No proving output is reused as input. No campaign build or diagnostic overlaps acceptance timing.

| XMSS | Pairs | Lean mean s | GKR mean s | Rust mean s | Lean peak B |
|---|---:|---:|---:|---:|---:|
| 4 | 5 | 5.699338 | 0.832612 | 0.236072 | 1408069632 |
| 16 | 5 | 7.585236 | 1.698248 | 0.142186 | 1528025088 |
| 1400 | 5 | 343.263818 | 97.763919 | 2.989255 | 16034304000 |

| XMSS1400 control | Lean total s | GKR s | Rust s | Lean peak B |
|---|---:|---:|---:|---:|
| Original pre-edit baseline | 495.299500 | 213.445628 | 3.484691 | 15736782848 |
| Fresh saved-baseline control | 441.760340 | 200.575009 | 3.349624 | 15870304256 |
| Final five-pair selected binary | 343.263818 | 97.763919 | 2.989255 | 16034304000 |

| Candidate XMSS1400 matched gate | Lean total s | GKR s | Rust s | Peak B |
|---|---:|---:|---:|---:|
| candidate1 | 364.016344 | 164.780370 | 4.103613 | 16061480960 |
| candidate2 | 362.538437 | 149.734392 | 3.963599 | 15837421568 |
| candidate3 | 357.882954 | 146.516820 | 3.574380 | 16046379008 |
| candidate4 | 322.139223 | 131.888088 | 3.466708 | 15936102400 |
| candidate5 | 487.209818 | 173.545397 | 3.880687 | 15725670400 |
| candidate6 | 762.182160 | 539.734519 | 4.237936 | 15776288768 |
| candidate7 | 361.108949 | 102.436217 | 3.459092 | 16177577984 |

Host/phase drift is substantial; raw differences between candidates are not causal speedup estimates. The fresh baseline control and final per-pair raw samples are retained in `final-results.json`. Confidence intervals in the summary assume independent pair means and do not establish host stability.

Final observed non-GKR phase subtotal:245.511332s. This is a measured phase budget, not a mathematical lower bound after arbitrary pipeline changes; further E2E work requires the other owners.

## Authoritative gate and historical gaps

| Target time / RSS | Time ratio | Excess seconds | Excess RSS B |
|---|---:|---:|---:|
| <1.0s / <4.0GiB | 343.264 | 342.263818 | 11739336704.000 |

Historical total370.612s: final delta -27.348182s. Historical RSS15038140416B: final delta +996163584B. Historical GKR153.06s: final delta -55.296081s. Those historical runs are not matched controls. Wire remains359217B.

## Actual path and optimization

`Model.Cli.E2E.proveKeccakGkrOnlyWq` calls `Model.KeccakGkr.Flat.proveReductionFlat`. Standalone `Native.Kernels.KeccakGkr` kernels are absent from that import/call path. Whole-binary SIMD instruction counts therefore do not certify vector GKR integration. The measured hot path is scalar sumcheck/product and row-fold work.

A noinline UInt64-limb helper keeps the owned E accumulator live across planar reads, allowing reuse instead of one allocation per bit position. RoundETape is consumed before creating its destination-fold closure. Packed reads use proved USize byte indices and a cheap representable size guard with the exact original fallback. All-buffer/all-offset/shift and all-tape refinements preserve prior total semantics, including malformed/truncated buffers and aliases.

Candidate2 failed its intended reuse hypothesis. Candidate5 showed severe within-run drift (350.160/557.905/553.564s totals) and no reliable E2E gain. Candidate6 exposed per-read `lean_cstr_to_nat("4294967296")`; runtime assembly constructs/parses mpz before returning a tagged Nat. The selected guard uses2^32−1, which emits an immediate comparison. No compiler source was edited.

## Full-size allocation diagnostic

Actual XMSS1400 instrumented product-loop constructors (candidate2→candidate7):29569843200→0; the prior inner constructors requested946234982400 cumulative bytes including headers but excluding allocator rounding. Initial bucket objects remaining:18481152. Instrumented UInt64 boxing calls:0. Row-fold potential shared-input COW payload:226492416000→136734310400B. Instrumented pair-sum loop objects:1887772404; row-fold loop objects:1258252908.

These are selective generated-C counters, not total runtime allocations, peak RSS or DRAM traffic. Timers are nested aggregate thread CPU, not native wall time. Parent timers exclude CPU used by spawned child threads. Instrumentation may change inlining. The full diagnostic proof is byte-identical and independently verified; diagnostic executables are excluded from acceptance.

## Correctness, purity and scope

All selected-version gates passed: native128-instance×24-round permutation vs Spec; RMFE vs Spec; F192 fold vs Model; native972 bucket cases;72 ownership cases;960 read boundary/wrapping cases; positive baselines and34 mutations in both Lean and frozen Rust; whole/transitive axiom audit; static purity; per-file nonvacuous/tight spec audits; unchanged native symbol/ISA audit; protocol-source hash checks; all-size matched gates; final>=5 pairs. Application extern/unsafe/sorry/crypto FFI remain zero; axioms stay within propext/Quot.sound. No protocol, security, log_inv_rate, transcript, wire, PCS, bus, compiler, proof-caching or duplicate-definition-linker changes.

The installed CLI rejects `audit-spec --policy strict-proofs`. That named global policy gate remains unsupported and is not claimed passed. Available per-file spec audits and the unchanged whole/transitive purity/axiom audits passed.

## Resources and handoff

Initial observed scope max8973910016B (8.358GiB), high8076517376B (7.522GiB) were insufficient; the operator also reported prior8.56/7.7GiB caps. Durable campaign scopes use 26GiB max/24GiB high. Ancestor CPU quotas showed no throttling; cgroup samples retain memory/CPU pressure and events. Final scope memory-event maxima:{'low': 0, 'high': 0, 'max': 0, 'oom': 0, 'oom_kill': 0, 'oom_group_kill': 0}. Builds used jobs1/max-memory6144/LEAN_NUM_THREADS1; babylon was never built. The compatible frozen compiler plus its recorded existing repair was rebuilt; compiler SHA79b805002e329a6eee167403265daa91b50467a4169c8e735d0e843eca3cc6ba.

Bus profiling is read-only: see `bus-next-wave-profile.md`. Balance/product-tree allocation is the leading next-wave hypothesis ahead of constraint rounds. Bus source hash724458dc9bd2a9ed9a489081a3af77718eb7d1bb0e8affde81dcd9545a9daab3 is unchanged. Constructor/boxing counters across the candidate2/5 full bus diagnostics match at52 sites.

Evidence root:`/var/lib/orb-node/work/keccak-gkr-evidence`. Raw run status/log/phase/proof files live in `baseline/`, `baseline-final-control/`, candidate directories and `final/`. Full diagnostic CSVs/site maps, normal disassemblies, audits, fixture hashes, compiler provenance and scope-resource samples are retained. `final-results.json` embeds all final samples, phase means, proof/binary hashes and target gaps.

No credentials/secrets or VM snapshots were used. Anonymous GitHub writes are unavailable; export git bundle+patch+SHA256 under durable evidence for coordinator harvest/push. No TTL/lifecycle/coordinator tool was exposed. Request cleanup only after refs and evidence have been harvested.

Independent Rust verification: cold first-pass mean729.000ms; subsequent-pass mean10.900ms. These include the verifier harness behavior and are separate from proving time.
