# W3-S4 · Hub Fork Integrator: K4 VmWitness + Audit Hygiene + Timer Parity

## Scope delivered

1. **SHA-verified W3-K4-PREP VmWitness kernel installed** at `Native/Kernels/VmWitness.lean`
   (uset64LE/uget64LE, copy8/zero8, copyU64Slice/zeroU64Fill/packColumnU64,
   copyU64Bulk/zeroU64Bulk, vmMemPackLanes, fillGpowU64) and wired into
   `Model/Witness/Flat.lean` + `Model/Cli/E2E.lean` so the e2e prover path never
   materialises the 107M-word boxed `Array K` message (`msg`) for xmss1400.
2. **Audit hygiene**: `Tests/Audit/WholeRepoAxiomAudit.lean` import set extended
   (`Model.Cli.E2E`, `Native.Kernels.VmWitness`); VmHWM retention fixed in
   `Model/Cli/Aggregate.lean` warmup pass; whole-repo audit re-run clean.
3. **Timer parity check**: back-to-back G0-vs-K4 A/B on the same machine plus a
   final clean-machine run, all phase-timed, with byte-identical proofs.

## Kernel loop refactor (this shard's addition)

The W3-K4-PREP kernel and the packing helpers used `match n with | k+1 =>`-style
direct recursion. Every directly recursive definition makes Lean emit a
`<name>._unsafe_rec` auxiliary constant; the whole-repo audit rejects any
`LeanVmXmss.*._unsafe_rec` generated name. All seven loops
(`copyChunks`, `copyWords`, `zeroChunks`, `zeroWords`, `gpowLoop`,
`zeroBulkChunks`, `packLoop`) were rewritten as non-recursive `Fin.foldl` folds
(the repo's existing `foldRange` convention; `Nat.rec` was rejected because the
non-tail evaluation chain stack-overflows past a few million iterations).
Microbenchmark (50M words, warm): `Fin.foldl` 7.4 ns/word vs the old
recursion 7.7 ns/word — no measurable cost.

## Layout-overlay discovery (correctness fix)

`buildColumnsFlatWq` originally rebuilt bus columns from the retained `wins`
arrays (pointer-copy). The xmss4 fixture diff showed 26 columns where the wins
view is not the stacked view: the qKeccak placement (`col 5`) spans
`qw.size = qKeccakSlots*kh` words but its placement height is
`(qKeccakSlots + spares)*kh`, so the tail of its region contains the spare
columns' data; the 25 keccak-table input-lane columns are overlaid on the
qKeccak slots region (real data in wq, empty in wins). G0's bus semantics are
exactly "extract the stacked region from the message", so `buildColumnsFlatWq`
now uses the wins fast path only when `wins[col].size >= placement height`
(no overlay possible) and falls back to `extractWordsWq` otherwise. For xmss1400
the fallback covers 26 columns / 23.3M words (~1 s); 92.9M words use the
zero-copy path. Bus stream, stage stream, wq and root fixtures are byte-identical
to G0 on xmss4/16/1400.

## Build-system note

`Tests/Hub/cache_manager.py` keys its native object cache by source SHA-256
only (no dependency tracking). After editing a dependency, dependents' cached
`.c`/`.c.o.export` artifacts must be deleted so they are regenerated; leaving
them stale produces undefined-reference link errors (e.g.
`buildColumnsFlatWq___redArg`). All downstream artifacts were regenerated for
this delivery.

## Verification (all with the final binary)

- Kernel unit test: `SUMMARY|checks=5064130|failures=0`
  (`wave3/s4/kernel-test.txt`).
- Lean mutants: 5/5 rejected, 0 accepted (`wave3/s4/audit/mutants-lean.json`).
- Rust mutants: 29/29 killed (pre-existing, unchanged; `audit/g3-rust-mutants.json`).
- Whole-repo axiom audit: 8267 declarations, 40 modules, 0 rejections,
  axioms used = {propext, Quot.sound} (`audit/axiom-audit-repo.json`).
- xmss4 / xmss16 / xmss1400: every exported fixture (K1, K2, K3, K4) byte-matches
  the G0 fixtures; `e2e-oracle verify-eth` PASS on all three proofs;
  `e2e-oracle check-eth` PASS on the oracle dirs (G0-canonical proofs).
- xmss1400 proof is byte-identical to the G0 binary's proof
  (`ab-test/g0-proof.bin` vs `ab-test/k4-proof.bin`, cmp clean).

## Benchmarks (xmss1400, 16 vCPU AMD Ryzen 9 9950X, 32 GiB)

Back-to-back A/B on the same machine (`ab-g0-*.txt/json`, `ab-k4-*.txt/json`):

| phase                |     G0 |     K4 | delta   |
|----------------------|--------|--------|---------|
| 1_execute_witness    |  44.4s |  23.5s | -47.2%  |
| 2_commit_ntt_merkle  |  16.1s |  11.3s | -29.7%  |
| 3_bus_constraints    |  66.8s |  50.9s | -23.8%  |
| 4_keccak_gkr         | 269.9s | 226.8s | -16.0%  |
| 5_pcs_open           | 297.4s | 302.9s |  +1.8%  |
| pass total           | 694.9s | 615.6s | -11.4%  |
| warmup total         | 665.5s | 563.9s | -15.3%  |
| pass VmHWM           | 13.59 GiB | 13.91 GiB | +0.32 GiB |

Final clean-machine run (`lean-xmss1400-bench.txt`, `xmss1400-phases.json`):
warmup 488.6s (HWM 12.37 GiB), pass 482.7s (HWM 14.09 GiB);
phase 1 16.1s, phase 2 10.1s, phase 3 35.2s, phase 4 206.7s, phase 5 214.5s.
Same-session G0 reference (g0check, cooler machine): pass 560.8s with phase 1
24.6s / phase 3 44.0s. Phase-to-phase machine drift on this box is 20-30 %
(thermal); the A/B numbers above are the controlled comparison.

The peak-RSS target of <5.5 GiB is infeasible within this shard: the peak sits
inside phase 3 (bus balance/constraint proving over the full column set), which
would require restructuring `Model.Bus` internals. Peak and warmup HWM remain
within ~0.6 GiB of G0 while eliminating the 2.6 GiB boxed message and retaining
2.6 GiB of `wins` arrays for the phase-3 column rebuild.

## Files modified

- `Native/Kernels/VmWitness.lean` (kernel loops -> Fin.foldl)
- `Model/Witness/Flat.lean` (K4 helpers: limbWordOf/memLimbBytes/colIndexOf/
  packColAt/stackWqK4/extractWordsWq/qKeccakWindowWq)
- `Model/Bus/Flat.lean` (buildColumnsFlatWq with wins/wq overlay-aware columns)
- `Model/Cli/E2E.lean` (assembleWqK4 returning sized/wq/wins,
  proveBusAndConstraintsWqWithBcCols, proveKeccakGkrOnlyWq, exportShardFixtures,
  proveLeafEthereumFast / proveLeafEthereumTimedPass on the K4 path)
- `Model/Cli/Aggregate.lean` (warmup ethProof retention fix)
- `Tests/Audit/WholeRepoAxiomAudit.lean` (import set)
