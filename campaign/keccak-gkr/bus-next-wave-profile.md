# Read-only XMSS1400 bus profile

No bus implementation source was edited. Model/Bus/Flat.lean SHA256 remains `724458dc9bd2a9ed9a489081a3af77718eb7d1bb0e8affde81dcd9545a9daab3`.

One full proving recomputation in an external generated-C diagnostic copy completed. Its 359217-byte wire is byte-identical to the original baseline and independently accepted by frozen leanVM@59c2984 with positional `verify-eth inputs proof 1400 1`. Diagnostic source/object copies live outside the application. No duplicate-definition linker flag or app extern was introduced. Native candidate2 acceptance measurements are separate.

Timers below are nested aggregate thread CPU, selectively instrumented, and are not wall time, percentages, an acceptance benchmark, or evidence of speedup. The diagnostic C object may have different inlining from the ordinary native object; Lean mutant correctness checks overlapped part of diagnostics. Constructor counts include requested object storage/header, exclude allocator rounding, and do not count every runtime allocation.

| Function | Calls | Diagnostic thread CPU s |
|---|---:|---:|
| proveBalanceFlat | 1 | 11.235240 |
| proveProductTripleFlat | 1 | 6.722283 |
| decomposeSideFoldFlat | 3 | 3.033714 |
| buildSideLeavesFlat | 3 | 1.936029 |
| buildColumnsFlatWq | 1 | 1.726178 |
| foldTreeFlat | 432 | 1.264777 |
| proveConstraintsFlat | 1 | 1.255592 |
| treeRoundMessageFlat | 432 | 1.138764 |
| constraintsRoundsFoldFlat | 1 | 0.432306 |
| constraintsUpdateTablesFlat | 18 | 0.329630 |
| constraintsRoundMsgsFlat | 18 | 0.099879 |

The strongest next-wave hypothesis is balance/product-tree allocation and scalar field work, before constraints-round machinery. Validate each intervention on the ordinary complete E2E path. Large measured constructor sites:

| Worker | Constructors | Requested bytes |
|---|---:|---:|
| foldTreeFlat loop | 93,847,492 | 3,003,119,744 |
| buildSideLeavesFlat loop | 67,651,448 | 2,164,846,336 |
| eqTableExpandArray loop 0 | 43,078,968 | 1,378,526,976 |
| eqTableExpandArray loop 1 | 43,078,968 | 1,378,526,976 |
| nextLevelFlat loop | 23,461,884 | 750,780,288 |
| foldTableFlat loop | 4,292,570 | 137,362,240 |
| tableMessageKFlat loop | 2,490,368 | 79,691,776 |

Read-only follow-up should inspect E temporary materialization and ownership in tree folds/leaves, table expansion/shrink allocation, and repeated field interpolation. Avoid assuming a standalone kernel microbenchmark governs these call sites. Keep transcript order, public layout, challenge sampling, constraints, and security fixed; this report authorizes no bus edits.

For comparison, this diagnostic measured 29,569,843,200 GKR product-loop constructors (946,234,982,400 requested bytes) and 226,492,416,000 bytes of potential shared-buffer copy payload in foldRowsFlat. These are actual full-size instrumentation counts, not extrapolated small cases. They motivate separate GKR ownership changes; they do not certify E2E gains.

Evidence root: `/var/lib/orb-node/work/keccak-gkr-evidence/`. Files: `candidate2-full-profile-status.json`, `candidate2-profile-xmss1400-verify.log`, `candidate2-profile-xmss1400-{gkr,bus}.csv`, corresponding `-summary.json`, `candidate2-profile-link.json`, and `candidate2-full-profile-resources.jsonl`. Site maps: `candidate2-profile-gkr.sites.json` and `candidate1-profile-bus.sites.json`.
