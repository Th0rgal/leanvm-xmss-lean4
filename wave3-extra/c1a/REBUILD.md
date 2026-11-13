# C1a reconstruction checkpoint

**Current placement correction:** this session runs on fresh Boat xlarge
`managed-859023b6-1b58-4d60-aa6d-c0a47c637108`. Local builds here are explicitly
authorized; the Babylon restriction applies to the coordinator. Coordinator
owns TTL/extensions. Earlier missing-worker statements below are historical
and no longer block builds. No snapshots or secrets are used.

Priority: bootstrap the frozen public compiler against Lean 4.35 first,
because the preinstalled executable embeds Lean 4.31 and cannot import this
package's Init.olean. Clean frozen worktree `/var/lib/orb-node/work/c1a-bootstrap`
is building through turbo-lean (one job/thread, max-memory 6144 MiB).
The reproducible bootstrap script is committed in compiler `f74efc3`;
receipts are under `/var/lib/orb-node/work/c1a-evidence/bootstrap`.
No compatible executable or native test PASS has been claimed yet.

Application base: `299c689373ef3e98e0f150ff4bec21ca5e3aaea1`.
Compiler source: public `https://github.com/Th0rgal/turbo-lean.git`, frozen
revision `29d85f7da2d963750f77d76d5323408a73386f14` from
`meta/hub-manifest.json` and `meta/p1-frozen-spec-manifest.json`.
Lean: `leanprover/lean4:v4.35.0`.

Durable worktrees:
- `/var/lib/orb-node/work/c1a-rebuild`, branch `campaign/c1a-rebuild`.
- `/var/lib/orb-node/work/c1a-turbo-lean`, same branch name.

Read the plan, README, C1a status/final report and operation journal.
The report describes prior results; none is a validation of this rebuild.
Reconstruct from committed P0 patch and C1a journal, then reconcile the
recovered Worker A archive when delivered. Application/oracle sources must
remain unchanged. No duplicate-definition linker allowance is permitted.

No Boat API or connection is exposed to this session yet. No builds have
run on the local host. Request sent for a fresh worker and TTL route.
Builds must use turbo-lean, jobs 1, max-memory 6144, LEAN_NUM_THREADS=1.
Required validation: P0 build-exe and trust-boundary scripts, actual app
module builds/execution, final linked symbol/disassembly evidence, and
available prescribed lint/typechecking. Application purity and axiom gates
remain required. All gates are pending.

Authoritative superseding contract (Thomas, verbatim): "under 1s and 4gb is the goal".
Acceptance requires matched measured XMSS1400 aggregation passes with wall time
strictly <1 second and peak RSS strictly <4 GiB = 4,294,967,296 bytes.
This supersedes all earlier thresholds, including <1.15s/<8.633GiB,
<3s/4GiB, and <920ms/5.5GiB. No relaxation is authorized.
Coordinator-reported current result: 370.6123 seconds / 15,038,140,416 bytes,
approximately 370.6123x the time boundary and 3.5013x the memory boundary.
That result fails both thresholds and is not matched certification for this
compiler checkpoint. No acceptance gate is claimed passed.
No snapshots. Lost machines are not recovery targets.

## Compiler checkpoint 9d6c297

Compiler commits, in order: `8d644b8`, `4ea9b0a`, `105041a`, `9d6c297`.
The final commit checkpoints uncompiled reconstruction of canonical intrinsic
body/dependency recognition, borrowed ByteArray ownership adapters, bounded
unsigned tail-loop conversion, helper inlining, ZMM loop emission, and the
recovered C1a canary/differential test cases. This is a recovery checkpoint,
not a validated implementation or an acceptance result.

Lightweight checks: `git diff --check`, Python AST parsing for both required
test scripts, and `python3 scripts/sync_docs_inventory.py --check` passed.
Compiler bundle verification passed against the frozen source prerequisite.
Lean typechecking, LLVM verification, both required native test scripts,
real application compilation/execution, final linked disassembly, purity/
axiom audits, end-to-end ablation, and performance gates remain pending.
The CI script includes Lake builds; these have not been run on the local
host and must be adapted to the authorized turbo-lean worker workflow.

An unauthenticated push was attempted and failed because GitHub requires
authentication. No credentials were requested or transferred. Coordinator
harvest files under `/var/lib/orb-node/work`:

- `c1a-compiler-checkpoint.bundle` (incremental from frozen compiler revision)
- `c1a-compiler-checkpoint.patch` (cumulative compiler diff)
- `c1a-rebuild-checkpoint.bundle` (application report branch)
- `c1a-rebuild-checkpoint.patch` (application report diff)
- `c1a-harvest-manifest.json` (refs, prerequisite and SHA-256 hashes)

No Boat provisioning, SSH, or TTL tools/connection are exposed. A new worker
and TTL-management route remain required; no worker exists here to extend
or clean up. The promised Worker A archive has not been delivered.

## Follow-up checkpoint

Compiler commit `68df8e2`
adds prepared P0 coverage for borrowed ByteArray reads, owned writes with a
retained original, unaligned/short/out-of-range/max offsets, and slice kernels
whose destination aliases a retained source. Python syntax and whitespace
checks pass; the Lean fixture and native cases remain uncompiled/unrun.
Boat tool discovery still returns no callable managed-compute tool. The newly
available managed-compute/lean-builds skills were read; their referenced REST
fallback resource is absent from this session. No provider keys were sought.

## Verified Lean 4.35 bootstrap delivery

Clean pinned compiler `29d85f7da2d963750f77d76d5323408a73386f14` and dependency
`077775ba387f1eeb2976cb8763b4633b8d5ce313` built successfully via turbo-lean
(352 jobs, one thread/job, max-memory 6144). The installed turbo-lean delegates
this executable target to Lake; its process environment was recorded.
Both the static original and smaller shared-runtime relink imported Lean 4.35
Init.olean, ingested an exported UInt64 addition source, and evaluated 7+5=12.
The packaged launcher independently repeated ingestion/evaluation successfully.

Harvest `/var/lib/orb-node/work/c1a-bootstrap-lean435.tar.gz` (7.1 MiB), SHA-256
`88bd563d4e1e11cfb6080842c3fc7d720bd44731a5d6e80ed68b9e7266dc7c1e`.
It includes executable, matching-runtime launcher, reproducible bootstrap script,
source patch, README, manifest, and command/build receipts. Requires an installed
Lean 4.35 runtime. Source bootstrap script is compiler commit `3e3b2dc`.
The original 248 MiB static executable is separately preserved at
`/var/lib/orb-node/work/c1a-lean-native-435-static`.

This establishes compiler/toolchain compatibility only, not C1a correctness or
XMSS1400 acceptance. Bootstrap worktree is now detached at `3e3b2dc` and rebuilding
lean-native + lean-native-core incrementally for reconstruction validation.

## Reconstructed compiler checkpoint ba5b99b

The rebuilt compiler and core executable pass the full Lean 4.35 build through
turbo-lean. Required suites were run from the detached compiler build worktree:

- `scripts/test_build_exe_p0.py`: PASS, 2 tests, 10.994 seconds.
- `scripts/test_p0_trust_boundary.py`: PASS, 20 tests, 38.530 seconds, plus
  12 embedded runner tests, all passing.

P0 covers 262 scalar field pairs, 131 extension-field pairs, UInt64 boxing,
33 borrowed ByteArray boundary/alias cases, 9 slice sizes with separate and
aliased destinations, fault injection, and imported-module native-c fallback.
The imported cache object is unchanged; the private link copy has a weak
replacement symbol and the final executable has one strong optimized owner.
Final `p0_zmm_slice_kernel` objdump contains ZMM VPCLMULQDQ, GFNI, VPTERNLOGQ,
and VMOVDQU64. Raw commands, symbols, disassembly and result JSON are under
`/var/lib/orb-node/work/c1a-evidence/p0-r4`; trust log is under `.../trust`.

Runtime diagnostics found and fixed internal ByteArray return rejection,
redundant impure Bool case guards around qualified loops, retention of source
self edges after loop conversion, and residual-heap filtering of typed
ByteArray RC. Untyped heap/object operations and unresolved cycles remain
rejected. Previous failing logs remain under the evidence directories.

Real Field/Bus/Hub/Keccak module builds are now running. These suite results
are not an application purity/axiom audit, real-app acceptance certificate,
or matched XMSS1400 performance result.

## Real application executable checkpoint

All seven requested Field/Bus/Hub/Keccak modules compiled (48 jobs, 36.211s).
All 40 imported-module native objects were generated (81 jobs, 12.334s).
The reconstructed compiler then built real `Tests.Field.NativeMulProbe`,
`Tests.Field.Native`, `Tests.Keccak.ImportedRunner`, and
`Tests.Keccak.LaneRunner` executables without application source changes.

Independent deterministic polynomial validation passed 48 field/extension
cases (products, inverses, squares) and 48 imported multiplication probes.
`shard_a_test_mul` final objdump contains VPCLMULQDQ and no calls.
The imported Keccak runner passed five comparisons with the pure permutation;
the lane/transcript runner output matched Lean interpreter output byte for byte.
The existing static purity checker passed 129 Spec/Model/Native/Proofs files,
with no forbidden declarations or non-Lean FFI files. Transitive axiom audit
is still running; these results do not certify its outcome.

Evidence and external validation script are preserved under
`/var/lib/orb-node/work/c1a-evidence/app`. All work remains compiler-only:
this journal is the sole application-repository change from the recovery base.
Reconstructed dynamic compiler packaging is underway, separate from the clean
bootstrap archive. Neither compiler correctness checks nor application tests
constitute matched XMSS1400 performance acceptance. Strict goal remains
wall time <1 second and peak RSS <4294967296 bytes; no passing measurement.

## Purity and axiom audit results

Existing Field AxiomAudit passed: 626 declarations, 420 theorems. Existing
StructuralAudit passed (61 declarations). Keccak AxiomDetails compiled; listed
Keccak/transcript proof dependencies are subsets of `{propext, Quot.sound}`.
Combined turbo audit build completed 38 jobs in 181.875 seconds.

A separate module-origin audit of production Field/Bus/Keccak/Transcript and
all their application dependencies passed: 2961 declarations, 754 theorems,
33 modules; zero unsafe/external declarations and only allowed transitive
axioms. Audit source and output are preserved outside the application tree.

The stricter fixture-inclusive audit failed on pre-existing generated
`clmul64.go._unsafe_rec` from `Tests.Field.Intrinsic` (a total well-founded
recursive fixture). Therefore no claim of zero unsafe auxiliaries across all
Tests is made. The original fixture and application remain untouched. Static
purity and production-module audit passes must not conceal this scope gap.

## Reconstructed Lean 4.35 delivery

Harvest `/var/lib/orb-node/work/c1a-reconstructed-lean435.tar.gz`, SHA-256
`4ac1830ca553463b1e93bc767fd7b90c03a2eec9759f36941ea3ba2a7d9c3a06`.
This is distinct from the earlier clean-bootstrap package. Contains dynamic
lean-native and lean-native-core, matching-runtime launchers, compiler source
bundle/patch, reproduction instructions, exact source/runtime/binary manifests,
command receipts, required-suite logs and selected final disassembly/audits.
Compiler source is ba5b99b221e25c2d95d81ca09879015bf2ff3ed1.

Both dynamic binaries passed source ingestion and evaluated 7+5=12. Both
required suites were rerun against the actual delivery binaries: P0 PASS
(2 tests,13.278s), trust boundary PASS (20 tests,39.954s), plus 12 embedded
runner tests PASS. No C1a/XMSS1400 performance certificate is asserted.
The source bundle and application journal bundle are refreshed for coordinator
harvest; unauthenticated push remains unavailable. No credentials were used.

## Production caller acceleration correction

Additional external harnesses (outside application sources) exposed a gap in
ba5b99b: canonical exported CLMUL roots accelerated, but persisted LCNF for
production nativeMul/Bus callers already contained the expanded bitwise body.
The earlier archive remains a valid checkpoint with this limitation.

Compiler 48d1ee2 adds a restricted UInt64 source frontend preserving typed
helper calls, and discovers source dependencies alongside LCNF dependencies.
Complete canonical graph validation still admits crypto intrinsics; unsupported
source forms fall back to the LCNF bridge. This extension has Tested assurance,
not the RealLCNFBridge refinement theorem. RealLCNFBridge proofs are unchanged.

Updated real production nativeMul final objdump has one VPCLMULQDQ; Bus
planarEmul0 has four VPCLMULQDQ and no calls. Independent oracle validation
passed 48 production Bus/Field cases and 48 ShardAHw cases. Earlier disassembly
showing expanded arithmetic is retained beside the corrected `*-r2.asm` files.
P0 regression now calls the actual [inline] masked canonical helper family:
262 additional arithmetic pairs and final call-free VPCLMULQDQ checks pass.
Expanded P0 suite PASS (2 tests,20.102s). Trust suite and all real executables
are being revalidated before an updated delivery archive is certified.

Post-fix validation completed: trust boundary PASS (20 tests,36.357s), plus
12 embedded runner tests PASS. All five refreshed real application executables
(Field NativeMulProbe/Native, Keccak ImportedRunner/LaneRunner, ShardAHw external
harness) built successfully with the corrected compiler. Field and imported
multiply oracle cases passed; both Keccak runner outputs match earlier verified
outputs; 48 production Bus/Field and 48 refreshed ShardAHw oracle cases passed.
P0 final masked caller and extension kernels are call-free VPCLMULQDQ; its
slice kernel retains all four required ZMM instruction families. Updated dynamic
compiler delivery is being linked; old archive still identifies ba5b99b only.

## Final corrected compiler harvest checkpoint

Updated delivery: `/var/lib/orb-node/work/c1a-reconstructed-lean435-r2.tar.gz`,
15,423,346 bytes, SHA-256
`cb48ac065b29338d5e451d5688721be2fb81727b8a2db8a6b59aaf44cf8978e7`.
Compiler source: 48d1ee2e4432d9991945b8d14782e2b993848969.
Both actual dynamic binaries passed source ingestion; both copied runtime
launchers independently evaluated bootstrap_add(7,5)=12. Final delivery P0
PASS (2 tests,19.168s); trust boundary PASS (20 tests,86.832s), plus all
12 embedded runner tests PASS. This supersedes the earlier ba5b99b compiler
archive for production-caller acceleration. Earlier artifacts remain preserved.

Both source bundles/patches and `/var/lib/orb-node/work/c1a-harvest-manifest.json`
are refreshed for coordinator harvest. No credentials, snapshots, application
or oracle workaround edits, or duplicate-definition linker flags were used.
Worker A archive has not arrived; reconstruction did not depend on recovering
or waiting for lost machines. All build processes have completed.

Outstanding: fixture-inclusive audit still rejects the pre-existing generated
Tests.Field.Intrinsic clmul64.go._unsafe_rec; production-module audit passes.
No matched XMSS1400 <1s/<4294967296B measurement exists for this rebuild.
The coordinator's 370.6123s/15038140416B result remains a failed measurement,
not certification of this compiler. No acceptance target was relaxed.
Coordinator should harvest the durable archives/bundles/evidence before VM
cleanup; TTL and release remain coordinator-owned.

## PCS public bootstrap cross-check and candidate compatibility

Fetched public `campaign/pcs-opening` at
0a7aa39b4403fbb7edfe8de97039a78c5df219ce into a separate detached worktree
`/var/lib/orb-node/work/c1a-pcs-compat`. Its published BOOTSTRAP.md confirms the
pinned compiler/toolchain/dependency recipe. Extracted meta/compiler-fix.patch
SHA-256 exactly matches 05d8024587ec0046b363a8821a899a5bd7c75a5eea56a68515dd558e1b8d526d.
Applied that patch to a source-only pinned reference worktree: both LLVM.lean
and BuildExe.lean hashes exactly match the published expected values.
No duplicate bootstrap build or system compiler replacement was needed.

Fresh PCS E2E, batch-test and campaign-audit module compilation has completed;
the committed cache_manager.py is now regenerating native objects sequentially
with the reconstructed task-local 48d1ee2 compiler on PATH. No PCS worker
native objects are reused. Native batch execution, audit and real E2E linking
are pending. Commands, source/tool hashes and receipts are preserved under
`/var/lib/orb-node/work/c1a-evidence/pcs-compat`. This compatibility check does
not certify the reported full1400 fixture recovery on a different worker and
does not claim an XMSS1400 performance pass.

## PCS native compatibility and cached ABI ownership fix

Compiler bd58dbedd76a49be3942f3b029d5ac85718589a6 fixes duplicate cached
boxed ABI adapters by weakening only private copies of actually replaced
kernels and their emitted adapters. No linker duplicate-definition bypass.
Expanded imported-native-c P0 regression passed (2 tests,23.425s).
PCS compatibility at public app 0a7aa39b4403fbb7edfe8de97039a78c5df219ce
passes native batch execution, strict audit (598 declarations,0 rejections),
and real E2E linking. Final field symbols have unique strong owners and CLMUL;
shard_a_mul is call-free. All130 original cached object hashes are unchanged.
Evidence: c1a-evidence/pcs-compat/receipt.json, commands.json and disassembly.
Main/core Lean builds pass; final dynamic packaging and rerun are in progress.
This is compatibility evidence, not a full XMSS1400 performance certificate.
