# C1a reconstruction checkpoint

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
