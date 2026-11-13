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

Performance contracts remain unresolved: committed <1.15s/<8.633GiB,
later <3s/4GiB and <920ms/5.5GiB. No threshold is relaxed or claimed passed.
No snapshots. Lost machines are not recovery targets.
