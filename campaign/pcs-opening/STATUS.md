# PCS opening campaign checkpoint — 2026-11-13

Status: UNCHANGED NATIVE MATCHED BASELINE COMPLETE; DIAGNOSTIC REPLAY PREPARING.
Compatible compiler and fixtures are restored; initial blockers below are archived.
No application Lean source has changed. Strict <1 second / <4294967296-byte gate.
The unchanged full1400 warmup+repeat3 finished before any optimization edits.

Starting revision: 299c689373ef3e98e0f150ff4bec21ca5e3aaea1.
Anonymous HTTPS clone: /var/lib/orb-node/work/pcs-opening.
Owned branch: campaign/pcs-opening. No credential access or snapshots.
Evidence directory: /var/lib/orb-node/work/pcs-opening-evidence.

## Archived initial feasibility (resolved below)

Host: box-node-bdcc355beb075447 (not babylon). The actual job cgroup initially
had memory.max=8973631488 and memory.high=8076267520 bytes, with all memory.events
counters zero. This cannot contain the historical 15038140416-byte peak. Its
writable controls were raised to 25769803776/23622320128 bytes (24/22 GiB), below
the parent user.slice limit 33114030080 bytes. No benchmark was run throttled.

Unchanged E2E module build passed using turbo-lean, LEAN_NUM_THREADS=1 and a
6144 MiB build budget. However the installed lean-native v0.5.0 embeds Lean
4.31.0 (binary strings show leanprover/lean4:v4.31.0), whereas lean-toolchain
and the installed Lean are 4.35.0 (eb6cafb7290e8bd5f2937522d8d804f58f02bafc).
Both compile-llvm on Tests/Hub/ShardAHw.lean and build-exe on Model/Cli/E2EMain.lean
fail on Init.olean with "incompatible header". Thus there is no valid native
baseline executable. lean-native-core accepts LNIR only and is not a replacement
for the failing Lean frontend. No compiler changes or alternate proving path used.

Rust reference cloned anonymously to references/leanVM and detached at
59c2984df79cc9ff1914e547c5d5d390fffc8f3e; its working tree is unchanged.
The committed e2e-oracle harness builds successfully in release mode (jobs=1).
Its historical absolute include paths were satisfied by a local symlink to this
same reference checkout; no Rust verifier source was edited. The harness CLI
consumes positional input/proof arguments; trailing 1400/1 arguments are ignored
by this wrapper, so parameter validation needs separate evidence on resumption.

Four full1400 input/guest files are deliberately omitted from the public clone;
expected sizes/hashes are in oracle/xmss1400/LARGE_FIXTURES_MANIFEST.json. They
have not been regenerated or verified. No fresh proof was generated or reused.

## Actual call graph and hypotheses

Read committed plan.md and wave3-extra/k3-prep/k3-final-report.md. Current
E2E uses Model.Cli.E2E.proveLeafEthereumTimedPass (and related runners)
-> Model.Pcs.FlatWhir.provePcsOpenFlat -> proveLevelPlanar.

L0 opening: openL0Cosets -> firstCosetFromBytes -> encodeCosetVec8 ->
streamCosetsOpen -> hashLeafVec8From/subtreeRootBuf. Extension commitments and
openings use commitExtPlanar/openExtCosets -> encodeCosetVec8 ->
hashLeafExtVec8/subtreeRootExtVec8. These use Model.Pcs.Ntt and Model.Pcs.Commit,
not Native.Kernels.Ntt or Native.Kernels.Keccak8x.

Inspected both native kernel files and NativePcsMerkleKernelTest. Their reported
microbench improvements cannot be credited as an E2E gain without integrating
and verifying the actual opening callers.

Static candidates requiring measurement, not established bottleneck attribution:
- encodeCosetVec8 holds boxed Array Vec8 values; vecPairLoop reads two values,
  clears two slots, builds butterfly results, then writes two slots. Allocation,
  reference counting, and scalar arithmetic should be separated in profiles.
- firstCosetFromBytes is inside the L0 encode-coset closure; each coset rebuilds
  the packed Vec8 input. Hoisting may trade repeated packing for sharing/COW;
  it must be measured rather than assumed beneficial.
- foldPlanar/msgPlanar use byte-backed limbs but materialize E values and tuple
  accumulators. Generated code is needed to determine actual boxing elimination.
- streamCosetsOpen reconstructs codewords and hashes subtree leaves. Any native
  replacement must preserve leading-zero padding, row extraction, query ordering,
  sibling order, roots, transcript and wire bytes, not merely match a root.

No KeccakGkr or compiler edits. No extern/unsafe/sorry or crypto FFI introduced;
no allow-multiple-definition. Protocol/security/log_inv_rate=1 unchanged.

## Evidence limits and restart contract

No matched baseline, candidate, E2E XMSS4/16/1400 warmup+repeat3, proof-size/RSS
comparison, independent fresh-proof verification, or alternating Rust/Lean pairs
has completed. Historical 370.612 s / warmup 374.455 s / wall 751.54 s /
15038140416 B / wire 359217 B and ~154.93 s PCS opening are supplied historical
observations, not measurements from this host.

Authoritative contract (Thomas, relayed verbatim): "under 1s and 4gb is the goal".
Acceptance is strictly XMSS1400 aggregation <1 second and peak RSS
<4294967296 bytes (4 GiB), in matched measured passes. This supersedes ALL
previous targets, including <920 ms/5.5 GiB, <3 s/4 GiB and <1.15 s/8.633 GiB.
There are no remaining alternative performance gates and no relaxation.

The supplied historical current1400 370.6123 s / 15038140416 B is 370.6123x
the time threshold and approximately 3.50134x the memory threshold. Absolute
gaps are 369.6123 s and 10743173120 B to the threshold boundaries; strict
acceptance requires going below both. This is historical gap arithmetic, not
matched certification. No performance improvement is claimed.

Coordinator prerequisite: provision a credential-free compatible Lean 4.35
lean-native frontend/compiler/runtime with the campaign's pinned P0 fixes and
recorded hashes. Then regenerate omitted fixtures and match every committed
hash, establish unchanged full baseline first, profile, and only then implement
and gate a candidate. Final certification still requires >=5 same-host alternating
fresh Rust/Lean pairs with warmup+repeat3 and independent Rust verification.

No TTL/lease or coordinator messaging API is exposed here. Checkpoint is durable;
no VM deletion has been requested. No credential-free push capability was
provisioned (origin is public HTTPS). Export bundle/patch/hashes for coordinator
harvest, then request destruction after harvest acknowledgement.

## Current static gates

Targeted transitive purity audit of FlatWhir, Model Ntt/Commit, and both native
kernels: 595 declarations, zero rejections; permitted axioms only propext and
Quot.sound, no unsafe or extern declarations. This is an elaboration/kernel gate,
not native execution or a performance result. A source token scan on these files
and Model/Merkle/Flat.lean found no extern/unsafe/sorry/native_decide tokens.

turbo-lean audit-spec reports ok=true, no warnings/vacuous/trivial specs for all
three inspected modules: Ntt has 4 theorem specs; Keccak8x and FlatWhir have zero.
Zero recognized theorem specs is explicitly not evidence of algorithm refinement.
The committed kernel differential test builds successfully, but was not executed natively.
The broader WHIR/RingSwitch/StackOpen/Wire strict audit also passes: 1072
declarations, zero rejections. The 66-target gate build completed in 208.711 s;
this is build time, not prover time. Final cgroup high/max/OOM event counts
remain zero.


## Authoritative gate update and feasibility recheck

Rechecked native E2E build after the gate update: the same incompatible
Init.olean header prevents baseline generation. No compatible replacement
lean-native binary was found in the exposed workspace or /opt. The shared
compiler was not changed. native-recheck.log preserves the failure.

Further call-graph review: the reported PCS phase also includes decodePhases,
signer-set checks and statement construction after provePcsOpenFlat. The phased
total currently ends at t5, with wire serialization reported separately through
t6. On resumption, document this timing boundary against Rust aggregation;
do not mistake a PCS kernel timer for the complete aggregation gate.

Even removing the entire historical ~154.93 s PCS phase would leave about
215.6823 s from a 370.6123 s run. This arithmetic is not a measured speedup:
PCS ownership alone cannot certify the overall <1 s gate. Other phase owners
must resolve the remainder, while this branch still needs a matched baseline
before any PCS candidate edit. Peak RSS must be measured across the full process,
not inferred from PCS-end resident memory.


## Authorized bootstrap resume

Coordinator/user explicitly authorized rebuilding the pinned public compiler
on this same fresh Boat xlarge; coordinator owns TTL. No separate VM or Boat
API is needed. The prior toolchain prerequisite is now active local work, not
a reason to stop the campaign. See BOOTSTRAP.md and TEST_DESIGN.md.

Pinned public source clone completed; committed P0 patch applied with exact
expected LLVM/BuildExe hashes. Sequential turbo-lean lean-native build is active
with LEAN_NUM_THREADS=1 and TURBO_LEAN_MAX_MEMORY_MB=6144. Public fixture export
helpers were rebuilt outside app sources with path relocation only; deterministic
XMSS1400 inputs are being regenerated into pcs-restored-oracle. All fixture
hashes must match before their use as the unchanged baseline.

The cgroup reset to its original cap at the new turn; controls were re-raised
via Python /proc/self/cgroup to 24/22 GiB for feasibility only. No memory-gate
success is claimed. Coordinator can harvest the updated checkpoint immediately.

Bootstrap and P0 canary now pass; the former 4.31/4.35 blocker is resolved.
All omitted full1400 fixtures match their committed SHA-256s and sizes.
Unchanged app native-object build is running with task-local rebuilt compiler.

Unchanged prover linkage and native CLMUL inspection passed. Corrected paired
baseline uses explicit Rust target-cpu=native (generic-Rust attempt excluded).
XMSS4: Lean mean 4.878195301 s, peak RSS 1516535808 B, wire 241473 B;
Rust mean 0.11071572933333333 s. XMSS16: Lean mean 7.620480492 s, peak RSS
1680027648 B, wire 279625 B; Rust mean 0.11292168233333333 s. Both fresh Lean
proofs independently verify 3x with unchanged Rust and expected signer counts.
XMSS1400 Rust mean 2.3668005103333334 s, peak RSS 3953496064 B; full Lean
warmup+repeat3 is active. No candidate or certification claim.

## Diagnostic preparation while unchanged full1400 runs

Prepared tools/make_diagnostics.py (not executed against app sources yet). It
will generate a separate IO replay driver around the actual E2E PCS calls,
with noinline forcing before stop-clock reads. Its results are diagnostics only,
never matched certification. It separates L0 packing/NTT, extension NTT,
queried/unqueried Merkle work, folding, extension commitment and query basis.
Comparing the replay proof byte-for-byte with the unchanged parent and independent
Rust verification is mandatory before trusting its attribution. perf remains denied.

Critical integration correction: Keccak8x hash8LeavesAt/hash1LeafAt always
absorb a 64-word leaf. leafWords only determines leading padZeros; it is NOT a
generic leaf-length parameter. Therefore passing width=48, leafWords=48 would
not refine FlatWhir's extension hash, which absorbs exactly 48 words. Any bounded
existing-kernel integration must stay L0 (64-word padded) unless separate extension
support is implemented and validated. Existing unit tests cover leafWords=64 only.

Full1400 process HWM so far 15899238400 B; not a final measurement. cgroup
24/22 GiB controls remain in effect, all throttle/max/OOM events zero. Two fresh
small Lean proofs have independently verified; no full1400 Lean proof yet.

## Completed unchanged matched baseline

Full1400: warmup 364.511610148 s; measured 356.959524611,
355.062736964, 342.662656722 s; mean 351.5616394323333 s.
PCS phase mean 148.685955360 s. Process peak RSS 17001930752 B,
wall 1431.818044424057 s. Wire 359217 B, VM proof 358656 B.
Fresh proof independently Rust verified three times at expected 1400 signers.
All cgroup throttle/max/OOM counters stayed zero. Rust matched mean
2.3668005103333334 s, peak 3953496064 B. No source optimization implemented.

Time gate fails by 350.5616394323333 s to the 1 s boundary (351.56x).
Memory gate fails by 12706963456 B to the 4 GiB boundary (3.95857x).
Even deleting the entire measured PCS phase leaves about 202.875684 s;
this branch alone cannot certify whole-aggregation acceptance. This is arithmetic,
not an achieved optimization. Final >=5 alternating pairs remain outstanding.

The diagnostic generator is now executed, after full baseline completion.
It creates Tests/Hub/PcsOpeningDiagnostics.lean; this isolated replay is not a
production code edit. Native compilation and byte-identical proof checks follow.
