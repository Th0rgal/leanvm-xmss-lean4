# PCS opening campaign checkpoint — 2026-11-13

Status: second candidate gates and full matched matrix COMPLETE; no E2E win; NOT certified.
See latest dated checkpoint below; earlier sections are chronological evidence.
Compatible compiler and fixtures are restored; initial blockers below are archived.
One L0 opening callback and a new bounded helper are changed. Strict <1 second / <4294967296-byte gate.
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

## Diagnostic replay validated on XMSS4

Native kernel differential executable passed all Keccak8x/NTT/Merkle/WHIR tests
at existing 2^4/2^12/2^14 sizes. Its microbench output is retained as execution
evidence only, not E2E improvement. Separate PCS replay generated a byte-identical
XMSS4 proof (cmp PASS) and unchanged Rust verification passed 3x.

XMSS4 diagnostic attribution: first-coset packing 0.042556663 s, L0 NTT
0.053344963 s, extension NTT 0.034119466 s, queried leaves 0.627057356 s,
queried tree builds 0.205548335 s, unqueried Merkle roots 0.246648847 s,
extension commitments 0.540308820 s, folding 0.179988957 s, query grinding
1.013366538 s. This is one instrumented pass, not a certified benchmark.
Full1400 diagnostic is active under durable runner PID 135560; no candidate
selected based solely on small-case behavior. Whole-source purity scan passes:
129 Lean files, zero forbidden tokens/non-Lean FFI files in Spec/Model/Native/Proofs.

## First measured-hot-path candidate (not yet performance accepted)

Full1400 isolated diagnostic completed: exact wire equality to unchanged parent,
SHA-256 9fcdb0ac8e76b81bbbb6cd42827aca27ef918c02d1f42e93865321b0b8d638a6,
Rust verification PASS 3x. L0 dimensions: 106954752 words, 51 lanes, stackLog27,
logRows21, nVecs7. Unqueried L0 Merkle 44.486610989 s across 3879 calls;
L0 NTT 8.879369480 s; initial fold 13.235770100 s; first extension commit
25.161634555 s. Total instrumented PCS 169.954436581 s versus unchanged matched
mean 148.685955360 s: instrumentation/host variance means these are attribution,
not a benchmark comparison or speedup. Native profiling output is retained.

Candidate adds Model/Pcs/MerkleBatch.lean and replaces only openL0Cosets'
unqueried-subtree callback. It packs at most 1024 rows / eight Vec8s per row
(512 KiB scratch upper bound, actual L0 448 KiB), then uses the existing native
64-word-padded leaf kernel. Queried trees and extension hashing are unchanged.
Explicit small-tree/width/range guards retain scalar fallback; failed root decoding
also falls back lazily. No compiler, KeccakGkr, transcript or parameter changes.

Native differential tests PASS: packed all-eight-lane order, zero default tails,
widths0..9, depth0/1/3/4/10/11, zeros/allones/highbits/pseudorandom,
base offsets/truncated buffers, complete opened rows and ordered siblings,
duplicates/boundaries/invalid queries, both rate1 cosets (also rate2), lanes51
and other padded widths. Existing native kernel suite reran PASS. These are
execution refinement tests; a universal Keccak8x-to-scalar theorem is NOT claimed.
Whole-repo/purity/mutation gates and matched4/16/1400 timing remain pending.

## Candidate correctness gates complete; matched matrix active

Whole-source purity: 130 files, zero violations. Targeted PCS/native audit:
598 declarations / zero rejections. WHIR audit: 1072 / zero. Whole-repo audit:
10319 / zero, axioms only propext/Quot.sound (existing documented broken-test
import exclusions remain). Native-symbol/ISA audit: no unexpected undefined
or crypto FFI symbols; vector and CLMUL instructions present. These static ISA
counts do not alone establish dynamic hot-path attribution. Generated FlatWhir C
explicitly calls MerkleBatch.subtreeRootBuf from the L0 callback.

Dual mutation harness: Lean and unchanged Rust each accept34/34 baseline wires
and reject34/34 mutations, zero disagreements. Distinct seed/fresh5 parent and
candidate proofs are byte-identical (242345 B), each Rust verified3x. Exact
strict-proofs gate now passes1102/1102 with the locally rebuilt pinned CLI;
installed CLI's unsupported flag failure is preserved, not silently waived.
See candidate-gates-consolidated.json for exact result provenance.

Matched4/16/1400 matrix is active, fresh warmup+repeat3, same compiler/native
Rust flags, independent Rust verification and byte-for-byte unchanged-parent
wire comparison. Candidate binary SHA-256:
17d726988ec3a9ccfb82de896f17dd1eb6207981cab730a917fe49505a1c2017.
No speedup, peak-RSS reduction or certification is claimed before completion.

## First candidate full matched result: NOT promoted

Warmup360.822977912 s; measured352.065413901,354.214879587,358.678112100 s;
mean354.986135196 s, sample stdev3.373139603 s. Wall1438.231102705 s.
PCS mean146.389741362 s (only2.296213998 s /1.544% below baseline);
aggregation is3.424495764 s slower. Peak16517795840 B (484134912 B below baseline).
Both strict gates FAIL:354.986x time threshold,3.845849x RSS threshold;
gaps353.986135196 s and12222828544 B to the boundaries.
Wire359217 B / VM proof358656 B, exact unchanged wire identity; independent
Rust verify3x:460,10,10 ms. All memory/CPU throttle and OOM counters zero.
This is one matched candidate pair, not >=5-pair certification or an E2E win.

Packing still uses8 runtime ByteArray.push calls per word: at3879 unqueried L0
subtrees,1024 rows and56 words/row, this implies1779499008 byte-push calls for
the measured full1400 query pattern. Static code confirms those runtime calls;
the count is derived from the validated diagnostic dimensions/call count. Next
bounded revision will copy a shared zero template and use existing proof-bounded
USize stores, retaining the old packer as a differential oracle and fallback.
It must rerun all gates and another full matched matrix; no improvement assumed.

## Bounded fast-packing revision — correctness checkpoint

Retained push packer as oracle/fallback; bounded path uses existing safe USize
stores into an extracted immutable 512KiB zero template. No compiler/kernel,
protocol or extension-leaf changes. Native differential tests and existing kernel
suite pass. Whole-repo audit:10321 declarations,0 rejects. Fresh XMSS4 and
distinct-seed fresh5 wire bytes exactly match unchanged; Rust verifies each3x.
Generated fast-loop C has zero byte-push calls versus64 static sites in old loop.
This is mechanism evidence, not a measured performance claim. Comprehensive
mutation/strict-proof gate is active; fresh matched4/16/1400 follows.

Exact comprehensive gate PASS: purity130 files, clean Rust reference,
10321 declarations / allowed axioms only, strict specs1102/1102,
Lean and Rust each34 baseline accepts and34 mutation rejects.

## Fast-packing full matched result — not promoted

Warmup335.350313040s; passes350.444615351,368.279666582,348.921544292s.
Mean355.881942075s (sample stdev10.763717577s), wall1416.209074259s.
PCS140.814156462s:7.871798898s /5.294% below unchanged148.685955360s.
Total mean is4.320302643s slower than baseline351.561639432s; no E2E win.
Other phase variation prevents a causal whole-process speedup claim.
Peak16708775936B,293154816B below unchanged, still3.890315x memory threshold.
Strict time/memory gates FAIL: gaps354.881942075s and12413808640B.
Wire359217B / VM358656B, exact baseline bytes. Rust verifies3x (517,12,12ms).
Rust control mean2.074603905s, peak3951775744B. Memory-limit/OOM events zero.
Small matched means:XMSS4 4.377816103s/RSS1556328448B;
XMSS16 7.310990630s/RSS1729232896B; exact wires and Rust verification3x.
One candidate pair per workload only; >=5 alternating full1400 certification
pairs remain unperformed. No acceptance, promotion or completion claim.

Next work should profile extension 48-word hashing and boxed NTT/allocation
with full-path diagnostics before another production edit. Existing64-word
Keccak8x leaf kernel must not be passed48 as a purported equivalent kernel.
PCS-only improvement cannot remove the >200s remainder; coordinate phase owners.
No further source change is pending. Exported bundle/patch and evidence archive
are ready for harvest. Keep VM until coordinator acknowledges; TTL owned by
coordinator, no destruction requested.

## Additional same-candidate full1400 pair COMPLETE

No source/binary changes. Fresh Rust control then Lean warmup336.157928189s;
passes342.943689158,344.756919342,362.415487470s; mean350.038698657s.
Wall1401.703s, peak16549629952B. Wire359217B / VM358656B, exact unchanged
baseline; independent Rust verification3x PASS. Memory-limit/OOM events zero.
Together with prior pair this is two full1400 candidate pairs, six measured
passes, fewer than required five pairs: no certification. Pair means straddle
baseline; no repeatable E2E win established, both strict gates fail.
Previous export filenames remain frozen. New immutable milestone exports
use pcs-opening-milestone2-* names for harvest before coordinator-owned TTL.

## Diagnostic timing-boundary inspection

Inspected actual executed pcs-diagnostic binary SHA256
da0f677c70a00fbe1ecf851a07a7587586c3e4a33c29d6d17934b01f3a34f026.
measuredIO redArg calls first clock at0x8b71, lean_apply_1 at0x8b81,
second clock at0x8bc0. No reliance on noinline: forceResult's IO allocation
is visible inline in native code. Generated C shows the thunk captures inputs,
then executes fastSubRoot via lean_apply_3 when called. Native L0 Merkle lambda
tail-jumps Commit.subtreeRootBuf; L0/extension NTT lambdas tail-jump
Ntt.encodeCosetVec8; extension commitment lambda calls commitExtPlanar.
Work is inside the inspected clock boundaries, not precomputed in these closures.
Saved generated-C excerpts and actual executable disassembly with binary hashes.

Existing full1400 diagnostic proof rechecked byte-equal to immutable parent,
SHA2569fcdb0ac8e76b81bbbb6cd42827aca27ef918c02d1f42e93865321b0b8d638a6;
unchanged native Rust reverified3x PASS. This is another verification of the
existing diagnostic proof, not another fresh proving/certification pass.
No timer-overhead calibration claimed; tiny intervals include IO/closure
allocation overhead. Diagnostic attribution remains instrumented evidence,
not matched E2E speedup. Parent timed baseline and production code unchanged.

## Operator checkpoint policy ACK — 2026-11-13T12:35 UTC

Every worker must commit AND push WIP at least every30min and before ANY
VM TTL/cap/stop/destruction. No credentials on managed VM: export bundle,
patch and SHA for coordinator authenticated push. Checkpoint is INCOMPLETE
until coordinator confirms remote ref AND off-VM benchmark artifact harvest.
All benchmark proofs/timing/RSS/verification logs exported in stable chunks
<=20MiB under /var/lib/orb-node/work/pcs-benchmark-harvest. Propagate to any
future children. No VM cleanup before confirmed harvest. Coordinator owns TTL.
Latest confirmed remote/harvest acknowledgement is8dac390; newer local heads
are pending exact acknowledgement. Existing milestone exports remain frozen.

## Dedicated48-word extension-opening candidate: correctness PASS

New Native.Kernels.KeccakExt48 uses exactly17+17+14 data words plus1,0,
terminal high-bit padding. Existing64-word L0 kernel unchanged. Integration
only unqueried openExtCosets subtrees width48/nVecs6,depth3..10, bounded
384KiB packing plus existing shared512KiB zero template; other cases scalar.
commitExtPlanar unchanged. No KeccakGkr/compiler changes.
Native leaf/root/path differentials (all8 lanes,0/allones/highbits/random,
offsets/default tails,depth/width fallback,duplicates/boundary/invalid queries,
both rate1 cosets and rate2) PASS; existing L0 and kernel suites PASS.
Fresh4 and distinct-seed5 proofs match unchanged wire bytes, Rust verifies3x.
Exact comprehensive gate PASS:131 source files,10327 declarations/0 rejects,
axioms only propext/Quot.sound,strict specs1102/1102; native symbol/ISA gate
PASS; both Lean/Rust accept34 baseline/reject34 mutations.
These are execution refinement tests, not universal Keccak refinement theorem.
Matched fresh4/16/1400 warmup+repeat3 is launching; no speedup claim yet.
Incorrect initial test-target invocation retained; corrected full build PASS.

## Ext48 full matched matrix COMPLETE — provisional, not promoted

Full1400 warmup333.078648364s; passes337.303694192,352.895667494,349.816974303s;
mean346.672111996s, wall1388.518s. PCS134.968388496s.
Against unchanged:mean4.889527436s lower(1.391%);PCS13.717566864s lower(9.226%).
Against fastpack first pair:mean9.209830079s lower;PCS5.845767966s lower.
Timing ranges overlap prior measurements; only one ext48 pair. No repeatable
E2E speedup or causal improvement established, no promotion or certification.
Peak16594870272B,407060480B below unchanged. Both strict gates FAIL:
time346.672x threshold/gap345.672111996s;RSS3.863794x/gap12299902976B.
Wire359217B/VM358656B exact unchanged bytes, independent Rust verification3x.
All memory-limit/OOM events zero. No build or competing benchmark during matrix.
Small cases:XMSS4 mean4.877127636s/RSS1484107776B;
XMSS16 mean6.789829360s/RSS1584660480B; exact wires and Rust3x each.
Rust full control mean1.979298736s/RSS3960688640B, same native binary
built with target-cpu=native; reference59c2984 unchanged.

Remaining:>=5 alternating fresh same-host Rust/Lean candidate pairs; strict
<1s/<4294967296B total process acceptance is still far open. Further extension
commitment batching is unimplemented and requires its own gates and matrix.
No time remains for another full candidate before coordinator-owned13:40TTL.
Stable all-artifact chunk export and latest source bundle must be harvested
and pushed with exact remote-ref confirmation before checkpoint is complete.

## Additional ext48 pair checkpoint 2026-11-13T14:03:25.659093+00:00

Exact remote+offVM preservation confirmed throughcfa3f738. Additional fresh
full1400 Rust/Lean pair running durable PID833361, same preserved binaries,
no source changes/build overlap. Current receipt status:RUNNING.
This is PARTIAL and does not count as completed/certified pair until final
receipt and fresh proof verification. Checkpoint before14:05 deadline;
cap14:40:02UTC, backupmargin14:25. No cleanup authorization.

## Additional ext48 full1400 pair COMPLETE

Warmup344.528185771s; passes348.021198769,383.810447481,368.526813252s;
mean366.786153167s, wall1465.660s, peak16523329536B. Rust verify3x PASS;
wire359217B exact unchanged parent. Memory-limit/OOM event deltas zero.
No source edits or builds overlapped run; tiny partial snapshot exported near
end before14:05 checkpoint deadline. Rust control mean1.951800262s.
Two ext48 pairs pooled mean356.729132582s. Second pair
materially slower than first346.672111996s; no repeatable E2E gain established.
Both strict gates FAIL. Two pairs only, not required five: no certification,
no promotion. No additional full benchmark planned before14:40:02TTL.
Complete final evidence export required and checkpoint incomplete until
coordinator confirms exact remote ref and OFF-VM harvest. No cleanup authorized.
