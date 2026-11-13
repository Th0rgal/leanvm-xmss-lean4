# PCS candidate acceptance design

The sole gate is full XMSS1400 aggregation strictly <1 second and peak RSS
strictly <4294967296 bytes, matched measured passes. No candidate is implemented
before a compatible unchanged full baseline. All numbers below describe design,
not executed tests or measured attribution.

## Establish the unchanged parent

Restore bytecode, hints, schedule and inputs, checking the committed SHA-256s.
Record Lean/Rust/native compiler commits, P0 patch hash, flags and executable
hashes. Build both parent and candidate with the same toolchain and host.
Fresh processes: full warmup, repeat=3, log_inv_rate=1, XMSS4/16/1400. Record
unrounded phase/aggregate times, wall time, process peak RSS, VM proof size and
wire size separately. Verify every retained fresh proof independently with
unchanged leanVM@59c2984 and check record/signature counts and statement/digest.
Monitor nested cgroup memory.high/max/oom counters around each run; raised caps
are feasibility controls, never satisfaction of the RSS gate.

## Instrument actual PCS opening in a diagnostic build

Keep an untouched baseline executable. Trace the following existing boundaries
in a separate diagnostics-only variant; exclude that variant from certification:
termsOf, projectStack, buildLaneMatrixA, foldWitnessAndLift, stepFoldPlanar,
commitExtPlanar, introduceOodPlanar, grindWhirFast, openL0Cosets/openExtCosets,
inducedBasisPlanar, glueBasisPlanar. Report invocation counts and dimensions
alongside time, not a disconnected synthetic kernel benchmark. PCS phase also
includes decodePhases and final statement checks in E2E's current timer.

Inspect generated LLVM/C for allocation/boxing/RC in Model.Pcs.Ntt.vecPairLoop,
FlatWhir.wordAt, foldPlanar/msgPlanar, foldWitnessAndLift and hashLeafExtVec8.
Count emitted lean_alloc_ctor/lean_box_uint64/lean_inc/lean_dec sites and inspect
symbol bodies; static counts are not dynamic allocation counts. Pair profiler
samples with input/codeword sizes and array sharing to distinguish arithmetic,
packing, COW copying and Merkle hashing. Never assume hoisting the first coset
is free: sharing its Array Vec8 across cosets can trigger COW.

## Candidate refinement boundaries

For a byte-codeword replacement, compare all decoded words against
encodeCosetVec8, including padded leading lanes, both cosets at rate1, layer0
and tails. Then compare *complete* pruned paths (opened rows and ordered siblings)
from openL0Cosets/openExtCosets, not just roots. Preserve sorted/deduplicated
queries, queried-row order, transcript scalars and serialized phase bytes.
Small tests use Spec/Model oracles; actual extracted full1400 dimensions use
unchanged parent differential output. Zero words, high bits, all-ones words,
non-multiples-of-8 lane widths, duplicate queries, boundary queries and invalid
indices are required. Invalid indices must retain rejection semantics.

For fold/sumcheck changes, compare all three E limbs against foldPlanar/msgPlanar
and the scalar model at each challenge boundary, including empty/odd/truncated
inputs if exposed by the existing function contract. Prove representation and
loop refinement, without native_decide, sorry, unsafe, extern or new axioms.
Hash/root equality alone does not establish fold correctness.

Negative controls: flip row data, sibling, root, transcript scalar, signature,
message and key; malformed length, query order and trailing bytes. Retain the
unchanged verifier's rejections. Separate proof theorem evidence from native
execution tests and compiler/runtime trust boundaries.

## Promotion

After each application change: all available correctness, strict transitive
purity and frozen-source/fixture gates, native kernel differentials, then matched
full E2E XMSS4/16/1400 warmup+repeat3. Reject changes without justified E2E benefit.
Final certification remains >=5 alternating same-host Rust/Lean fresh-proof
pairs with all runs retained. Report mean/dispersion, all RSS peaks, both proof
sizes and verifier timings. No cached-proof reuse or minimum-only reporting.
