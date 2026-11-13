# Remaining PCS opening work after the first bounded candidate

The only goal remains full XMSS1400 aggregation <1 s and peak RSS <4294967296 B.
Neither component-only timing nor native microbenchmarks satisfy it. The initial
unchanged mean is351.5616394323333 s /17001930752 B. Even eliminating all PCS
would leave about202.875684 s in that measured pipeline.

The validated single full1400 diagnostic (wire-identical, Rust verified3x) measured
L0 unqueried Merkle44.486610989 s, extension unqueried Merkle34.987183875 s,
extension commitment43.386583250 s, L0 NTT8.879369480 s, extension NTT7.669300184 s,
folding13.912059917 s, and query basis5.314173440 s. These are diagnostic costs,
not matched speedup estimates or an exact additive attribution of the baseline.

The current candidate only addresses L0 unqueried Merkle. A possible next bounded
candidate is a separate48-word leaf kernel for extension commitment/opening.
The existing native leaf kernel always absorbs64 words, regardless of leafWords.
Do not route48-word extension leaves through that API. Exact extension format:
17-word first block,17-word second block, then14 data words plus1,0,bit63 in the
third block; Merkle internal nodes remain the existing64-byte pair hash.

A dedicated8-lane48-word implementation would need independent scalar tail
handling, complete byte/word/digest and pruned-path differentials, default-zero
reads, all-ones/high-bit patterns, queried/unqueried boundaries, transcript/wire
identity, fresh-seed negatives, axiom/purity/ISA/mutation gates and another full
matched4/16/1400 warmup+repeat3 matrix. Keep subtree packing bounded; full-coset
materialization would be a separate memory tradeoff requiring measurement.
No extension candidate is implemented or measured.

The NTT source has confirmed16-byte twiddle boxing and56-byte closure allocation
in the optimized vecPairLoop entry. Explicit tail recursion could isolate this
overhead without changing field arithmetic or Vec8 storage. A universal loop
refinement against foldRangeLoop is feasible using Fin.foldl_succ and induction.
It is a lower-priority hypothesis given the measured L0 NTT share.
