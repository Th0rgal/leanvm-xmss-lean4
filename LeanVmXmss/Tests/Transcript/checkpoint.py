import base64
import hashlib
import io
import json
from pathlib import Path
import tarfile

root = Path(__file__).resolve().parents[2]
out = root.parent.parent / 'p1-shard-b-out'
out.mkdir(exist_ok=True)
files = sorted(p for top in ['Spec', 'Model', 'Proofs', 'Tests']
               for domain in ['Keccak', 'Transcript', 'Merkle']
               for p in (root / top / domain).rglob('*')
               if p.is_file() and p.suffix in ['.lean', '.py', '.rs', '.toml', '.lock']
               and p.name != 'Standalone.lean' and 'evidence' not in p.parts
               and 'target' not in p.parts)
archive = out / 'shard-b-keccak-transcript.tar.gz'
with tarfile.open(archive, 'w:gz', compresslevel=9) as tar:
    for path in files:
        data = path.read_bytes()
        info = tarfile.TarInfo(str(path.relative_to(root)))
        info.size = len(data)
        info.mode = 0o644
        tar.addfile(info, io.BytesIO(data))
encoded = base64.encodebytes(archive.read_bytes())
(out / 'shard-b-keccak-transcript.tgz.b64').write_bytes(encoded)
manifest = dict(status='incomplete_checkpoint', verification_exit_zero=False,
                    blocker='Strict audit and all 12 scoped MCP checks pass; global verification exits 1 at remaining heap, prover/verifier and native sponge gates',
                 completed=['B v2 archive and all 32 member hashes verified before restoration',
                             '27 source modules kernel checked freshly without lake inner loop',
                            'register permutation, duplex, init, observe, sample, nonceProbe, verifyPow, searchNonce and grind refinements kernel checked',
                            'replay scalar binding, exact finish and remainder rejection contracts kernel checked',
                            'Merkle input domain and pruned exact sibling consumption contracts kernel checked',
                            'pruned shared/duplicate queries and malformed/replay executable Lean tests passed',
                            'actual Rust MerkleBuilder, PrunedMerklePaths, ProverState, verifier transcript exercised',
                            'Rust/Lean differential byte equality; Rust sumcheck reconstruction passed',
                            '12 real MCP calls passed across Keccak permutation, transcript grind and Merkle consumption using actual schemas',
                            'register nonce search minimality and canonical zero-bit grinding kernel checked',
                            'built heap shape, root existence, in-range path existence and path length kernel checked',
                            'Full imported namespace audit rejects every forbidden axiom, including external Field; no exclusions or exceptions',
                            'Five connected protocol mutant comparisons executed successfully: SHA3 domain, swapped children, missing observe tag, register overwrite versus XOR, insufficient PoW',
                            'Register verifyPow rejects noncanonical nonzero nonce for zero bits',
                            'Merkle heap preserves leaves, satisfies all internal parent equations, and refines any matching heap target; kernel checked',
                            'Replay nextScalars exact length, offset consumption and fold-observe binding kernel checked',
                            'Field A v2: all chunk, archive and 19 member hashes verified; exactly 19 source files installed and freshly compiled',
                            'Replay grindCheck soundness, accepted Merkle opening/root/offset binding, and sumcheck exact coefficient length and scalar consumption kernel checked',
                            'General power-of-two Spec Merkle build/inclusionPath/verifyPath completeness kernel checked; constructive array range lookup avoids Classical.choice',
                             'Field Basic v3 installed: 2206 bytes, SHA256 2519ed3878ae7346ee140d2c414daf6fe84d88a291a2aed04b4e719bcce238f9; all 19 Field modules freshly compiled',
                                 'Fresh imported-environment audit: 910 declarations, 849 Shard B, zero forbidden transitive axioms, unsafe/extern flags or generated runtime names; strict coverage 910/910',
                             'Explicit Nat recursors and List folds compile with repaired dependent proofs; zero Shard B _unsafe_rec names',
                             'Prototype concatenated 24-round scalarized Keccak permutation executed with 50 LCNF declarations; not accepted as real-import module lowering',
                             'General expandLevels composition and acceptance decomposition across arbitrary depth partitions kernel checked by induction',
                             'Built heap root refines any matching parent/leaf target; kernel checked',
                              'General accepted sumcheck reconstruction and exact sponge observation binding proved for both eqFactor branches',
                              'Real-import Keccak module compiled to static C-ABI archive and LLVM with 50 LCNF declarations; C driver execution matches register model on five inputs',
                              'All 25 materialized scalar lanes have kernel-checked function equality to their imported register-model definitions',
                              'verify.py executes imported native differential before the unchanged strict audit gate',
                              'General built heap path refines any matching parent/leaf target; sibling positivity derived constructively from depth bounds, without extra assumptions',
                              'Appended scalar replay proved for arbitrary prefix/suffix, sponge and opening state; real nextScalar consumes and observes the inserted value',
                               'Prover addScalar and verifier nextScalar refinement kernel checked for arbitrary prover state and trailing proof stream',
                               'Arbitrary appended scalar sequences replay exactly, including empty sequences, prefix/suffix, exact offset and fold-observe sponge state',
                               'Prover addScalars state and verifier nextScalars refinement kernel checked constructively without Array.foldl_append or Classical.choice',
                               'Challenge following arbitrary scalar sequence agrees between prover and verifier in value and sponge state, preserving proof stream and consumed offset',
                               'addRoundPoly equals addScalars on exact filtered coefficient indices in both branches; verifier nextScalars replays that transmitted stream with exact offset and sponge state; coefficient reconstruction compatibility remains pending',
                                'General sumcheck replay completeness in both eqFactor branches: arbitrary prefix/suffix and transmitted tail accepted with exact reconstructed coefficients, consumed offset and sponge; includes plain degree one',
                                'Constructive filtered-range forms identify addRoundPoly transmitted streams in both branches; actual prover output is accepted by sumcheckRoundPoly with exact reconstructed coefficients, offset and prover sponge, for every coefficient array of size at least two; equality to original coefficients still needs the protocol algebraic relation',
                                 'Both prover sumcheck branches replay the original coefficients under explicit omitted-coefficient compatibility relations, with exact final offset and prover sponge; constructive suffix lookup covers arbitrary tails including plain degree one',
                                 'Extension-field additive cancellation and omitted-coefficient equivalence proved; both prover branches reconstruct original coefficients under reduced claim identities; polynomial evaluation and multi-round protocol invariants remain pending',
                                 'Arbitrary prover scalar sequence replay followed by actual finish succeeds with exact prover sponge and paths when prior openings are consumed; kernel checked including empty sequences',
                                 'Constructive byte-width proof: wordsBytes size is eight times word count; every Digest32 serializes to exactly 32 bytes, is accepted by fromBytes and maps through checkedDigest to the Spec digest; byte-content roundtrip and hashPair refinement remain pending',
                                 'Strict MCP runner validates payloads, nonempty nonvacuous specification audits and kernel verification stages for all 12 calls; copied source project with independent Lake artifacts avoids symlink import freshness failure',
                               'Field recursor bundle: corrected chunks 8000+8000+5644 authenticated; 16232-byte archive SHA256 2d23ba3a6cbf3a2633dd9ae9f57a5051a9144ef891fc87758837b90aa9438a1b, authenticated manifest and all 19 member hashes verified before exact installation; all 19 modules freshly compiled'],
                  pending=['Merkle heap refinement to Spec levels and heap-path inclusion completeness',
                          'general pruned construction/expansion correctness and full prover/verifier refinement',
                           'full verify.py exit zero; latest complete run passes strict audit and exits 1 at remaining required gates; Rust/Lean differential passed',
                            'Real-import native execution currently covers two input lanes, zero-filled remaining state, and output lane zero; general full-state sponge lowering remains pending',
                            'Kernel proof linking full scalarized native permutation to register model remains pending; imported lane function equalities are kernel checked'],
                 audit=dict(allowed_axioms=['propext', 'Quot.sound'], exclusions=[],
                                  external_field_failures=[], declarations=910, shard_b_declarations=849,
                                  forbidden_transitive_axioms=0, unsafe_rec_count=0, strict_coverage='910/910'),
                  verification=json.loads((out / 'evidence/verification.json').read_text()),
                  mcp=json.loads((out / 'evidence/mcp-summary.json').read_text()),
                 imported_native=json.loads((out / 'keccak-imported-execution.json').read_text()),
                prior_native_lowering_declarations=25,
                archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest(),
                archive_bytes=archive.stat().st_size, base64_bytes=len(encoded),
                files=[dict(path=str(p.relative_to(root)),
                            sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in files])
(out / 'shard-b-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps({k: v for k, v in manifest.items() if k != 'files'}, indent=2))
