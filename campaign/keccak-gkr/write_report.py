#!/usr/bin/env python3
"""Render the completed campaign; refuse incomplete final acceptance data."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import statistics
import subprocess

p = argparse.ArgumentParser()
p.add_argument('--evidence', required=True, type=Path)
a = p.parse_args()
e = a.evidence.resolve()
here = Path(__file__).resolve().parent
repo = here.parents[1]
state = json.loads((e / 'final-campaign-status.json').read_text())
assert state['complete']
winner = state['winner']

def summary(name):
    data = json.loads(subprocess.check_output(
        ['python3', here / 'summarize.py', e / name], text=True))
    assert data['complete']
    (e / (name + '-summary.json')).write_text(json.dumps(data, indent=2) + '\n')
    return data

def gkr(row):
    return statistics.mean(x['lean']['phase_means_nanos']['4_keccak_gkr']
                           for x in row['pairs'].values()) / 1e9

final = summary('final')
control = summary('baseline-final-control')
original = summary('baseline')
attempts = {}
for i in range(1, int(winner.removeprefix('candidate')) + 1):
    name = f'candidate{i}'
    attempts[name] = (json.loads((e / 'candidate4-accepted-summary.json').read_text())
                      if i == 4 else summary(name))
fs = json.loads((e / 'final/status.json').read_text())
assert all(x['exit_code'] == 0 for x in fs['commands'])
for n in ['4', '16', '1400']:
    assert final['paired'][n]['pair_count'] >= 5
    for row in final['paired'][n]['pairs'].values():
        assert len(row['lean']['passes_nanos']) == len(row['rust']['passes_nanos']) == 3
for command in fs['commands']:
    if command['label'].endswith(('-lean', '-rust')):
        text = Path(command['log']).read_text()
        assert len(re.findall(r'^WARMUP\|', text, re.M)) == 1
        assert len(re.findall(r'^PASS\|i=', text, re.M)) == 3
for path, detail in fs['proofs'].items():
    n = re.search(r'xmss(\d+)-', Path(path).name)[1]
    reference = e / 'baseline' / f'xmss{n}-pair1.ethproof'
    assert Path(path).read_bytes() == reference.read_bytes()
    assert hashlib.sha256(Path(path).read_bytes()).hexdigest() == detail['sha256']
for path, digest in state['binary_sha256'].items():
    assert hashlib.sha256(Path(path).read_bytes()).hexdigest() == digest
frozen = json.loads((e / 'frozen-protocol-sources.json').read_text())
assert all(hashlib.sha256((repo / 'LeanVmXmss' / path).read_bytes()).hexdigest() == digest
           for path, digest in frozen.items())

subprocess.run(['python3', here / 'summarize_profile.py', '--evidence', e,
                '--candidate', winner.removeprefix('candidate')], check=True)
profile = json.loads((e / (winner + '-profile-xmss1400-gkr-summary.json')).read_text())
rows = profile['rows']
inner = sum(r['calls'] for r in rows if r['kind'] == 'lean_alloc_ctor'
            and ('productBucketLoop_spec__' in r['function']
                 or 'accumulateProductLimbs' in r['function']))
boxes = sum(r['calls'] for r in rows if r['kind'] == 'lean_box_uint64')
initial = sum(r['calls'] for r in rows if r['kind'] == 'lean_alloc_ctor'
              and r['function'].endswith('_productBucketLoop'))
pair_objects = sum(r['calls'] for r in rows if r['kind'] == 'lean_alloc_ctor'
                   and 'pairSumsRangeFlat_spec__0' in r['function'])
row_objects = sum(r['calls'] for r in rows if r['kind'] == 'lean_alloc_ctor'
                  and 'foldRowsFlat_spec__0' in r['function'])
cow = sum(r['bytes_or_nanos'] for r in rows if r['kind'] == 'lean_byte_array_set'
          and 'foldRowsFlat' in r['function'])
f = final['paired']['1400']
c = control['paired']['1400']
o = original['paired']['1400']
rust_peak = max(x['rust']['peak_rss_bytes'] for x in f['pairs'].values())
phases = {k: statistics.mean(x['lean']['phase_means_nanos'][k]
                            for x in f['pairs'].values()) / 1e9
          for k in next(iter(f['pairs'].values()))['lean']['phase_means_nanos']}
verify = []
for cmd in fs['commands']:
    if cmd['label'].startswith('xmss1400-') and cmd['label'].endswith('-verify'):
        text = Path(cmd['log']).read_text()
        verify.extend((int(i), int(ms)) for i, ms in
                      re.findall(r'VERIFY_ETH\|PASS\|pass=(\d+)\|ms=(\d+)', text))
resources = []
for line in (e / 'final-resource-samples.jsonl').read_text().splitlines():
    resources.append(json.loads(line))
events = {}
for row in resources:
    for key, value in re.findall(r'^(\w+) (\d+)$', row.get('memory.events', ''), re.M):
        events[key] = max(events.get(key, 0), int(value))
manifest = dict(base='299c689373ef3e98e0f150ff4bec21ca5e3aaea1', winner=winner,
    implementation_commit=subprocess.check_output(['git', 'log', '-1', '--format=%H',
        '--', 'LeanVmXmss/Model/KeccakGkr/Flat.lean'], cwd=repo, text=True).strip(),
    final=final, baseline_final_control=control, original_baseline=original,
    candidate_matched_attempts=attempts,
    phase_means_seconds=phases, binary_sha256=state['binary_sha256'], proofs=fs['proofs'],
    final_scope_memory_events=events, full_profile_inner_constructors=inner,
    full_profile_uint64_boxes=boxes, full_profile_potential_row_cow_bytes=cow)
(here / 'final-results.json').write_text(json.dumps(manifest, indent=2) + '\n')

lines = ['# Keccak GKR campaign final report', '',
    f'Base `{manifest["base"]}`; branch `campaign/keccak-gkr`; selected implementation '
    f'`{manifest["implementation_commit"]}` ({winner}).', '',
    f'Final XMSS1400 mean E2E **{f["lean_mean_seconds"]:.6f}s**, GKR **{gkr(f):.6f}s**, '
    f'peak RSS **{f["lean_peak_rss_bytes"]}B** ({f["lean_peak_rss_bytes"]/2**30:.6f}GiB). '
    f'Frozen Rust mean {f["rust_mean_seconds"]:.6f}s, peak {rust_peak}B; '
    f'Lean/Rust mean-time ratio {f["lean_over_rust_time_ratio"]:.3f}. '
    'The authoritative strict <1 second / <4 GiB (4294967296 bytes) gate remains unmet. All earlier targets are superseded.', '',
    '## Matched final measurements', '',
    'Every pair uses sequential Rust then Lean on this host, each a fresh process with one '
    'warmup and three timed full recomputations. `/usr/bin/time -v` measures fresh-process '
    'peak RSS. Every emitted Lean proof is byte-compared with the pre-edit baseline and '
    'independently verified by clean leanVM@59c2984 using positional '
    '`verify-eth <xmss-inputs.bin> <proof> N 1`. No proving output is reused as input. '
    'No campaign build or diagnostic overlaps acceptance timing.', '',
    '| XMSS | Pairs | Lean mean s | GKR mean s | Rust mean s | Lean peak B |',
    '|---|---:|---:|---:|---:|---:|']
for n in ['4', '16', '1400']:
    row = final['paired'][n]
    lines.append(f'| {n} | {row["pair_count"]} | {row["lean_mean_seconds"]:.6f} | '
                 f'{gkr(row):.6f} | {row["rust_mean_seconds"]:.6f} | {row["lean_peak_rss_bytes"]} |')
lines += ['', '| XMSS1400 control | Lean total s | GKR s | Rust s | Lean peak B |',
    '|---|---:|---:|---:|---:|']
for label, row in [('Original pre-edit baseline', o), ('Fresh saved-baseline control', c),
                   ('Final five-pair selected binary', f)]:
    lines.append(f'| {label} | {row["lean_mean_seconds"]:.6f} | {gkr(row):.6f} | '
                 f'{row["rust_mean_seconds"]:.6f} | {row["lean_peak_rss_bytes"]} |')
lines += ['', '| Candidate XMSS1400 matched gate | Lean total s | GKR s | Rust s | Peak B |',
          '|---|---:|---:|---:|---:|']
for name, attempt in attempts.items():
    row = attempt['paired']['1400']
    lines.append(f'| {name} | {row["lean_mean_seconds"]:.6f} | {gkr(row):.6f} | '
                 f'{row["rust_mean_seconds"]:.6f} | {row["lean_peak_rss_bytes"]} |')
lines += ['', 'Host/phase drift is substantial; raw differences between candidates are not '
    'causal speedup estimates. The fresh baseline control and final per-pair raw samples '
    'are retained in `final-results.json`. Confidence intervals in the summary assume '
    'independent pair means and do not establish host stability.', '',
    f'Final observed non-GKR phase subtotal:{sum(v for k, v in phases.items() if k != "4_keccak_gkr"):.6f}s. '
    'This is a measured phase budget, not a mathematical lower bound after arbitrary '
    'pipeline changes; further E2E work requires the other owners.', '',
    '## Authoritative gate and historical gaps', '',
    '| Target time / RSS | Time ratio | Excess seconds | Excess RSS B |',
    '|---|---:|---:|---:|']
for gap in f['target_gaps']:
    lines.append(f'| <{gap["target_seconds"]}s / <{gap["target_gib"]}GiB | '
        f'{gap["time_ratio"]:.3f} | {gap["excess_seconds"]:.6f} | {gap["excess_rss_bytes"]:.3f} |')
lines += ['', f'Historical total370.612s: final delta {f["lean_mean_seconds"]-370.612:+.6f}s. '
    f'Historical RSS15038140416B: final delta {f["lean_peak_rss_bytes"]-15038140416:+d}B. '
    f'Historical GKR153.06s: final delta {gkr(f)-153.06:+.6f}s. '
    'Those historical runs are not matched controls. Wire remains359217B.', '',
    '## Actual path and optimization', '',
    '`Model.Cli.E2E.proveKeccakGkrOnlyWq` calls `Model.KeccakGkr.Flat.proveReductionFlat`. '
    'Standalone `Native.Kernels.KeccakGkr` kernels are absent from that import/call path. '
    'Whole-binary SIMD instruction counts therefore do not certify vector GKR integration. '
    'The measured hot path is scalar sumcheck/product and row-fold work.', '',
    'A noinline UInt64-limb helper keeps the owned E accumulator live across planar reads, '
    'allowing reuse instead of one allocation per bit position. RoundETape is consumed '
    'before creating its destination-fold closure. Packed reads use proved USize byte '
    'indices and a cheap representable size guard with the exact original fallback. '
    'All-buffer/all-offset/shift and all-tape refinements preserve prior total semantics, '
    'including malformed/truncated buffers and aliases.', '',
    'Candidate2 failed its intended reuse hypothesis. Candidate5 showed severe within-run '
    'drift (350.160/557.905/553.564s totals) and no reliable E2E gain. Candidate6 exposed '
    'per-read `lean_cstr_to_nat("4294967296")`; runtime assembly constructs/parses mpz '
    'before returning a tagged Nat. The selected guard uses2^32−1, which emits an immediate '
    'comparison. No compiler source was edited.', '',
    '## Full-size allocation diagnostic', '',
    f'Actual XMSS1400 instrumented product-loop constructors (candidate2→{winner}):'
    f'29569843200→{inner}; '
    'the prior inner constructors requested946234982400 cumulative bytes including headers '
    f'but excluding allocator rounding. Initial bucket objects remaining:{initial}. '
    f'Instrumented UInt64 boxing calls:{boxes}. Row-fold potential shared-input COW '
    f'payload:226492416000→{cow}B. Instrumented pair-sum loop objects:{pair_objects}; '
    f'row-fold loop objects:{row_objects}.', '',
    'These are selective generated-C counters, not total runtime allocations, peak RSS or '
    'DRAM traffic. Timers are nested aggregate thread CPU, not native wall time. '
    'Parent timers exclude CPU used by spawned child threads. '
    'Instrumentation may change inlining. The full diagnostic proof is byte-identical '
    'and independently verified; diagnostic executables are excluded from acceptance.', '',
    '## Correctness, purity and scope', '',
    'All selected-version gates passed: native128-instance×24-round permutation vs Spec; '
    'RMFE vs Spec; F192 fold vs Model; native972 bucket cases;72 ownership cases;960 read '
    'boundary/wrapping cases; positive baselines and34 mutations in both Lean and frozen '
    'Rust; whole/transitive axiom audit; static purity; per-file nonvacuous/tight spec '
    'audits; unchanged native symbol/ISA audit; protocol-source hash checks; all-size '
    'matched gates; final>=5 pairs. Application extern/unsafe/sorry/crypto FFI remain zero; '
    'axioms stay within propext/Quot.sound. No protocol, security, log_inv_rate, transcript, '
    'wire, PCS, bus, compiler, proof-caching or duplicate-definition-linker changes.', '',
    'The installed CLI rejects `audit-spec --policy strict-proofs`. That named global '
    'policy gate remains unsupported and is not claimed passed. Available per-file spec '
    'audits and the unchanged whole/transitive purity/axiom audits passed.', '',
    '## Resources and handoff', '',
    'Initial observed scope max8973910016B (8.358GiB), high8076517376B (7.522GiB) were insufficient; the operator also reported prior8.56/7.7GiB caps. Durable campaign scopes use '
    '26GiB max/24GiB high. Ancestor CPU quotas showed no throttling; cgroup samples retain '
    f'memory/CPU pressure and events. Final scope memory-event maxima:{events}. '
    'Builds used jobs1/max-memory6144/LEAN_NUM_THREADS1; babylon was never built. '
    'The compatible frozen compiler plus its recorded existing repair was rebuilt; '
    'compiler SHA79b805002e329a6eee167403265daa91b50467a4169c8e735d0e843eca3cc6ba.', '',
    'Bus profiling is read-only: see `bus-next-wave-profile.md`. Balance/product-tree '
    'allocation is the leading next-wave hypothesis ahead of constraint rounds. '
    'Bus source hash724458dc9bd2a9ed9a489081a3af77718eb7d1bb0e8affde81dcd9545a9daab3 '
    'is unchanged. Constructor/boxing counters across the candidate2/5 full bus diagnostics '
    'match at52 sites.', '',
    f'Evidence root:`{e}`. Raw run status/log/phase/proof files live in `baseline/`, '
    '`baseline-final-control/`, candidate directories and `final/`. Full diagnostic '
    'CSVs/site maps, normal disassemblies, audits, fixture hashes, compiler provenance '
    'and scope-resource samples are retained. `final-results.json` embeds all final '
    'samples, phase means, proof/binary hashes and target gaps.', '',
    'No credentials/secrets or VM snapshots were used. Anonymous GitHub writes are '
    'unavailable; export git bundle+patch+SHA256 under durable evidence for coordinator '
    'harvest/push. No TTL/lifecycle/coordinator tool was exposed. Request cleanup only '
    'after refs and evidence have been harvested.', '']
if verify:
    lines += [f'Independent Rust verification: cold first-pass mean'
        f'{statistics.mean(ms for i, ms in verify if i == 1):.3f}ms; subsequent-pass mean'
        f'{statistics.mean(ms for i, ms in verify if i > 1):.3f}ms. '
        'These include the verifier harness behavior and are separate from proving time.', '']
(here / 'final-report.md').write_text('\n'.join(lines))
print(here / 'final-report.md')
