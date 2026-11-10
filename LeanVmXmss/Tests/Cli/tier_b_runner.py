"""The W4 Tier B alternating benchmark runner.

Runs the Rust `e2e-oracle benchmark` and the Lean `cli-check bench` on the same
oracle fixtures in ALTERNATING fresh-process pairs (at least 5 by default),
recording exact unrounded per-pass nanos, arithmetic mean, stddev, 95% CI, the
`/usr/bin/time -v` ru_maxrss high-water mark per implementation, proof_size(),
and the unchanged-Rust verification status.

Usage:
    python3 Tests/Cli/tier_b_runner.py <oracle-root> <out-dir>
        [--fixtures xmss4,xmss16] [--pairs 5] [--repeat 3] [--cooldown-ms 2000]
        [--impls rust,lean-stub,lean-vm]

Smoke test (Rust vs Rust dry-run + Lean CLI stub):
    python3 Tests/Cli/tier_b_runner.py <oracle-root> <out-dir> --fixtures xmss4 \
        --pairs 2 --impls rust,rust-dry,lean-stub
"""

import argparse
import json
import math
import os
from pathlib import Path
import re
import subprocess
import sys

root = Path(__file__).resolve().parents[2]
hub = os.environ.get('HUB', '/var/lib/orb-node/work/caches/xmss-hub-v3')
e2e = Path(os.environ.get('CARGO_TARGET_DIR', str(Path(hub) / 'targets/rust'))) / 'release/e2e-oracle'
cli_check = Path(hub) / 'artifacts/w4-cli-traces-tierb/cli-check'
XMSS_OF = {'xmss4': 4, 'xmss16': 16, 'xmss1400': 1400}

# Student-t two-sided 95% critical values by degrees of freedom (n - 1).
T95 = {0: float('nan'), 1: 12.706, 2: 4.303, 3: 3.182, 4: 2.776, 5: 2.571,
       6: 2.447, 7: 2.365, 8: 2.306, 9: 2.262, 10: 2.228, 11: 2.201,
       12: 2.179, 13: 2.160, 14: 2.145, 15: 2.131, 16: 2.120, 17: 2.110,
       18: 2.101, 19: 2.093, 20: 2.086, 21: 2.080, 22: 2.074, 23: 2.069,
       24: 2.064, 25: 2.060, 26: 2.056, 27: 2.052, 28: 2.048, 29: 2.045}


def t95(n):
    return T95.get(n - 1, 1.96 if n > 30 else T95[29])


def parse_bench(text):
    """Parse the machine-readable benchmark protocol both implementations emit."""
    out = {}
    for line in text.splitlines():
        if line.startswith(('BENCH|', 'WARMUP|', 'STATS|', 'LAST|', 'VERIFY|')):
            kind, _, rest = line.partition('|')
            fields = dict(part.split('=', 1) for part in rest.split('|') if '=' in part)
            out.setdefault(kind, []).append(fields)
        elif line.startswith('PASS|'):
            out.setdefault('PASS', []).append(
                dict(part.split('=', 1) for part in line.partition('|')[2].split('|') if '=' in part))
    return out


RSS_RE = re.compile(r'Maximum resident set size \(kbytes\): (\d+)')


def run_and_parse(label, argv, timeout, logs):
    """Run one fresh process under /usr/bin/time -v and parse its protocol."""
    timed = ['/usr/bin/time', '-v'] + argv
    result = subprocess.run(timed, cwd=root, text=True, capture_output=True, timeout=timeout)
    text = result.stdout + result.stderr
    logs.write_text(f"$ {' '.join(argv)}\n\n{text}")
    if result.returncode:
        raise RuntimeError(f'{label} failed with exit {result.returncode}')
    rss = RSS_RE.search(result.stderr)
    return parse_bench(result.stdout), int(rss.group(1)) if rss else None


def stats(nanos):
    """Arithmetic mean, sample stddev, and 95% CI half-width of the pass times."""
    n = len(nanos)
    mean = sum(nanos) / n
    if n < 2:
        return {'n': n, 'mean_nanos': mean, 'stddev_nanos': None, 'ci95_nanos': None,
                'min_nanos': min(nanos), 'max_nanos': max(nanos)}
    variance = sum((x - mean) ** 2 for x in nanos) / (n - 1)
    stddev = math.sqrt(variance)
    half = t95(n) * stddev / math.sqrt(n)
    return {'n': n, 'mean_nanos': mean, 'stddev_nanos': stddev, 'ci95_nanos': half,
            'min_nanos': min(nanos), 'max_nanos': max(nanos)}


def rust_argv(oracle_fixture, repeat, cooldown):
    return [str(e2e), 'benchmark', str(oracle_fixture),
            '--repeat', str(repeat), '--cooldown-ms', str(cooldown), '--log-inv-rate', '1']


def lean_argv(oracle_fixture, xmss, repeat, cooldown, prover, out_proof):
    return [str(cli_check), 'bench', '--inputs', str(oracle_fixture),
            '--xmss', str(xmss), '--log-inv-rate', '1', '--repeat', str(repeat),
            '--cooldown-ms', str(cooldown), '--prover', prover,
            '--out-proof', str(out_proof)]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('oracle_root')
    parser.add_argument('out_dir')
    parser.add_argument('--fixtures', default='xmss4,xmss16')
    parser.add_argument('--pairs', type=int, default=5)
    parser.add_argument('--repeat', type=int, default=3)
    parser.add_argument('--cooldown-ms', type=int, default=2000)
    parser.add_argument('--impls', default=None,
                        help='comma list: rust, rust-dry, lean-stub, lean-vm '
                             '(default: rust,lean-stub,lean-vm for records<=16, else rust,lean-stub)')
    parser.add_argument('--timeout', type=int, default=7200)
    options = parser.parse_args()
    oracle = Path(options.oracle_root)
    out = Path(options.out_dir)
    out.mkdir(parents=True, exist_ok=True)
    logs = out / 'logs'
    logs.mkdir(exist_ok=True)
    report = {'tier': 'B', 'alternating_pairs': options.pairs, 'repeat': options.repeat,
              'cooldown_ms': options.cooldown_ms, 'fixtures': []}
    for fixture in options.fixtures.split(','):
        xmss = XMSS_OF[fixture]
        impls = options.impls.split(',') if options.impls else (
            ['rust', 'lean-stub', 'lean-vm'] if xmss <= 16 else ['rust', 'lean-stub'])
        # Which implementation each label maps to: `rust-dry` is the same Rust
        # binary run a second time per pair (the Rust-vs-Rust dry-run mode).
        factories = {
            'rust': lambda pair: (
                'rust-e2e', rust_argv(oracle / fixture, options.repeat, options.cooldown_ms),
                logs / f'rust-{fixture}-p{pair}.log'),
            'rust-dry': lambda pair: (
                'rust-e2e-dry', rust_argv(oracle / fixture, options.repeat, options.cooldown_ms),
                logs / f'rust-dry-{fixture}-p{pair}.log'),
            'lean-stub': lambda pair: (
                'lean-cli-stub',
                lean_argv(oracle / fixture, xmss, options.repeat, options.cooldown_ms, 'stub',
                          out / f'lean-proof-{fixture}.txt'),
                logs / f'lean-stub-{fixture}-p{pair}.log'),
            'lean-vm': lambda pair: (
                'lean-cli-vm',
                lean_argv(oracle / fixture, xmss, options.repeat, options.cooldown_ms, 'vm',
                          out / f'lean-vm-proof-{fixture}.txt'),
                logs / f'lean-vm-{fixture}-p{pair}.log'),
        }
        for name in impls:
            if name not in factories:
                raise RuntimeError(f'unknown implementation label {name!r}')
        entry = {'fixture': fixture, 'records': None, 'implementations': {}}
        # Per-impl accumulators across all alternating pairs.
        acc = {name: {'passes': [], 'warmups': [], 'rss': [], 'last': None, 'verify': None}
               for name in impls}
        for pair in range(1, options.pairs + 1):
            for name in impls:  # alternating: each impl runs once per pair, fresh process
                label, argv, log_path = factories[name](pair)
                parsed, rss = run_and_parse(label, argv, options.timeout, log_path)
                if parsed['BENCH'][0].get('records'):
                    entry['records'] = int(parsed['BENCH'][0]['records'])
                acc[name]['passes'].extend(int(p['nanos']) for p in parsed['PASS'])
                acc[name]['warmups'].append(int(parsed['WARMUP'][0]['nanos']))
                acc[name]['rss'].append(rss)
                acc[name]['last'] = parsed['LAST'][-1]
                if parsed.get('VERIFY'):
                    acc[name]['verify'] = parsed['VERIFY'][0]['status']
        for name in impls:
            data = acc[name]
            last = data['last']
            impl_report = {
                'fresh_process_runs': options.pairs,
                'pass_stats': stats(data['passes']),
                'ru_maxrss_kib': max(r for r in data['rss'] if r is not None) if data['rss'] else None,
                'ru_maxrss_kib_runs': data['rss'],
                'warmup_nanos_first': data['warmups'][0],
                'statement': last['statement'],
            }
            if last.get('proof_bytes') and last['proof_bytes'] not in ('none', 'null'):
                impl_report['ethereum_proof_wire_bytes'] = int(last['proof_bytes'])
                impl_report['proof_size'] = int(last.get('proof_size', 0))
            if data['verify'] is not None:
                impl_report['verify'] = data['verify']
            if last.get('hints_keccak256'):
                impl_report['hints_keccak256'] = last['hints_keccak256']
            if last.get('cycles') and last['cycles'] not in ('none', 'null'):
                impl_report['cycles'] = int(last['cycles'])
            entry['implementations'][name] = impl_report
        rust_verify = acc[impls[0]]['verify']
        if rust_verify is not None and rust_verify != 'ok':
            raise RuntimeError(f'{fixture}: Rust verification status {rust_verify!r}')
        statements = {impl['statement'] for impl in entry['implementations'].values()}
        if len(statements) != 1:
            raise RuntimeError(f'{fixture}: implementations disagree on the statement')
        entry['statements_match'] = True
        report['fixtures'].append(entry)
    report['status'] = 'COMPLETE'
    (out / 'tier_b_report.json').write_text(json.dumps(report, indent=2))
    lines = ['TIER_B_REPORT']
    for entry in report['fixtures']:
        for name, impl in entry['implementations'].items():
            ps = impl['pass_stats']
            lines.append(
                f"TIER_B|fixture={entry['fixture']}|impl={name}"
                f"|runs={impl['fresh_process_runs']}|passes={ps['n']}"
                f"|mean_nanos={ps['mean_nanos']:.0f}|stddev_nanos={(ps['stddev_nanos'] or 0):.0f}"
                f"|ci95_nanos={(ps['ci95_nanos'] or 0):.0f}"
                f"|ru_maxrss_kib={impl['ru_maxrss_kib']}")
    lines.append('TIER_B_STATEMENTS_MATCH|true')
    (out / 'tier_b_report.txt').write_text('\n'.join(lines) + '\n')
    print('\n'.join(lines))


try:
    main()
except Exception as error:
    print(json.dumps(dict(status='BLOCKED', blocker=str(error))))
    sys.exit(1)
