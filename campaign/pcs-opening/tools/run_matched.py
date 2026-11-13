"""Fresh-process paired campaigns; all failures are retained and stop the run."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

p = argparse.ArgumentParser()
p.add_argument('--lean', required=True, type=Path)
p.add_argument('--rust', required=True, type=Path)
p.add_argument('--fixtures', required=True, type=Path)
p.add_argument('--out', required=True, type=Path)
p.add_argument('--counts', default='4,16,1400')
p.add_argument('--pairs', default=1, type=int)
a = p.parse_args()
a.out.mkdir(parents=True, exist_ok=True)
cg = Path('/sys/fs/cgroup' + Path('/proc/self/cgroup').read_text().split('::')[1].strip())
receipt = dict(status='RUNNING', pid=os.getpid(), start=time.time(), records=[],
               acceptance=dict(seconds_strict_lt=1, rss_bytes_strict_lt=4294967296),
               binaries={str(b): hashlib.sha256(b.read_bytes()).hexdigest() for b in (a.lean, a.rust)})

def save():
    temp = a.out / 'receipt.json.tmp'
    temp.write_text(json.dumps(receipt, indent=2) + '\n')
    temp.replace(a.out / 'receipt.json')

def mem():
    return {n: (cg / n).read_text() for n in ('memory.max', 'memory.high', 'memory.events')}

def run(label, args, expect_signers=None):
    row = dict(label=label, argv=list(map(str, args)), start=time.time(), cgroup_before=mem())
    receipt['records'].append(row)
    save()
    print('START', label, flush=True)
    log = a.out / (label + '.log')
    rss = a.out / (label + '.time')
    with log.open('w') as f:
        child = subprocess.Popen(['/usr/bin/time', '-v', '-o', str(rss), *map(str, args)], stdout=f, stderr=subprocess.STDOUT)
        row['pid'] = child.pid
        save()
        row['exit_code'] = child.wait()
    row['wall_seconds'] = time.time() - row['start']
    row['cgroup_after'] = mem()
    text = log.read_text()
    row['passes_nanos'] = [int(x) for x in re.findall(r'^PASS\|i=\d+\|nanos=(\d+)', text, re.M)]
    warm = re.findall(r'^WARMUP\|nanos=(\d+)', text, re.M)
    row['warmup_nanos'] = int(warm[0]) if warm else None
    peak = re.search(r'Maximum resident set size \(kbytes\): (\d+)', rss.read_text())
    row['peak_rss_bytes'] = int(peak[1]) * 1024 if peak else None
    if row['passes_nanos']:
        row['mean_seconds'] = sum(row['passes_nanos']) / len(row['passes_nanos']) / 1e9
        row['time_gate'] = all(ns < 1_000_000_000 for ns in row['passes_nanos'])
        row['mean_time_gate'] = row['mean_seconds'] < 1
        row['min_seconds'] = min(row['passes_nanos']) / 1e9
        row['max_seconds'] = max(row['passes_nanos']) / 1e9
        row['memory_gate'] = row['peak_rss_bytes'] is not None and row['peak_rss_bytes'] < 4294967296
    if 'verify' in label:
        row['verification_passes'] = len(re.findall(r'VERIFY_ETH\|PASS', text))
        row['signers_match'] = f'|signers={expect_signers}\n' in text
    for n in ['proof_size', 'proof_bytes', 'wire_bytes']:
        vals = re.findall(r'\|' + n + r'=(\d+)', text)
        if vals: row[n] = int(vals[-1])
    save()
    if row['exit_code'] != 0:
        raise RuntimeError(f'{label} exit {row["exit_code"]}')
    before = dict(x.split() for x in row['cgroup_before']['memory.events'].splitlines())
    after = dict(x.split() for x in row['cgroup_after']['memory.events'].splitlines())
    if any(int(after[k]) > int(before[k]) for k in ['high', 'max', 'oom', 'oom_kill']):
        raise RuntimeError(f'{label} cgroup throttle/OOM events; measurement invalid')
    if 'verify' in label and (row['verification_passes'] != 3 or not row['signers_match']):
        raise RuntimeError(f'{label} independent verification/count failed')
    if 'bench' in label and (len(row['passes_nanos']) != 3 or row['warmup_nanos'] is None):
        raise RuntimeError(f'{label} incomplete warmup/repeat3')
    print('DONE', label, 'wall', round(row['wall_seconds'], 3), flush=True)

try:
    save()
    for pair in range(a.pairs):
        for n in map(int, a.counts.split(',')):
            fixture = a.fixtures / f'xmss{n}'
            assert (fixture / 'xmss-inputs.bin').stat().st_size == n * 2468
            base = f'p{pair}-xmss{n}'
            run(base + '-rust-bench', [a.rust, 'benchmark', fixture, '--repeat', '3', '--cooldown-ms', '2000', '--log-inv-rate', '1'])
            proof = a.out / (base + '-lean.ethproof')
            assert not proof.exists(), 'fresh proof path required'
            run(base + '-lean-bench', [a.lean, '--xmss', n, '--inputs', fixture, '--prover', 'e2e', '--repeat', 3,
                '--cooldown-ms', 2000, '--log-inv-rate', 1, '--phase-timings', a.out / (base + '-phases.json'), '--out-proof', proof])
            receipt.setdefault('proofs', []).append(dict(path=str(proof), bytes=proof.stat().st_size,
                sha256=hashlib.sha256(proof.read_bytes()).hexdigest()))
            run(base + '-verify', [a.rust, 'verify-eth', fixture / 'xmss-inputs.bin', proof, n, 1], expect_signers=n)
    receipt['status'] = 'COMPLETE'
except BaseException as e:
    receipt['status'] = 'FAILED_OR_INCOMPLETE'
    receipt['error'] = str(e)
    raise
finally:
    receipt['finish'] = time.time()
    save()
