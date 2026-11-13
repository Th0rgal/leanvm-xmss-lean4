#!/usr/bin/env python3
"""Sequential fresh-process Rust/Lean runs; each Lean proof independently verified.

No result or proof is reused as a proving input. Diagnostic builds must use a
different output directory and must never be described as acceptance timings.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time

p = argparse.ArgumentParser()
p.add_argument('--lean', required=True, type=Path)
p.add_argument('--rust', required=True, type=Path)
p.add_argument('--oracle', required=True, type=Path)
p.add_argument('--out', required=True, type=Path)
p.add_argument('--sizes', default='4,16,1400')
p.add_argument('--pairs', default=1, type=int)
p.add_argument('--repeat', default=3, type=int)
p.add_argument('--final', action='store_true')
p.add_argument('--reference-proof-dir', type=Path)
a = p.parse_args()
if a.final and (a.pairs < 5 or a.repeat < 3):
    p.error('Final acceptance requires at least five pairs and repeat three')
a.out.mkdir(parents=True, exist_ok=True)
status = dict(started=time.time(), complete=False, commands=[],
              binary_sha256={str(b): hashlib.sha256(b.read_bytes()).hexdigest()
                             for b in [a.lean, a.rust]})


def run(label, command, timed=False):
    log = a.out / (label + '.log')
    argv = ['/usr/bin/time', '-v', *map(str, command)] if timed else list(map(str, command))
    entry = dict(label=label, argv=argv, started=time.time(), log=str(log))
    status['commands'].append(entry)
    (a.out / 'status.json').write_text(json.dumps(status, indent=2) + '\n')
    with log.open('w') as f:
        result = subprocess.run(argv, stdout=f, stderr=subprocess.STDOUT)
    entry.update(exit_code=result.returncode, finished=time.time())
    (a.out / 'status.json').write_text(json.dumps(status, indent=2) + '\n')
    if result.returncode:
        raise SystemExit(f'{label} failed: {log}')


for n in map(int, a.sizes.split(',')):
    fixture = a.oracle / f'xmss{n}'
    for pair in range(1, a.pairs + 1):
        label = f'xmss{n}-pair{pair}'
        # Rust then Lean consistently, with no concurrent workload.
        run(label + '-rust', [a.rust, 'benchmark', fixture, '--repeat', a.repeat,
                             '--cooldown-ms', 2000, '--log-inv-rate', 1], True)
        proof = a.out / (label + '.ethproof')
        run(label + '-lean', [a.lean, '--prover', 'e2e', '--xmss', n,
                             '--inputs', fixture, '--out-proof', proof,
                             '--repeat', a.repeat, '--cooldown-ms', 2000,
                             '--log-inv-rate', 1, '--phase-timings',
                             a.out / (label + '-phases.json')], True)
        run(label + '-verify', [a.rust, 'verify-eth', fixture / 'xmss-inputs.bin',
                               proof, n, 1], True)
        if a.reference_proof_dir:
            reference = a.reference_proof_dir / f'xmss{n}-pair1.ethproof'
            if proof.read_bytes() != reference.read_bytes():
                raise SystemExit(f'Proof bytes differ: {proof} versus {reference}')
        status.setdefault('proofs', {})[str(proof)] = dict(
            bytes=proof.stat().st_size,
            sha256=hashlib.sha256(proof.read_bytes()).hexdigest())
status.update(complete=True, finished=time.time())
(a.out / 'status.json').write_text(json.dumps(status, indent=2) + '\n')
