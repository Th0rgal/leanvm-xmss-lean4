#!/usr/bin/env python3
"""Isolated generated-C allocation diagnostic; never an acceptance timing gate."""
import argparse
import collections
import csv
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

p = argparse.ArgumentParser()
p.add_argument('--candidate', required=True, type=int)
p.add_argument('--evidence', required=True, type=Path)
a = p.parse_args()
e = a.evidence.resolve()
repo = Path(__file__).resolve().parents[2]
project = repo / 'LeanVmXmss'
name = f'candidate{a.candidate}'
for status in e.glob('candidate[0-9]*/status.json'):
    if not json.loads(status.read_text()).get('complete'):
        raise SystemExit(f'Acceptance benchmark active: {status}')
assert (e / (name + '-e2e')).is_file()


def run(label, command, env=None):
    with (e / (name + '-' + label + '.log')).open('w') as f:
        subprocess.run(list(map(str, command)), cwd=project, env=env,
                       stdout=f, stderr=subprocess.STDOUT, check=True)


source = e / (name + '-profile-gkr.c')
run('profile-generate', [sys.executable, repo / 'campaign/keccak-gkr/profile_generated.py',
                       project / '.lake/build/ir/Model/KeccakGkr/Flat.c', source])
source.write_text(source.read_text().replace('CAMPAIGN_ALLOC_OUT', 'CAMPAIGN_GKR_OUT'))
run('profile-compile', ['clang', '-O3', '-DNDEBUG', '-march=native',
                      '-I/opt/orb/elan/toolchains/leanprover--lean4---v4.35.0/include',
                      '-c', source, '-o', source.with_suffix('.o')])
link = json.loads((e / 'candidate1-profile-link.json').read_text())
link = [s.replace('candidate1-e2e', name + '-e2e')
         .replace('candidate1-profile-gkr.o', name + '-profile-gkr.o') for s in link]
link[-1] = str(e / (name + '-profile-e2e'))
(e / (name + '-profile-link.json')).write_text(json.dumps(link, indent=2))
run('profile-link', link)
env = dict(os.environ, LEAN_NUM_THREADS='1',
           CAMPAIGN_GKR_OUT=str(e / (name + '-profile-xmss4-gkr.csv')),
           CAMPAIGN_BUS_OUT=str(e / (name + '-profile-xmss4-bus.csv')))
proof = e / (name + '-profile-xmss4.ethproof')
run('profile-xmss4', [e / (name + '-profile-e2e'), '--prover', 'e2e', '--xmss', '4',
                    '--inputs', e / 'oracle/xmss4', '--out-proof', proof,
                    '--repeat', '0', '--cooldown-ms', '0', '--log-inv-rate', '1'], env)
assert proof.read_bytes() == (e / 'baseline/xmss4-pair1.ethproof').read_bytes()
run('profile-xmss4-verify', [e / 'rust-native-target/release/e2e-oracle', 'verify-eth',
                          e / 'oracle/xmss4/xmss-inputs.bin', proof, '4', '1'])
sites = json.loads(source.with_suffix('.sites.json').read_text())
totals = collections.defaultdict(lambda: [0, 0])
with (e / (name + '-profile-xmss4-gkr.csv')).open() as f:
    for _, index, calls, size in csv.reader(f):
        site = sites[int(index)]
        key = (site['function'], site['kind'])
        totals[key][0] += int(calls)
        totals[key][1] += int(size)
rows = [dict(function=k[0], kind=k[1], calls=v[0], bytes_or_nanos=v[1])
        for k, v in totals.items()]
report = dict(diagnostic_only=True, proof_matches_baseline=True,
              independently_verified=True,
              proof_sha256=hashlib.sha256(proof.read_bytes()).hexdigest(), rows=rows)
(e / (name + '-profile-xmss4-summary.json')).write_text(json.dumps(report, indent=2))
print(json.dumps([r for r in rows if 'product' in r['function'].lower()
                  and r['kind'] == 'lean_alloc_ctor'], indent=2))
