#!/usr/bin/env python3
"""Aggregate diagnostic counters; these are never acceptance wall timings."""
import argparse
import collections
import csv
import json
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument('--evidence', required=True, type=Path)
p.add_argument('--candidate', required=True, type=int)
p.add_argument('--size', default=1400, type=int)
a = p.parse_args()
e = a.evidence
name = f'candidate{a.candidate}'
if a.size == 1400:
    state = json.loads((e / (name + '-full-profile-status.json')).read_text())
    if not state['complete']:
        raise SystemExit('Full diagnostic has not completed and verified')
for module, site_file in [('gkr', name + '-profile-gkr.sites.json'),
                          ('bus', 'candidate1-profile-bus.sites.json')]:
    sites = json.loads((e / site_file).read_text())
    totals = collections.defaultdict(lambda: [0, 0])
    with (e / f'{name}-profile-xmss{a.size}-{module}.csv').open() as f:
        for _, index, calls, value in csv.reader(f):
            site = sites[int(index)]
            row = totals[(site['function'], site['kind'])]
            row[0] += int(calls)
            row[1] += int(value)
    report = dict(diagnostic_only=True, size=a.size, module=module,
        caveats=['Timers are nested aggregate thread CPU, not wall time.',
                 'Each timer excludes CPU spent by spawned child threads.',
                 'Constructor bytes include headers, exclude allocator rounding.',
                 'ByteArray bytes are potential shared-input COW payload.',
                 'Generated-C instrumentation may change native inlining.',
                 'Only instrumented sites are counted.'],
        rows=[dict(function=k[0], kind=k[1], calls=v[0], bytes_or_nanos=v[1])
              for k, v in sorted(totals.items())])
    out = e / f'{name}-profile-xmss{a.size}-{module}-summary.json'
    out.write_text(json.dumps(report, indent=2) + '\n')
    print(out)
