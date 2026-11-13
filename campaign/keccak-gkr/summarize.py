#!/usr/bin/env python3
"""Summarize completed matched pairs; never count an unfinished process as data."""
import argparse
import json
from pathlib import Path
import re
import statistics

p = argparse.ArgumentParser()
p.add_argument('directory', type=Path)
a = p.parse_args()
s = json.loads((a.directory / 'status.json').read_text())
groups = {}
for command in s['commands']:
    m = re.fullmatch(r'xmss(\d+)-pair(\d+)-(rust|lean)', command['label'])
    if not m or command.get('exit_code') != 0:
        continue
    n, pair, implementation = int(m[1]), int(m[2]), m[3]
    text = Path(command['log']).read_text()
    passes = [int(t) for t in re.findall(r'^PASS\|i=\d+\|nanos=(\d+)$', text, re.M)]
    if not passes:
        raise SystemExit('Missing recomputation samples: ' + command['label'])
    rss = re.search(r'Maximum resident set size \(kbytes\): (\d+)', text)
    row = dict(passes_nanos=passes, mean_nanos=statistics.mean(passes),
               peak_rss_bytes=int(rss[1]) * 1024 if rss else None)
    if implementation == 'lean':
        phases = a.directory / f'xmss{n}-pair{pair}-phases.json'
        row['phase_means_nanos'] = json.loads(phases.read_text())['mean']['phases_nanos']
    groups.setdefault(n, {}).setdefault(pair, {})[implementation] = row

result = dict(complete=s['complete'], paired={})
for n, pairs in groups.items():
    full = {pair: row for pair, row in pairs.items() if set(row) == {'rust', 'lean'}}
    if not full:
        continue
    lean = statistics.mean(row['lean']['mean_nanos'] for row in full.values()) / 1e9
    rust = statistics.mean(row['rust']['mean_nanos'] for row in full.values()) / 1e9
    rss = max(row['lean']['peak_rss_bytes'] for row in full.values())
    ratios = [row['lean']['mean_nanos'] / row['rust']['mean_nanos'] for row in full.values()]
    item = dict(pair_count=len(full), lean_mean_seconds=lean, rust_mean_seconds=rust,
                lean_peak_rss_bytes=rss, lean_over_rust_time_ratio=lean / rust,
                mean_pair_time_ratio=statistics.mean(ratios), pairs=full)
    if len(ratios) >= 5:
        # A conservative t critical value for >=5 independent pair means.
        item['pair_ratio_ci95_halfwidth'] = 2.776 * statistics.stdev(ratios) / len(ratios)**0.5
    if n == 1400:
        item['target_gaps'] = [dict(target_seconds=t, target_gib=g,
                                    time_ratio=lean/t,
                                    excess_seconds=lean-t,
                                    excess_rss_bytes=rss-g*2**30)
                              for t, g in [(1.15, 8.633), (3.0, 4.0), (0.920, 5.5)]]
    result['paired'][n] = item
print(json.dumps(result, indent=2))
