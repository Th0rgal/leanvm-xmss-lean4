#!/usr/bin/env python3
"""Run the repository's unchanged symbol and ISA audit on saved native binaries."""
import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
p = argparse.ArgumentParser()
p.add_argument('--evidence', required=True, type=Path)
p.add_argument('--labels', required=True)
p.add_argument('--out', required=True, type=Path)
a = p.parse_args()
repo = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location(
    'campaign_gate', repo / 'LeanVmXmss/Tests/Audit/maxwell_gate_check.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
report = m.check_native_binaries([a.evidence / (s + '-e2e') for s in a.labels.split(',')])
reference = repo / 'references/leanVM'
report['rust_commit'] = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=reference, text=True).strip()
report['rust_dirty'] = subprocess.check_output(['git', 'status', '--porcelain'], cwd=reference, text=True)
report['rust_clean_frozen'] = (not report['rust_dirty'] and
    report['rust_commit'] == '59c2984df79cc9ff1914e547c5d5d390fffc8f3e')
a.out.write_text(json.dumps(report, indent=2))
print(json.dumps(report, indent=2))
if not report['ok'] or not report['rust_clean_frozen']:
    raise SystemExit(1)
