import json
import os
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parents[2]
evidence = root / 'Tests/Vm/evidence'
sources = ['Spec/Field/Basic.lean', 'Model/Field/Scalar.lean',
    'Model/Vm/Kernel.lean', 'Spec/Vm/KeccakInternal.lean',
    'Spec/Xmss/Encoding.lean', 'Spec/Xmss/Hints.lean',
    'Spec/Vm/Equality.lean', 'Spec/Vm/Basic.lean',
    'Model/Vm/Interpreter.lean', 'Spec/Vm/Hints.lean', 'Model/Vm/Scheduled.lean',
    'Tests/Vm/Synthetic.lean']
flat = root / 'Tests/Vm/NativeSynthetic.lean'
flat.write_text('import Std\n' + '\n'.join('\n'.join(
    line for line in (root/name).read_text().splitlines() if not line.startswith('import '))
    for name in sources))
env = os.environ.copy()
local_cargo_home = root / 'Tests/Vm/Rust/cargo-home'
if (local_cargo_home / 'registry/index').is_dir() and (local_cargo_home / 'registry/cache').is_dir():
    env['CARGO_HOME'] = str(local_cargo_home)
cargo_cmd = ['cargo', 'build', '--release', '--manifest-path',
    'Tests/Vm/Rust/Cargo.toml', '--bin', 'vm-synthetic']
if (local_cargo_home / 'registry/index').is_dir() and (local_cargo_home / 'registry/cache').is_dir():
    cargo_cmd.insert(2, '--offline')
subprocess.run(cargo_cmd, cwd=root, env=env, check=True)
subprocess.run(['lean-native', 'build-exe', '--input', str(flat), '-o',
    str(evidence/'vm-synthetic'), '--standalone'], cwd=root, check=True)
rust = subprocess.check_output(['/var/lib/orb-node/work/caches/xmss-hub-unified/targets/rust/release/vm-synthetic'], text=True, cwd=root)
lean = subprocess.check_output([str(evidence/'vm-synthetic')], text=True, cwd=root)
(evidence/'synthetic-rust.txt').write_text(rust)
(evidence/'synthetic-lean.txt').write_text(lean)
if rust != lean:
    raise RuntimeError('synthetic Rust/Lean mismatch; inspect synthetic-{rust,lean}.txt')
report = dict(status='PASS', cases=len(rust.splitlines()), report=rust)
(evidence/'synthetic-comparison.json').write_text(json.dumps(report, indent=2))
print(json.dumps(report, indent=2))
