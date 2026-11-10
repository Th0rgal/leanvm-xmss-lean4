import base64
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import tarfile

root = Path(__file__).resolve().parents[2]
out = Path('/var/lib/orb-node/work/caches/p1-shard-c-out')
stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
checks = {}
for label, args in [
    ('build', ['turbo-lean', '--json', 'build', '--project-dir', '.', 'Tests.Vm.Witnesses', 'Tests.Vm.Synthetic']),
    ('runtime-audit', ['turbo-lean', '--json', 'audit-spec', 'Proofs/Vm/RuntimePowers.lean']),
    ('basic-audit', ['turbo-lean', '--json', 'audit-spec', 'Proofs/Vm/Basic.lean']),
    ('native-build', ['python3', 'Tests/Vm/build_native.py', '--vm-only'])]:
    result = subprocess.run(args, cwd=root, capture_output=True, text=True, timeout=120)
    checks[label] = dict(argv=args, exit_code=result.returncode, output=result.stdout+result.stderr)
report = root/'Tests/Vm/evidence/w11-checks.json'
report.write_text(json.dumps(checks, indent=2))
names = ['Spec/Vm/Basic.lean', 'Model/Vm/Interpreter.lean', 'Model/Vm/Kernel.lean',
    'Proofs/Vm/Basic.lean', 'Proofs/Vm/RuntimePowers.lean', 'Tests/Vm/Witnesses.lean',
    'Tests/Vm/build_native.py', 'Tests/Vm/verify.py', 'Tests/Vm/Profile.lean',
    'Tests/Vm/Synthetic.lean', 'Tests/Vm/synthetic.py', 'Tests/Vm/Rust/Cargo.toml',
    'Tests/Vm/Rust/src/synthetic.rs', 'Tests/Vm/package_w11.py',
    'Tests/Vm/evidence/w11-checks.json', 'Tests/Vm/evidence/verification.json',
    'Tests/Vm/evidence/axiom-audit.log', 'Tests/Vm/evidence/synthetic-comparison.json']
archive = out/f'shard-c-w11-{stamp}.tar.gz'
with tarfile.open(archive, 'w:gz', compresslevel=9) as tar:
    for name in names:
        tar.add(root/name, arcname=name)
raw = archive.read_bytes()
encoded = base64.b64encode(raw).decode()
b64 = out/f'shard-c-w11-{stamp}.tgz.b64'
b64.write_text('\n'.join(encoded[i:i+120] for i in range(0,len(encoded),120))+'\n')
manifest = dict(status='BLOCKED_PARTIAL', created_at_utc=stamp,
    kind='W11 delta; apply after W10 and followup7', archive=str(archive), base64=str(b64),
    archive_bytes=len(raw), archive_sha256=hashlib.sha256(raw).hexdigest(),
    files={name:hashlib.sha256((root/name).read_bytes()).hexdigest() for name in names},
    checks={name:result['exit_code'] for name,result in checks.items()},
    completed=['PowersValid initial, all steps, all hints, witness loads, and scheduled runner; 16 strict specs pass',
        'Independent Model setStep with non-rfl refinement; explicit XOR kernel equivalence',
        'Integrated vm-full lowering 1 LCNF declaration; no performance claim',
        '10 exact frozen Rust/Lean native synthetic differentials PASS'],
    pending=['multiplicative GPow homomorphism', 'more independent Model opcode/XMSS hint implementations',
        'authenticated Field delivery, strict global audit and complete verify exit0'],
    field_source_sha256=hashlib.sha256((root/'Spec/Field/Basic.lean').read_bytes()).hexdigest(),
    expected_field_sha256_from_A='d49923be4522321de1e1c7cbd2e65d31ee0480a5442abd60fd7546b96b1b4f3c',
    verification=json.loads((root/'Tests/Vm/evidence/verification.json').read_text())['blocker'])
path = out/f'shard-c-w11-{stamp}.json'
path.write_text(json.dumps(manifest, indent=2)+'\n')
with tarfile.open(archive) as tar:
    assert all(hashlib.sha256(tar.extractfile(n).read()).hexdigest()==h for n,h in manifest['files'].items())
assert base64.b64decode(b64.read_text())==raw
subprocess.run(['sync'], check=True)
print(json.dumps(dict(manifest=str(path), base64=str(b64), sha256=manifest['archive_sha256'],
    bytes=len(raw), base64_lines=len(b64.read_text().splitlines()), checks=manifest['checks']), indent=2))
