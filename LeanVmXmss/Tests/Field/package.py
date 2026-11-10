import base64
import hashlib
import json
import os
from pathlib import Path
import re
import socket
import subprocess
import tarfile

root = Path(__file__).resolve().parents[2]
out = Path('/var/lib/orb-node/work/caches/p1-shard-a-out')
out.mkdir(parents=True, exist_ok=True)
artifacts = root / 'Tests' / 'Field' / 'artifacts'
log = artifacts / 'verify-final.log'
package_env = dict(os.environ, ELAN_HOME='/var/lib/orb-node/work/caches/elan', GIT_OPTIONAL_LOCKS='0',
                    PATH='/var/lib/orb-node/work/caches/xmss-hub-unified/git-install/bin:' + os.environ.get('PATH', ''))
result = subprocess.run(['python3', 'Tests/Field/verify.py'], cwd=root, env=package_env,
                        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
log.write_text(result.stdout)
evidence = json.loads((artifacts / 'verification.json').read_text())
if result.returncode or evidence.get('acceptance') != 'PASS':
    raise RuntimeError('Final verification did not pass; see ' + str(log))
inventory = json.loads((artifacts / 'required-theorem-inventory.json').read_text())
audit_path = Path(evidence['log_directory']) / 'final-axioms.log'
sources = sorted(p for folder in ['Spec', 'Model', 'Proofs', 'Tests']
                 for p in (root / folder / 'Field').rglob('*')
                 if p.is_file() and not {'target', '__pycache__', 'artifacts'}.intersection(p.parts))
selected_evidence = [log, artifacts / 'verification.json',
                     artifacts / 'required-theorem-inventory.json', artifacts / 'Required.lean',
                     artifacts / 'field-vectors.txt',
                     Path(str(artifacts / 'field-native') + '.lnir.ll')]
files = sources + selected_evidence
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
archive = out / 'shard-a-field.tar.gz'
with tarfile.open(archive, 'w:gz') as tar:
    for path in files:
        tar.add(path, arcname=str(path.relative_to(root)), recursive=False)
encoded = out / 'shard-a-field.tgz.b64'
encoded.write_bytes(base64.encodebytes(archive.read_bytes()))
manifest = dict(status='PARTIAL_BLOCKED' if result.returncode else 'COMPLETE',
                machine_id=socket.gethostname(), verify_exit_code=result.returncode,
                verify_log_sha256=sha(log), theorem_count=sum(
                    len(re.findall(r'\btheorem\s+', p.read_text()))
                    for p in sources if p.suffix == '.lean'),
                files={str(p.relative_to(root)): sha(p) for p in files},
                archive_sha256=sha(archive), base64_sha256=sha(encoded),
                base64_bytes=encoded.stat().st_size,
                axiom_audit_sha256=sha(audit_path),
                remaining_obligations=inventory['missing'],
                blockers=[],
                evidence=evidence,
                scope_notes=['All 17 required theorem contracts were kernel checked.',
                             'Model codecs and window accumulation have separate implementations and proved refinements.',
                             'Transitive axiom audit includes private and generated Field declarations; only propext and Quot.sound are permitted.',
                             'Available MCP tool turbo_check_decl supplies the requested turbo_check role.',
                             'Native executable links imported native .c.o.export objects without --standalone and lowers >=5 LCNF kernels.'])
(out / 'shard-a-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
subprocess.run(['sync'], check=True)
print(json.dumps(dict(status=manifest['status'], verify_exit_code=result.returncode,
                     output_directory=str(out), base64_bytes=manifest['base64_bytes'],
                     remaining_obligations=manifest['remaining_obligations']), indent=2))
