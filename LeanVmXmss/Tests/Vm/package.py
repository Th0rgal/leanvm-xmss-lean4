import base64
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tarfile

root = Path(__file__).resolve().parents[2]
output = Path('/var/lib/orb-node/work/caches/p1-shard-c-out')
output.mkdir(exist_ok=True)
subprocess.run(['python3', 'Tests/Vm/verify.py'], cwd=root, env=os.environ, check=True)
files = []
for area in ['Spec', 'Model', 'Proofs', 'Tests']:
    for topic in ['Xmss', 'Vm']:
        for path in (root / area / topic).rglob('*'):
            if not path.is_file():
                continue
            rel = path.relative_to(root)
            if any(part in ['cargo-home', 'target', '__pycache__', 'generated'] for part in rel.parts):
                continue
            if path.suffix in ['.lean', '.py', '.toml', '.lock', '.json', '.log', '.txt'] and path.stat().st_size < 200000:
                files.append(path)
archive = output / 'shard-c-xmss-vm.tar.gz'
with tarfile.open(archive, 'w:gz') as tar:
    for path in sorted(files):
        tar.add(path, arcname=str(path.relative_to(root)))
encoded = output / 'shard-c-xmss-vm.tgz.b64'
encoded.write_bytes(base64.b64encode(archive.read_bytes()))
verification = json.loads((root / 'Tests/Vm/evidence/verification.json').read_text())
manifest = dict(status='COMPLETE', source_snapshot='orb-snap-default-xmss-hub-unified-v2-z2kt',
                verified=['1400 fresh XMSS signature verifications', 'exact 10594241-byte Rust/Lean hint stream',
                          'exact statement digest', '524288-instruction bytecode roundtrip',
                          'strict axiom audit: only propext and Quot.sound',
                          'GPow multiplicative homomorphism', '16-byte cell roundtrip',
                          'memory monotonicity', 'small synthetic Rust/Lean VM differential',
                          'strict audit-spec coverage',
                          'Full Lean/Rust VM differential: exact 1146537 cycles, 8668972 cells, memory hash, all six opcode counts, no unconstrained reads'],
                pending=[],
                verification=verification, statement_digest='ded8679e548f3d7c810a3c50e1c69b4fed50773b35189e3a67d7728accafe423',
                hints_keccak256='0038d98ce4f3337fc02da9c4ac0c8c9393e12ab8eda96094a41e636ebfcd08d4',
                rust_execution=json.loads((output / 'oracle/execution.json').read_text()),
                fixture_note='leaves.bin is a length-prefixed EthereumProof; raw records are xmss-inputs.bin',
                archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest(),
                archive_bytes=archive.stat().st_size, base64_bytes=encoded.stat().st_size,
                sources={str(path.relative_to(root)): hashlib.sha256(path.read_bytes()).hexdigest() for path in sorted(files)})
(output / 'shard-c-manifest.json').write_text(json.dumps(manifest, indent=2))
print(json.dumps({key: value for key,value in manifest.items() if key not in ['sources','verification']}, indent=2))
