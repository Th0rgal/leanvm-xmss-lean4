import base64
import hashlib
import json
from pathlib import Path
import tarfile

root = Path(__file__).resolve().parents[2]
out = root.parent.parent / 'p1-shard-b-out'
out.mkdir(exist_ok=True)
files = []
for layer in ['Spec', 'Model', 'Proofs', 'Tests']:
    for area in ['Keccak', 'Merkle', 'Transcript']:
        for p in (root / layer / area).rglob('*'):
            if p.is_file() and not any(x in p.parts for x in ['target', '__pycache__']) and not p.name.startswith('shard-b-native'):
                files.append(p)
files.sort()
archive = out / 'shard-b-keccak-transcript.tar.gz'
with tarfile.open(archive, 'w:gz') as t:
    for p in files:
        t.add(p, arcname=str(p.relative_to(root)), recursive=False)
encoded = base64.b64encode(archive.read_bytes()).decode()
(out / 'shard-b-keccak-transcript.tgz.b64').write_text('\n'.join(encoded[i:i + 120] for i in range(0, len(encoded), 120)) + '\n')
manifest = dict(shard='B', machine_id='mmj78bb29g', remote_node_id='managed-mmj78bb29g',
                archive=archive.name, archive_bytes=archive.stat().st_size,
                archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest(), base64_bytes=len(encoded),
                verification=json.loads((out / 'evidence/verification.json').read_text()),
                axiom_audit=(out / 'evidence/axioms.log').read_text().strip(),
                source_sha256={str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in files if 'evidence' not in p.parts},
                contracts=dict(pow_grinding='Fuel-bounded total search; returns none on exhaustion or bits >= 64; successful search is smallest nonce',
                               merkle_build='Power-of-two nonempty leaf arrays; path verification enforces index range',
                               model='Shared scalar primitives with definitional refinement',
                               byte_transport='24-byte little-endian scalar stream; Merkle hints remain separate and unabsorbed'))
(out / 'shard-b-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps({k: v for k, v in manifest.items() if k != 'source_sha256'}, indent=2))
