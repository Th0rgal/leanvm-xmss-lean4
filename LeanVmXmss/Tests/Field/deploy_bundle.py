import base64
import hashlib
import io
import json
import re
from pathlib import Path, PurePosixPath
import sqlite3
import tarfile

db = '/var/lib/orb-node/work/41108234-5367-4582-afcf-7924f6e240c0/.local/share/opencode/opencode.db'
conn = sqlite3.connect(f'file:{db}?mode=ro', uri=True)
begin = '-----BEGIN SHARD_A_RECONSTRUCTED_SOURCES_B64-----'
end = '-----END SHARD_A_RECONSTRUCTED_SOURCES_B64-----'
texts = []
def visit(value):
    if isinstance(value, str) and begin in value and end in value:
        texts.append(value)
    elif isinstance(value, dict):
        for item in value.values():
            visit(item)
    elif isinstance(value, list):
        for item in value:
            visit(item)
for table in ('part', 'session_message', 'event'):
    for (data,) in conn.execute(f'SELECT data FROM {table}'):
        visit(json.loads(data))
for (prompt,) in conn.execute('SELECT prompt FROM session_input'):
    visit(prompt)
assert texts, 'Bundle message not found'
candidates = [text.rsplit(begin, 1)[1].split(end)[0].strip() for text in texts]
print('CANDIDATE_LENGTHS', [len(s) for s in candidates])
encoded = max((s for s in candidates if re.fullmatch('[A-Za-z0-9+/=]+', s)), key=len)
print('BASE64_LENGTH', len(encoded), 'BASE64_SHA256', hashlib.sha256((encoded + '\n').encode()).hexdigest())
decoded = base64.b64decode(encoded, validate=True)
print('ARCHIVE_LENGTH', len(decoded), 'ARCHIVE_SHA256', hashlib.sha256(decoded).hexdigest())
assert len(encoded) == 22324
assert hashlib.sha256((encoded + '\n').encode()).hexdigest() == 'b7baf380267a9c19cffb1e8092525f61a32657f9557cf82185122eac62f1c001'
raw = base64.b64decode(encoded, validate=True)
assert len(raw) == 16742
assert hashlib.sha256(raw).hexdigest() == '70bfd625f87602b963860ba9c254f1b16253c462473ef364ca7d576bc85a33f7'
root = Path(__file__).resolve().parents[2]
with tarfile.open(fileobj=io.BytesIO(raw), mode='r:gz') as archive:
    members = archive.getmembers()
    assert len(members) == 24
    for member in members:
        p = PurePosixPath(member.name)
        assert member.isfile() and not p.is_absolute() and '..' not in p.parts
        assert len(p.parts) >= 3 and p.parts[0] in ('Spec', 'Model', 'Proofs', 'Tests') and p.parts[1] == 'Field'
        assert p.suffix != '.md'
        print(member.name, member.size)
    Path('/tmp/shard-a-reconstructed-sources.tar.gz').write_bytes(raw)
    archive.extractall(root, members=members, filter='data')
print('BUNDLE_SHA256_PASS 24 files')
