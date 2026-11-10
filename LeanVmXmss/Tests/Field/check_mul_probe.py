import json
from pathlib import Path
import subprocess

from vectors import generate

root = Path(__file__).resolve().parents[2]
binary = root / 'Tests/Field/artifacts/mul-probe'
mask = (1 << 64) - 1

def reference(a, b):
    product = 0
    for i in range(64):
        if (b >> i) & 1:
            product ^= a << i
    modulus = (1 << 64) | 0x1B
    for i in range(127, 63, -1):
        if (product >> i) & 1:
            product ^= modulus << (i - 64)
    return product & mask

rows = generate()
for index, row in enumerate(rows):
    a, b = row[0], row[3]
    result = subprocess.run([str(binary), str(a), str(b)], capture_output=True, text=True, check=True, timeout=10)
    assert int(result.stdout) == reference(a, b), (index, row, result.stdout)
report = dict(status='PASS', vectors=len(rows), scope='Isolated LNIR multiplication versus polynomial long division; excludes square/inverse/extension gates')
(root / 'Tests/Field/artifacts/mul-probe-vectors.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
