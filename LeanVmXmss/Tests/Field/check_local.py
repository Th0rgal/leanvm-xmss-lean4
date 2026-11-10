import os
from pathlib import Path
import subprocess
import sys
import time

root = Path(__file__).resolve().parents[2]
lib = root / '.lake/build/lib/lean'
env = dict(os.environ)
env['LEAN_PATH'] = str(lib) + ':' + env.get('LEAN_PATH', '')
for name in sys.argv[1:]:
    path = Path(name)
    output = lib / path.with_suffix('.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    result = subprocess.run(['lean', '-o', str(output), name], cwd=root, env=env, capture_output=True, text=True, timeout=180)
    print(name, 'seconds', time.monotonic() - start, 'exit', result.returncode, flush=True)
    print(result.stdout + result.stderr, flush=True)
    if result.returncode:
        sys.exit(result.returncode)
