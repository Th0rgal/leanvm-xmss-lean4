import os
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parents[2]
artifacts = root / 'Tests/Field/artifacts'
artifacts.mkdir(parents=True, exist_ok=True)
env = os.environ.copy()
env['LEAN_PATH'] = str(root / '.lake/build/lib/lean') + ':' + env.get('LEAN_PATH', '')
subprocess.run([sys.executable, str(root / 'Tests/Hub/cache_manager.py'),
                'Model.Field.NativeKernel', 'Tests.Field.Native'], cwd=root, env=env, check=True)
output = subprocess.run(['lean-native', 'build-exe', '--input', str(root / 'Tests/Field/Native.lean'),
                         '-o', str(artifacts / 'field-native'), '--dynamic-runtime'],
                        cwd=root, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True)
print(output.stdout, end='', flush=True)
