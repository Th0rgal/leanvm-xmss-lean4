import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

root = Path(__file__).resolve().parents[2]
stage = Path('/var/lib/orb-node/work/caches/p1-shard-a-out/mcp-checked-project')
if not stage.exists():
    raise RuntimeError('Missing staged MCP project: ' + str(stage))
env = dict(os.environ)
env.pop('LEAN_PATH', None)
env['TURBO_LEAN_TIMEOUT_MS'] = '240000'
for key, directory in [('TMPDIR', 'tmp'), ('TURBO_LEAN_HOME', 'turbo-cache'),
                       ('XDG_CACHE_HOME', 'cache'), ('CARGO_TARGET_DIR', 'cargo'),
                       ('TURBO_P0_EVIDENCE_DIR', 'evidence')]:
    path = stage / directory
    path.mkdir(parents=True, exist_ok=True)
    env[key] = str(path)
module = sys.argv[1] if len(sys.argv) > 1 else 'Codecs'
decls = {'Codecs': 'encodeBytesE_decodeBytesE', 'Extension': 'karatsuba_refines_spec',
         'Associativity': 'emul_assoc', 'Inverse': 'mul_inv_nonzero',
         'ExtensionInverse': 'emul_inv_nonzero', 'Windows': 'scaledMul_correct',
         'NativeKernel': 'nativeMul_correct'}
for tool in ['turbo_check_decl', 'turbo_agent_step', 'turbo_audit_spec']:
    args = dict(file='Proofs/Field/' + module + '.lean', project_dir=str(stage), compact=False)
    if tool != 'turbo_audit_spec':
        args['decl'] = decls[module]
    if tool == 'turbo_agent_step':
        args['tpu'] = False
    result = subprocess.run(['python3', str(root / 'Tests/Field/mcp_driver.py'),
                             tool, json.dumps(args)], cwd=stage, env=env,
                            capture_output=True, text=True, timeout=300)
    (stage / (module + '-' + tool + '.json')).write_text(result.stdout)
    (stage / (module + '-' + tool + '.stderr')).write_text(result.stderr)
    result.check_returncode()
    response = json.loads(result.stdout)['response']['result']
    payload = json.loads(response['content'][0]['text'])
    print(json.dumps(dict(module=module, tool=tool, payload=payload)), flush=True)
    if response.get('isError') or payload.get('ok') is False or payload.get('verified') is False:
        raise SystemExit(1)
