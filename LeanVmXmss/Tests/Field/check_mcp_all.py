import json
import os
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parents[2]
stage = Path('/var/lib/orb-node/work/caches/p1-shard-a-out/mcp-checked-project')
if not stage.exists():
    raise RuntimeError('Missing staged MCP project: ' + str(stage))
out = root / 'Tests/Field/artifacts/mcp-all'
out.mkdir(parents=True, exist_ok=True)
env = dict(os.environ)
env.pop('LEAN_PATH', None)
env['TURBO_LEAN_TIMEOUT_MS'] = '240000'
for key, directory in [('TMPDIR', 'tmp'), ('TURBO_LEAN_HOME', 'turbo-cache'), ('XDG_CACHE_HOME', 'cache')]:
    path = out / directory
    path.mkdir(parents=True, exist_ok=True)
    env[key] = str(path)
decls = {'Extension': 'karatsuba_refines_spec', 'Associativity': 'emul_assoc',
         'Inverse': 'mul_inv_nonzero', 'ExtensionInverse': 'emul_inv_nonzero',
         'Codecs': 'encodeBytesE_decodeBytesE', 'Windows': 'scaledMul_correct',
         'NativeKernel': 'nativeMul_correct'}
results = []
for file in sorted((stage / 'Proofs/Field').glob('*.lean')):
    relative = str(file.relative_to(stage))
    for tool in ['turbo_check_decl', 'turbo_agent_step', 'turbo_audit_spec']:
        args = dict(file=relative, project_dir=str(stage))
        if tool == 'turbo_agent_step':
            args.update(compact=False, tpu=False)
            if file.stem in decls:
                args['decl'] = decls[file.stem]
        if tool == 'turbo_check_decl':
            args['compact'] = False
        try:
            result = subprocess.run(['python3', 'Tests/Field/mcp_driver.py', tool, json.dumps(args)],
                                    cwd=root, env=env, capture_output=True, text=True, timeout=300)
        except subprocess.TimeoutExpired as error:
            result = subprocess.CompletedProcess(error.cmd, 124, error.stdout or b'', error.stderr or b'')
            result.stdout = result.stdout.decode() if isinstance(result.stdout, bytes) else result.stdout
            result.stderr = result.stderr.decode() if isinstance(result.stderr, bytes) else result.stderr
        label = file.stem + '-' + tool
        (out / (label + '.json')).write_text(result.stdout)
        (out / (label + '.stderr')).write_text(result.stderr)
        verified = False
        if result.returncode == 0:
            try:
                response = json.loads(result.stdout)['response']['result']
                payload = json.loads(response['content'][0]['text'])
                verified = not response.get('isError') and payload.get('ok') is not False and payload.get('verified') is not False
                if tool == 'turbo_audit_spec':
                    verified = verified and not any(payload.get(key) for key in
                        ['vacuous_specs', 'trivial_specs', 'warnings', 'stub_defs', 'shadowed_constants', 'forbidden_scope_decls'])
            except (KeyError, ValueError, IndexError):
                verified = False
        row = dict(file=relative, tool=tool, exit_code=result.returncode, accepted=verified)
        results.append(row)
        (out / 'results.json').write_text(json.dumps(results, indent=2))
        print(json.dumps(row), flush=True)
        if not verified:
            raise SystemExit(1)
