from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

from vectors import generate

root = Path(__file__).resolve().parents[2]
artifacts = root / 'Tests' / 'Field' / 'artifacts'
logs = artifacts / 'logs' / ('verification-' + datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'))
logs.mkdir(parents=True, exist_ok=True)
env = dict(os.environ, ELAN_HOME='/var/lib/orb-node/work/caches/elan', GIT_OPTIONAL_LOCKS='0')
env['TURBO_LEAN_TIMEOUT_MS'] = '240000'
env['TURBO_LEAN_HOME'] = str(root.parent / 'turbo-cache')
for key, folder in [('TMPDIR', 'tmp'), ('XDG_CACHE_HOME', 'cache'),
                    ('CARGO_TARGET_DIR', 'rust-target'),
                    ('TURBO_P0_EVIDENCE_DIR', 'native-evidence')]:
    destination = artifacts / folder
    destination.mkdir(parents=True, exist_ok=True)
    env[key] = str(destination)

required_theorems = {
    'mul_assoc': 'K multiplicative associativity',
    'emul_assoc': 'E multiplicative associativity',
    'mul_one_left': 'K left multiplicative identity',
    'emul_one_left': 'E left multiplicative identity',
    'emul_comm': 'E multiplicative commutativity',
    'emul_add_right': 'E distributivity',
    'mul_inv_nonzero': 'K nonzero inverse law',
    'emul_inv_nonzero': 'E nonzero inverse law',
    'decodeBytesK_encodeBytesK': '8-byte element roundtrip',
    'decodeBytesE_encodeBytesE': '24-byte element roundtrip',
    'encodeBytesK_decodeBytesK': '8-byte canonical image roundtrip',
    'encodeBytesE_decodeBytesE': '24-byte canonical image roundtrip',
    'frobenius_eq_pow': 'Frobenius equals exponent 2^64',
    'frobenius2_eq_pow': 'second Frobenius equals exponent 2^128',
    'norm_in_base': 'extension norm has zero nonconstant limbs',
    'inv_eq_pow': 'Itoh-Tsujii inverse equals exponent 2^64 - 2',
    'scaledMul_correct': '6-bit window table multiplication correctness',
}

required_contracts = {
    'mul_assoc': '(a b c : K) : M.mul (M.mul a b) c = M.mul a (M.mul b c)',
    'emul_assoc': '(a b c : E) : M.karatsubaMul (M.karatsubaMul a b) c = M.karatsubaMul a (M.karatsubaMul b c)',
    'mul_one_left': '(a : K) : M.mul 1 a = a',
    'emul_one_left': '(a : E) : M.karatsubaMul S.one a = a',
    'emul_comm': '(a b : E) : M.karatsubaMul a b = M.karatsubaMul b a',
    'emul_add_right': '(a b c : E) : M.karatsubaMul a (M.eadd b c) = M.eadd (M.karatsubaMul a b) (M.karatsubaMul a c)',
    'mul_inv_nonzero': '(a : K) (h : a ≠ 0) : M.mul a (M.inv a) = 1',
    'emul_inv_nonzero': '(a : E) (h : a ≠ S.zero) : M.karatsubaMul a (M.einv a) = S.one',
    'decodeBytesK_encodeBytesK': '(a : K) : M.decodeBytesK? (M.encodeBytesK a) = some a',
    'decodeBytesE_encodeBytesE': '(a : E) : M.decodeBytesE? (M.encodeBytesE a) = some a',
    'encodeBytesK_decodeBytesK': '(b : ByteArray) (a : K) (h : M.decodeBytesK? b = some a) : M.encodeBytesK a = b',
    'encodeBytesE_decodeBytesE': '(b : ByteArray) (a : E) (h : M.decodeBytesE? b = some a) : M.encodeBytesE a = b',
    'frobenius_eq_pow': '(a : E) : M.frobenius a = M.epow a (2^64)',
    'frobenius2_eq_pow': '(a : E) : M.frobenius2 a = M.epow a (2^128)',
    'norm_in_base': '(a : E) : M.karatsubaMul a (M.karatsubaMul (M.frobenius a) (M.frobenius2 a)) = S.embed (M.norm a)',
    'inv_eq_pow': '(a : K) : M.inv a = M.pow a (2^64 - 2)',
    'scaledMul_correct': '(a b : E) : M.scaledMul (M.scaled a) b = M.karatsubaMul a b',
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(label, argv, cwd=root, stdin=None, env_override=None):
    logfile = logs / (label + '.log')
    started = datetime.now(timezone.utc).isoformat()
    start = time.monotonic()
    run_env = env_override if env_override is not None else env
    result = subprocess.run(argv, cwd=cwd, env=run_env, input=stdin, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    logfile.write_text(result.stdout)
    receipt = dict(label=label, argv=argv, cwd=str(cwd), started=started,
                   elapsed_seconds=time.monotonic() - start, exit_code=result.returncode,
                   log=str(logfile), log_sha256=sha(logfile))
    with (artifacts / 'commands.jsonl').open('a') as handle:
        handle.write(json.dumps(receipt) + '\n')
    if result.returncode or re.search(r'(^Error:|: error[:(]|"isError": true)', result.stdout, re.M):
        raise RuntimeError(json.dumps(receipt))
    return result.stdout


def main():
    source_files = sorted(p for folder in ['Spec', 'Model', 'Proofs', 'Tests'] for p in (root / folder / 'Field').rglob('*') if p.is_file() and 'artifacts' not in p.parts and 'target' not in p.parts and '__pycache__' not in p.parts)
    before = {str(p.relative_to(root)): sha(p) for p in source_files}
    lean_files = [p for p in source_files if p.suffix == '.lean']
    proofs = '\n'.join(p.read_text() for p in lean_files if p.relative_to(root).parts[0] == 'Proofs')
    missing = {name: obligation for name, obligation in required_theorems.items()
               if not re.search(r'\btheorem\s+' + re.escape(name) + r'\b', proofs)}
    inventory = dict(acceptance='PARTIAL' if missing else 'PENDING_KERNEL_CHECK',
                     required=required_theorems, missing=missing)
    (artifacts / 'required-theorem-inventory.json').write_text(json.dumps(inventory, indent=2))
    for p in lean_files:
        if re.search(r'\b(sorry|admit|native_decide|bv_decide|axiom)\b', p.read_text()):
            raise RuntimeError('Forbidden token: ' + str(p))
        if '--' in p.read_text() or '/-' in p.read_text():
            raise RuntimeError('Comment in source: ' + str(p))
    run('final-build', ['turbo-lean', '--json', 'build', '--project-dir', '.',
                        'Proofs.Field.Windows', 'Proofs.Field.NativeKernel',
                        'Tests.Field.Witnesses', 'Tests.Field.ToolProbe', 'Tests.Field.Native', 'Tests.Field.NativeRefinement'])
    contract_source = artifacts / 'Required.lean'
    declarations = ['import Proofs.Field.Windows', 'open LeanVmXmss.Spec.Field (K E)']
    for name, signature in required_contracts.items():
        if name in missing:
            continue
        signature = signature.replace('M.', 'LeanVmXmss.Model.Field.').replace('S.', 'LeanVmXmss.Spec.Field.')
        declarations.append('theorem required_' + name + ' ' + signature +
                            ' := by exact LeanVmXmss.Proofs.Field.' + name + ' ' +
                            ' '.join(re.findall(r'\(([a-z ]+)\s*:', signature)))
    contract_source.write_text('\n'.join(declarations) + '\n')
    run('required-theorem-contracts', ['turbo-lean', '--json', 'check', str(contract_source), '--project-dir', '.'])
    for p in lean_files:
        if p.stem in ['AxiomAudit', 'InstanceAudit', 'Differential', 'StructuralAudit', 'CompilerInventory', 'NativeDependencies']:
            continue
        name = p.relative_to(root).as_posix()
        label = name.removesuffix('.lean').replace('/', '-').lower()
        run('final-check-' + label, ['turbo-lean', '--json', 'check', name, '--project-dir', '.'])
        audit = json.loads(run('final-audit-' + label, ['turbo-lean', '--json', 'audit-spec', name]))
        warnings = audit.get('warnings', [])
        definition_only = p.relative_to(root).parts[0] in ['Spec', 'Model', 'Tests'] and audit.get('total_specs_audited') == 0
        if definition_only:
            expected_warning = 'no_specs_found: 0 theorem/lemma specifications recognized in ' + name
            if not ((audit.get('verdict') == 'no_specs_found' and warnings == [expected_warning])
                    or (audit.get('verdict') == 'specs_audited' and warnings == [] and audit.get('specs') == [])):
                raise RuntimeError('Unexpected definition-only audit: ' + name)
            warnings = []
        if (not audit.get('ok') or audit.get('vacuous_specs') or audit.get('trivial_specs') or warnings
                or audit.get('stub_defs') or audit.get('shadowed_constants') or audit.get('forbidden_scope_decls')):
            raise RuntimeError('Specification audit failed: ' + name)
    run('final-cli-agent-step', ['turbo-lean', '--json', 'agent-step', 'Proofs/Field/Extension.lean', '--decl', 'karatsuba_refines_spec', '--project-dir', '.'])
    local_order = ['Spec/Field/Basic.lean', 'Spec/Field/Operations.lean', 'Spec/Field/Quotient.lean', 'Model/Field/Scalar.lean',
                   'Model/Field/Operations.lean'] + ['Proofs/Field/' + n + '.lean' for n in
                   ['Basic', 'Convolution', 'Reduction', 'Quotient', 'Squares', 'Extension', 'Operations',
                    'Associativity', 'Powers', 'Frobenius', 'Inverse', 'ExtensionInverse', 'Codecs', 'Windows']]
    local_order += ['Model/Field/NativeKernel.lean', 'Proofs/Field/NativeHighShift.lean', 'Proofs/Field/NativeKernel.lean',
                    'Tests/Field/Intrinsic.lean', 'Tests/Field/Native.lean', 'Tests/Field/NativeRefinement.lean']
    run('final-direct-kernel-build', ['python3', 'Tests/Field/check_local.py', *local_order,
                                     'Tests/Field/Witnesses.lean', 'Tests/Field/ToolProbe.lean'])
    lean_path = str(root / '.lake/build/lib/lean')
    run('final-axioms', ['turbo-lean', 'eval', 'Tests/Field/AxiomAudit.lean', '--project-dir', '.', '--lean-path', lean_path])
    run('final-instance-axioms', ['turbo-lean', 'eval', 'Tests/Field/InstanceAudit.lean', '--project-dir', '.', '--lean-path', lean_path])
    mcp_root = root
    mcp_env = dict(env)
    mcp_env.pop('LEAN_PATH', None)
    run('final-mcp-stage', ['python3', 'Tests/Field/prepare_mcp_checked.py'])
    mcp_targets = ['Proofs.Field.Extension', 'Proofs.Field.Associativity', 'Proofs.Field.Inverse',
                   'Proofs.Field.ExtensionInverse', 'Proofs.Field.Codecs', 'Proofs.Field.Windows',
                   'Proofs.Field.NativeKernel', 'Tests.Field.ToolProbe']
    run('final-mcp-bootstrap-build', ['turbo-lean', '--json', 'build', '--project-dir', '.', *mcp_targets], cwd=mcp_root, env_override=mcp_env)
    for tool, args in [
        ('turbo_check_decl', dict(file='Proofs/Field/Extension.lean', project_dir=str(mcp_root), compact=False)),
        ('turbo_fast_check', dict(file='Tests/Field/ToolProbe.lean', decl='LeanVmXmss.Tests.Field.toolProbe', project_dir=str(mcp_root), backend='cpu', compact=False)),
        ('turbo_agent_step', dict(file='Proofs/Field/Extension.lean', decl='karatsuba_refines_spec', project_dir=str(mcp_root), compact=False, tpu=False)),
        ('turbo_audit_spec', dict(file='Proofs/Field/Extension.lean', project_dir=str(mcp_root)))]:
        response = json.loads(run('final-mcp-' + tool, ['python3', 'Tests/Field/mcp_driver.py', tool, json.dumps(args)], env_override=mcp_env))['response']['result']
        payload = json.loads(response['content'][0]['text'])
        if response.get('isError') or payload.get('ok') is False or payload.get('verified') is False:
            raise RuntimeError('MCP gate failed: ' + tool)
        if tool == 'turbo_audit_spec' and (payload.get('vacuous_specs') or payload.get('trivial_specs') or payload.get('warnings')):
            raise RuntimeError('MCP audit failed')
    mcp_obligations = [
        ('Extension', 'karatsuba_refines_spec'),
        ('Associativity', 'emul_assoc'),
        ('Inverse', 'mul_inv_nonzero'),
        ('ExtensionInverse', 'emul_inv_nonzero'),
        ('Codecs', 'encodeBytesE_decodeBytesE'),
        ('Windows', 'scaledMul_correct'),
        ('NativeKernel', 'nativeMul_correct'),
    ]
    for module, declaration in mcp_obligations:
        file = 'Proofs/Field/' + module + '.lean'
        for tool in ['turbo_check_decl', 'turbo_agent_step', 'turbo_audit_spec']:
            args = dict(file=file, project_dir=str(mcp_root))
            if tool == 'turbo_agent_step':
                args.update(decl=declaration, compact=False, tpu=False)
            elif tool == 'turbo_check_decl':
                args.update(compact=False)
            response = json.loads(run('mcp-' + module + '-' + tool,
                ['python3', 'Tests/Field/mcp_driver.py', tool, json.dumps(args)], env_override=mcp_env))['response']['result']
            payload = json.loads(response['content'][0]['text'])
            if response.get('isError') or payload.get('ok') is False or payload.get('verified') is False:
                raise RuntimeError('MCP gate failed: ' + file + ' ' + tool)
            if tool == 'turbo_audit_spec' and any(payload.get(key) for key in
                    ['vacuous_specs', 'trivial_specs', 'warnings', 'stub_defs',
                     'shadowed_constants', 'forbidden_scope_decls']):
                raise RuntimeError('MCP audit failed: ' + file)
    vectors = generate()
    data = ''.join(' '.join(map(str, row)) + '\n' for row in vectors)
    (artifacts / 'field-vectors.txt').write_text(data)
    run('final-rust-build', ['cargo', 'build', '--offline', '--release', '--manifest-path', 'Tests/Field/Rust/Cargo.toml'])
    rust = run('final-rust-differential', [str(artifacts / 'rust-target/release/field-reference-adapter')], stdin=data)
    lean = run('final-lean-differential', ['turbo-lean', 'eval', 'Tests/Field/Differential.lean', '--project-dir', '.', '--lean-path', lean_path])
    if rust != lean or len(lean.splitlines()) != len(vectors):
        raise RuntimeError('Rust / Lean mismatch or incomplete vector execution')
    executable = artifacts / 'field-native'
    native_env_path = env.get('LEAN_PATH', '')
    env['LEAN_PATH'] = lean_path + ':' + native_env_path
    native_log = run('final-native-build', ['python3', 'Tests/Field/build_native.py'])
    lowered = re.search(r'lowered & optimized ([0-9]+) LCNF declarations', native_log)
    if not lowered or int(lowered.group(1)) < 5:
        raise RuntimeError('Native build must lower and optimize at least five LCNF declarations')
    lnir = Path(str(executable) + '.lnir.ll').read_text()
    for symbol in ['shard_a_test_mul', 'shard_a_test_square', 'shard_a_test_inv',
                   'shard_a_test_karatsuba_c0', 'shard_a_test_karatsuba_c1', 'shard_a_test_karatsuba_c2']:
        if not re.search(r'define\s+[^\n]*@' + symbol + r'\(', lnir):
            raise RuntimeError('Missing lowered native kernel: ' + symbol)
    for index, (row, line) in enumerate(zip(vectors, rust.splitlines())):
        fields = line.split()
        expected = ' '.join([fields[1], fields[15], *fields[6:9], *fields[16:19], fields[2]]) + '\n'
        actual = run('final-native-vector-' + str(index), [str(executable), *map(str, row)])
        if actual != expected:
            raise RuntimeError('Native / Rust mismatch at vector ' + str(index))
    after = {str(p.relative_to(root)): sha(p) for p in source_files}
    if before != after:
        raise RuntimeError('Source changed during verification')
    evidence = dict(acceptance='PARTIAL' if missing else 'PASS', missing_obligations=missing,
                     log_directory=str(logs), vectors=len(vectors), boundary_and_extension_vectors=166, pseudorandom_vectors=240,
                     values_per_vector=31, rust_lean_equal=True,
                    vectors_sha256=sha(artifacts / 'field-vectors.txt'),
                    output_sha256=sha(logs / 'final-lean-differential.log'),
                    sources={str(p.relative_to(root)): sha(p) for p in source_files})
    (artifacts / 'verification.json').write_text(json.dumps(evidence, indent=2))
    print(json.dumps({k: v for k, v in evidence.items() if k != 'sources'}, indent=2))
    if missing:
        raise RuntimeError('PARTIAL ONLY: missing required theorem inventory: ' + json.dumps(missing))


if __name__ == '__main__':
    main()
