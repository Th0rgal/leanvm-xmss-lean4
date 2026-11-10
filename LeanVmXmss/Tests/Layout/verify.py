import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parents[2]
evidence = root / 'Tests/Layout/evidence'
evidence.mkdir(exist_ok=True, parents=True)
results = []
oracle_bc = Path('/var/lib/sandboxed-node/.scratch/b2c1c0b9-4d89-47e7-ab06-c94b999a4cce/opencode/p1-shard-c-out/oracle/bytecode.bin')
rust_bin = root.parent / 'targets/rust/release/layout-oracle'


def run(label, args, timeout=3600, env=None):
    try:
        result = subprocess.run(args, cwd=root, env=env, text=True, capture_output=True, timeout=timeout)
        output = result.stdout + result.stderr
        rc = result.returncode
    except subprocess.TimeoutExpired as error:
        output = str(error)
        rc = 124
    (evidence / (label + '.log')).write_text(output)
    results.append(dict(label=label, argv=args, exit_code=rc))
    (evidence / 'verification.json').write_text(json.dumps(dict(status='IN_PROGRESS', commands=results), indent=2))
    if rc:
        raise RuntimeError(label + ' failed with exit ' + str(rc))
    return output


def definition_only(rel, payload):
    warnings = payload.get('warnings', [])
    expected = 'no_specs_found: 0 theorem/lemma specifications recognized in ' + rel
    return ((payload.get('verdict') == 'no_specs_found' and warnings == [expected])
            or (payload.get('verdict') == 'specs_audited' and warnings == [] and payload.get('specs') == []))


def audit_file(rel, definition):
    run('check-' + rel.replace('/', '-'), ['turbo-lean', '--json', 'check', rel, '--project-dir', '.'])
    payload = json.loads(run('audit-' + rel.replace('/', '-'), ['turbo-lean', '--json', 'audit-spec', rel]))
    if definition and payload.get('total_specs_audited') == 0:
        if not definition_only(rel, payload):
            raise RuntimeError('strict definition-only audit failed: ' + rel)
        return
    warnings = payload.get('warnings', [])
    if (not payload.get('ok') or warnings or payload.get('vacuous_specs') or payload.get('trivial_specs')
            or payload.get('stub_defs') or payload.get('shadowed_constants') or payload.get('forbidden_scope_decls')):
        raise RuntimeError('strict audit failed: ' + rel)


def case_map(text):
    out = {}
    current = None
    for line in text.splitlines():
        if line.startswith('CASE|'):
            current = line.split('|', 1)[1]
            out[current] = []
        elif current is not None:
            out[current].append(line)
    return out


def main():
    run('build', ['turbo-lean', '--json', 'build', '--project-dir', '.', '--max-memory-mb', '6144',
                  'Proofs.Layout.Basic', 'Tests.Layout.Witnesses', 'Tests.Layout.Differential', 'Tests.Layout.Main'])
    for rel, definition in [
        ('Spec/Layout/Basic.lean', True),
        ('Model/Layout/Scalar.lean', True),
        ('Proofs/Layout/Basic.lean', False),
        ('Tests/Layout/Witnesses.lean', False),
        ('Tests/Layout/Differential.lean', True),
    ]:
        audit_file(rel, definition)
    run('axiom-audit', ['turbo-lean', 'eval', 'Tests/Layout/AxiomAudit.lean', '--project-dir', '.'])
    run('native-modules', [sys.executable, 'Tests/Hub/cache_manager.py', 'Tests.Layout.Main'])
    env = os.environ.copy()
    env['LEAN_PATH'] = str(root / '.lake/build/lib/lean') + ':' + env.get('LEAN_PATH', '')
    env.setdefault('TMPDIR', str(root.parent / 'tmp'))
    binary = evidence / 'layout-differential'
    run('native-build', ['lean-native', 'build-exe', '--input', 'Tests/Layout/Main.lean',
                         '-o', str(binary), '--dynamic-runtime'], env=env)
    rust = run('rust-oracle', [str(rust_bin), str(oracle_bc)], timeout=1800)
    lean = run('lean-oracle', [str(binary), str(oracle_bc)], timeout=1800)
    rust_cases = case_map(rust)
    lean_cases = case_map(lean)
    if set(rust_cases) != {'syn_tiny', 'syn_keccak_heavy', 'xmss1400'}:
        raise RuntimeError('unexpected rust case set: ' + str(sorted(rust_cases)))
    mismatches = []
    for name, rust_lines in rust_cases.items():
        lean_lines = lean_cases.get(name, [])
        if rust_lines != lean_lines:
            mismatches.append(dict(case=name, rust_lines=len(rust_lines), lean_lines=len(lean_lines)))
    (evidence / 'differential.json').write_text(json.dumps(dict(
        status='PASS' if not mismatches else 'FAIL',
        cases=sorted(rust_cases), mismatches=mismatches), indent=2))
    if mismatches:
        raise RuntimeError('layout differential mismatch: ' + json.dumps(mismatches))
    (evidence / 'verification.json').write_text(json.dumps(dict(status='COMPLETE', commands=results), indent=2))
    print(json.dumps(dict(status='COMPLETE', commands=len(results)), indent=2))


try:
    main()
except Exception as error:
    report = dict(status='BLOCKED_PARTIAL', blocker=str(error), commands=results)
    (evidence / 'verification.json').write_text(json.dumps(report, indent=2))
    print(json.dumps(report, indent=2))
    sys.exit(1)
