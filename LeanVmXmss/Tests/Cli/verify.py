import json
import os
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parents[2]
evidence = root / 'Tests/Cli/evidence'
evidence.mkdir(exist_ok=True, parents=True)
results = []
hub = os.environ.get('HUB', '/var/lib/orb-node/work/caches/xmss-hub-v3')
oracle_root = Path(hub) / 'oracle'
bin_dir = Path(hub) / 'artifacts/w4-cli-traces-tierb'
deliverables = Path(hub) / 'deliverables/w4-cli-traces-tierb'
e2e = Path(os.environ.get('CARGO_TARGET_DIR', str(Path(hub) / 'targets/rust'))) / 'release/e2e-oracle'
cli_check = bin_dir / 'cli-check'
traces = deliverables / 'traces'
traces.mkdir(parents=True, exist_ok=True)

def record(label, args, rc, output):
    (evidence / (label + '.log')).write_text(output)
    results.append(dict(label=label, argv=[str(a) for a in args], exit_code=rc))
    (evidence / 'verification.json').write_text(json.dumps(dict(status='IN_PROGRESS', commands=results), indent=2))

def run(label, args, timeout=2400, env=None):
    try:
        result = subprocess.run(args, cwd=root, env=env, text=True, capture_output=True, timeout=timeout)
        output = result.stdout + result.stderr
        rc = result.returncode
    except subprocess.TimeoutExpired as error:
        output = str(error)
        rc = 124
    record(label, args, rc, output)
    if rc:
        raise RuntimeError(label + ' failed with exit ' + str(rc))
    return output

def run_expect_fail(label, args, timeout=2400, env=None):
    """The command must exit non-zero (an invalid-proof rejection check)."""
    try:
        result = subprocess.run(args, cwd=root, env=env, text=True, capture_output=True, timeout=timeout)
        output = result.stdout + result.stderr
        rc = result.returncode
    except subprocess.TimeoutExpired as error:
        output = str(error)
        rc = 124
    record(label, args, rc, output)
    if rc == 0:
        raise RuntimeError(label + ' unexpectedly succeeded')
    return output

def main():
    env = os.environ.copy()
    run('build', ['python3', 'Tests/Hub/cache_manager.py',
                  'Model.Cli.Inputs', 'Model.Cli.Aggregate', 'Tests.Cli.Check'], env=env)
    files = ['Model/Cli/Inputs.lean', 'Model/Cli/Aggregate.lean', 'Tests/Cli/Check.lean']
    for rel in files:
        run('check-' + rel.replace('/', '-'), ['turbo-lean', '--json', 'check', rel, '--project-dir', '.'])
        payload = json.loads(run('audit-' + rel.replace('/', '-'), ['turbo-lean', '--json', 'audit-spec', rel]))
        warnings = payload.get('warnings', [])
        if payload.get('total_specs_audited') == 0:
            expected_warning = 'no_specs_found: 0 theorem/lemma specifications recognized in ' + rel
            if not ((payload.get('verdict') == 'no_specs_found' and warnings == [expected_warning])
                    or (payload.get('verdict') == 'specs_audited' and warnings == [] and payload.get('specs') == [])):
                raise RuntimeError('strict definition-only audit failed: ' + rel)
            warnings = []
        if (not payload.get('ok') or warnings or payload.get('vacuous_specs') or payload.get('trivial_specs')
                or payload.get('stub_defs') or payload.get('shadowed_constants') or payload.get('forbidden_scope_decls')):
            raise RuntimeError('strict audit failed: ' + rel)
    audit_env = env.copy()
    audit_env['LEAN_PATH'] = '.lake/build/lib/lean:' + audit_env.get('LEAN_PATH', '')
    run('axiom-audit', ['lean', 'Tests/Cli/AxiomAudit.lean'], env=audit_env, timeout=600)
    run('frozen-spec', ['bash', '-c',
        'cd "{root}" && sha256sum $(find Spec -name "*.lean" | sort) > {tmp} && diff {tmp} {baseline}'
        .format(root=root, tmp='/tmp/opencode/w4-spec-now.txt',
                baseline='/tmp/opencode/spec-frozen-baseline.txt')])
    run('rust-build', ['cargo', 'build', '--release', '--offline',
                       '--manifest-path', 'Tests/Cli/Rust/Cargo.toml'], env=env, timeout=1800)
    run('native-build', ['lean-native', 'build-exe', '--input', 'Tests/Cli/Check.lean',
                         '-o', str(cli_check), '--dynamic-runtime'], timeout=1800)
    run('cli-oracle-xmss4', [str(cli_check), 'oracle', str(oracle_root / 'xmss4')])
    run('cli-oracle-xmss16', [str(cli_check), 'oracle', str(oracle_root / 'xmss16')])
    run('cli-parity-xmss1400', [str(cli_check), 'parity', str(oracle_root / 'xmss1400')], timeout=1200)
    fresh = Path('/tmp/opencode/w4-fresh-inputs')
    run('gen-fresh-inputs', [str(e2e), 'gen-fresh-inputs', '5', '2026090901',
                             str(fresh), str(oracle_root / 'xmss4')], timeout=2400)
    run('cli-fresh', [str(cli_check), 'fresh', str(fresh), str(oracle_root / 'xmss4')])
    run('e2e-check-vm-xmss4', [str(e2e), 'check-vm', str(oracle_root / 'xmss4')])
    run('e2e-check-vm-xmss16', [str(e2e), 'check-vm', str(oracle_root / 'xmss16')])
    for fixture in ['xmss4', 'xmss16']:
        proof = bin_dir / ('cpu-proof-' + fixture + '.bin')
        run('export-proof-' + fixture, [str(e2e), 'export-proof', str(oracle_root / fixture), str(proof)])
        run('e2e-verify-vm-' + fixture, [str(e2e), 'verify-vm', str(oracle_root / fixture), str(proof)])
    for fixture in ['xmss4', 'xmss16']:
        eth_proof = bin_dir / ('eth-proof-' + fixture + '.bin')
        run('export-eth-proof-' + fixture,
            [str(e2e), 'export-eth-proof', str(oracle_root / fixture), str(eth_proof)], timeout=3600)
        run('e2e-verify-eth-' + fixture,
            [str(e2e), 'verify-eth', str(oracle_root / fixture / 'xmss-inputs.bin'), str(eth_proof)],
            timeout=2400)
    tampered = bin_dir / 'cpu-proof-tampered.bin'
    data = bytearray((bin_dir / 'cpu-proof-xmss4.bin').read_bytes())
    data[len(data) // 2] ^= 1
    tampered.write_bytes(data)
    run_expect_fail('e2e-verify-vm-rejects-tampered',
                    [str(e2e), 'verify-vm', str(oracle_root / 'xmss4'), str(tampered)])
    for name in ['syn_tiny', 'syn_jump', 'syn_deref', 'syn_keccak']:
        path = traces / (name + '.json')
        run('export-trace-' + name, [str(e2e), 'export-trace', 'syn:' + name, str(path)])
        run('verify-trace-' + name, [str(e2e), 'verify-trace', 'syn:' + name, str(path)])
    for fixture in ['xmss4', 'xmss16']:
        path = traces / (fixture + '.json')
        run('export-trace-' + fixture, [str(e2e), 'export-trace', str(oracle_root / fixture), str(path)])
        run('verify-trace-' + fixture, [str(e2e), 'verify-trace', str(oracle_root / fixture), str(path)])
    run('cli-gate', [str(cli_check), 'gate', str(oracle_root), str(fresh)], timeout=2400)
    report = dict(status='COMPLETE', commands=results)
    (evidence / 'verification.json').write_text(json.dumps(report, indent=2))
    print(json.dumps(dict(status='COMPLETE', commands=len(results)), indent=2))

try:
    main()
except Exception as error:
    report = dict(status='BLOCKED_PARTIAL', blocker=str(error), commands=results)
    (evidence / 'verification.json').write_text(json.dumps(report, indent=2))
    print(json.dumps(report, indent=2))
    sys.exit(1)
