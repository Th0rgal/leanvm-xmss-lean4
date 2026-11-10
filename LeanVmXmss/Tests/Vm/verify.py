import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parents[2]
evidence = root / 'Tests/Vm/evidence'
evidence.mkdir(exist_ok=True, parents=True)
results = []

def run(label, args, timeout=240, env=None):
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

def main():
    run('build', ['turbo-lean', '--json', 'build', '--project-dir', '.',
                  'Tests.Vm.Witnesses', 'Tests.Vm.RuntimeIO', 'Tests.Vm.Synthetic', 'Proofs.Vm.Linear'])
    files = sorted(p for area in ['Spec', 'Model', 'Proofs', 'Tests'] for topic in ['Xmss', 'Vm']
                   for p in (root / area / topic).glob('*.lean') if p.name not in ['Native.lean', 'NativeFull.lean', 'NativeSynthetic.lean', 'Full.lean', 'DependencyProbe.lean', 'FieldDependency.lean', 'AxiomAudit.lean'])
    for path in files:
        rel = str(path.relative_to(root))
        run('check-' + rel.replace('/', '-'), ['turbo-lean', '--json', 'check', rel, '--project-dir', '.'])
        payload = json.loads(run('audit-' + rel.replace('/', '-'), ['turbo-lean', '--json', 'audit-spec', rel]))
        warnings = payload.get('warnings', [])
        definition_only = path.parts[-3] in ['Spec', 'Model', 'Tests'] and payload.get('total_specs_audited') == 0
        if definition_only:
            expected_warning = 'no_specs_found: 0 theorem/lemma specifications recognized in ' + rel
            if not ((payload.get('verdict') == 'no_specs_found' and warnings == [expected_warning])
                    or (payload.get('verdict') == 'specs_audited' and warnings == [] and payload.get('specs') == [])):
                raise RuntimeError('strict definition-only audit failed: ' + rel)
            warnings = []
        if (not payload.get('ok') or warnings or payload.get('vacuous_specs') or payload.get('trivial_specs')
                or payload.get('stub_defs') or payload.get('shadowed_constants') or payload.get('forbidden_scope_decls')):
            raise RuntimeError('strict audit failed: ' + rel)
    run('axiom-audit', ['turbo-lean', 'eval', 'Tests/Vm/AxiomAudit.lean', '--project-dir', '.'])
    schemas = json.loads(run('mcp-schemas', ['python3', 'Tests/Vm/mcp_driver.py']))
    available = {x['name']: x['inputSchema'] for x in schemas['result']['tools']}
    for name in ['turbo_fast_check', 'turbo_agent_step', 'turbo_audit_spec', 'turbo_check']:
        actual = name if name in available else 'turbo_check_decl' if name == 'turbo_check' else name
        if actual not in available:
            raise RuntimeError('required MCP tool unavailable: ' + name)
        args = dict(file='Proofs/Vm/Basic.lean', project_dir=str(root), compact=False)
        if name in ['turbo_fast_check', 'turbo_agent_step']:
            args['decl'] = 'store_out_of_memory'
        payload = json.loads(run('mcp-' + name, ['python3', 'Tests/Vm/mcp_driver.py', actual, json.dumps(args)]))
        if payload.get('error') or payload.get('result', {}).get('isError'):
            raise RuntimeError('MCP gate failed: ' + name)
    run('synthetic-differential', ['python3', 'Tests/Vm/synthetic.py'])
    run('native-build', ['python3', 'Tests/Vm/build_native.py'])
    fixture = '/var/lib/sandboxed-node/.scratch/b2c1c0b9-4d89-47e7-ab06-c94b999a4cce/opencode/p1-shard-c-out/xmss-inputs.bin'
    oracle = '/var/lib/sandboxed-node/.scratch/b2c1c0b9-4d89-47e7-ab06-c94b999a4cce/opencode/p1-shard-c-out/oracle'
    run('native-xmss-full', ['Tests/Vm/evidence/xmss-differential', fixture, oracle])
    run('native-vm-full', ['Tests/Vm/evidence/vm-full', fixture, oracle], timeout=int(os.environ.get('SHARD_C_VM_TIMEOUT', '1800')))
    execution = json.loads(Path(oracle, 'execution.json').read_text())
    lean = Path(oracle, 'lean-execution.txt').read_text()
    for item in [f"cycles={execution['cycles']}", f"memory_cells_used={execution['memory_cells_used']}", execution['memory_keccak256'], 'unconstrained_reads=[]']:
        if item not in lean:
            raise RuntimeError('full VM mismatch: ' + item)
    counts = '#[' + ', '.join(map(str, execution['rows'])) + ']'
    if 'counts=' + counts not in lean:
        raise RuntimeError('full VM opcode count mismatch')
    (evidence / 'full-vm-comparison.json').write_text(json.dumps(dict(
        status='PASS', cycles=execution['cycles'], memory_cells_used=execution['memory_cells_used'],
        memory_keccak256=execution['memory_keccak256'], opcode_counts=execution['rows'],
        unconstrained_reads=[], lean_report=lean), indent=2))
    report = dict(status='COMPLETE', commands=results, full_vm=json.loads((evidence / 'full-vm-comparison.json').read_text()))
    (evidence / 'verification.json').write_text(json.dumps(report, indent=2))
    print(json.dumps(dict(status='COMPLETE', commands=len(results)), indent=2))

try:
    main()
except Exception as error:
    report = dict(status='BLOCKED_PARTIAL', blocker=str(error), commands=results)
    (evidence / 'verification.json').write_text(json.dumps(report, indent=2))
    print(json.dumps(report, indent=2))
    sys.exit(1)
