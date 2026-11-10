import base64
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import socket
import subprocess
import tarfile

root = Path(__file__).resolve().parents[2]
evidence = root / 'Tests/Vm/evidence'
output = Path('/var/lib/orb-node/work/caches/p1-shard-c-out')
stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')

def capture(label, args):
    result = subprocess.run(args, cwd=root, capture_output=True, text=True, timeout=240)
    text = result.stdout + result.stderr
    (evidence / (label + '.log')).write_text(text)
    return dict(exit_code=result.returncode, command=args, output=text)

build = capture('checkpoint-proof-build', ['turbo-lean', '--json', 'build', '--project-dir', '.',
                'Proofs.Xmss.Encoding', 'Proofs.Vm.GPow'])
kernel = capture('checkpoint-kernel', ['lean-native', 'compile-llvm', '--input',
                 'Model/Vm/Kernel.lean', '-o', 'Tests/Vm/evidence/kernel.ll'])
field = capture('checkpoint-field-dependency', ['turbo-lean', 'eval',
                'Tests/Vm/FieldDependency.lean', '--project-dir', '.'])
audit = capture('checkpoint-global-audit', ['turbo-lean', 'eval',
                'Tests/Vm/AxiomAudit.lean', '--project-dir', '.'])
oracle = evidence / 'oracle'
execution = json.loads((oracle / 'execution.json').read_text())
lean = (oracle / 'lean-execution.txt').read_text()
for expected in [f"cycles={execution['cycles']}",
                 f"memory_cells_used={execution['memory_cells_used']}",
                 execution['memory_keccak256'],
                 'counts=#[' + ', '.join(map(str, execution['rows'])) + ']',
                 'unconstrained_reads=[]']:
    if expected not in lean:
        raise RuntimeError('Saved full VM report mismatch: ' + expected)
comparison = dict(status='PASS', checked_at=stamp, evidence_kind='comparison of saved completed runs',
                  cycles=execution['cycles'], memory_cells_used=execution['memory_cells_used'],
                  memory_keccak256=execution['memory_keccak256'], opcode_counts=execution['rows'],
                  unconstrained_reads=[], lean_report=lean,
                  runtime_rerun_after_latest_proof_edits=False)
(evidence / 'full-vm-comparison.json').write_text(json.dumps(comparison, indent=2))
fieldpath = root / 'Spec/Field/Basic.lean'
fieldinfo = dict(source_path=str(fieldpath), source_sha256=hashlib.sha256(fieldpath.read_bytes()).hexdigest(),
                 source_revision='working-tree content identified by SHA256',
                 lean_version=capture('checkpoint-lean-version', ['lean', '--version']),
                 imported_module='Spec.Field.Basic', probe=field,
                 dependency_chain=['LeanVmXmss.Spec.Field.instBEqE',
                                   'LeanVmXmss.Spec.Field.instBEqE.beq', 'Classical.choice'],
                 chain_detail='First edge printed from instance body; final transitive dependency certified by collectAxioms. Intermediate imported bodies unavailable to recursive walker.',
                 modified=False)
(evidence / 'field-import-identity.json').write_text(json.dumps(fieldinfo, indent=2))
state = dict(created_at_utc=stamp, machine=socket.gethostname(), status='INCOMPLETE',
             full_vm=comparison, proof_build=build, global_axiom_audit=audit,
             encoding='Both general directions compile: canonical E -> 16 bytes -> E; any 16 bytes -> E -> bytes.' if build['exit_code'] == 0 else 'Build failed; inspect log.',
             gpow='Loop-add/count and cache extension/growth validity compile; multiplicative homomorphism and initial invariant/runtime connection remain pending.',
             native_kernel=kernel,
             lcnf='Kernel contains only scalarGeneratorStep and xorKernel (no generatorLoop); LLVM output declares 2 compiled declarations. Relevant integrated runtime LCNF >0 is NOT established.',
             refinements='Principal VM/XMSS Model aliases remain; substantive non-alias refinements pending.',
             pending=['GPow multiplicative homomorphism and runtime invariants',
                      'Relevant integrated runtime native LCNF >0 and kernel refinement',
                      'Substantive Spec/Model separation and refinements',
                      'Synthetic Rust/Lean VM differential and memory monotonicity',
                      'Strict global axiom audit: Field instBEqE transitively uses Classical.choice',
                      'All required strict audit-spec/MCP gates and verify.py exit 0'],
             field_import=fieldinfo)
(evidence / 'checkpoint-state.json').write_text(json.dumps(state, indent=2))
files = []
for area in ['Spec', 'Model', 'Proofs', 'Tests']:
    for topic in ['Xmss', 'Vm']:
        for path in (root / area / topic).rglob('*'):
            if not path.is_file():
                continue
            rel = path.relative_to(root)
            if any(x in ['cargo-home', 'target', '__pycache__', 'generated'] for x in rel.parts):
                continue
            if path.suffix in ['.lean', '.py', '.rs', '.toml', '.lock', '.json', '.log', '.txt', '.ll'] and path.stat().st_size < 200000:
                files.append(path)
archive = output / ('shard-c-xmss-vm-' + stamp + '.tar.gz')
with tarfile.open(archive, 'w:gz', compresslevel=9) as tar:
    for path in sorted(files):
        tar.add(path, arcname=str(path.relative_to(root)))
encoded = archive.with_suffix('').with_suffix('.tgz.b64')
raw = base64.b64encode(archive.read_bytes()).decode()
encoded.write_text('\n'.join(raw[i:i+120] for i in range(0, len(raw), 120)) + '\n')
manifest = dict(state, archive_path=str(archive), base64_path=str(encoded),
                archive_bytes=archive.stat().st_size,
                archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest(),
                base64_bytes=encoded.stat().st_size,
                sources={str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(files)})
manifestpath = output / ('shard-c-manifest-' + stamp + '.json')
manifestpath.write_text(json.dumps(manifest, indent=2) + '\n')
(output / 'shard-c-xmss-vm.tar.gz').write_bytes(archive.read_bytes())
(output / 'shard-c-xmss-vm.tgz.b64').write_bytes(encoded.read_bytes())
(output / 'shard-c-manifest.json').write_bytes(manifestpath.read_bytes())
print(json.dumps(dict(manifest=str(manifestpath), archive=str(archive), base64=str(encoded),
                     archive_bytes=manifest['archive_bytes'], sha256=manifest['archive_sha256'],
                     base64_lines=len(raw) // 120 + bool(len(raw) % 120)), indent=2))
