import base64
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tarfile

root = Path(__file__).resolve().parents[2]
here = root / 'Tests/Transcript'
out = root.parent.parent / 'p1-shard-b-out'
logs = out / 'evidence'
logs.mkdir(parents=True, exist_ok=True)
env = dict(os.environ)
env.update(TMPDIR=str(out), TURBO_LEAN_HOME=str(out / 'turbo-cache'),
           XDG_CACHE_HOME=str(out / 'xdg'), CARGO_TARGET_DIR=str(out / 'rust-target'))
env['LEAN_PATH'] = str(root / '.lake/build/lib/lean') + ':' + env.get('LEAN_PATH', '')


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def run(label, args):
    p = subprocess.run(args, cwd=root, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (logs / (label + '.log')).write_text(p.stdout)
    if p.returncode or re.search(r'(^Error:|: error[:(])', p.stdout, re.M):
        raise RuntimeError(label + ': ' + p.stdout[-6000:])
    return p.stdout


def checked_mcp():
    import runpy
    runpy.run_path(str(here / 'mcp.py'), run_name='__main__')


def main():
    assert run('git-version', ['git', '--version']).strip().startswith('git version 2.')
    ordered = ['Spec/Keccak/Basic', 'Model/Keccak/Scalar', 'Spec/Merkle/Basic', 'Model/Merkle/Scalar',
               'Spec/Transcript/Basic', 'Model/Transcript/Scalar', 'Proofs/Keccak/Refinement',
               'Proofs/Merkle/Refinement', 'Proofs/Transcript/Refinement', 'Tests/Keccak/Witnesses',
               'Tests/Merkle/Witnesses', 'Tests/Transcript/Witnesses', 'Model/Keccak/Registers',
               'Proofs/Keccak/Registers', 'Spec/Merkle/Pruned', 'Model/Merkle/Heap',
               'Spec/Transcript/Replay', 'Model/Transcript/Registers', 'Proofs/Transcript/Minimality',
               'Proofs/Transcript/Registers', 'Proofs/Merkle/Contracts', 'Proofs/Transcript/Replay',
               'Tests/Merkle/Pruned', 'Tests/Transcript/Differential', 'Tests/Transcript/Mutants',
               'Tests/Keccak/Native', 'Tests/Keccak/NativeRefinement', 'Tests/Keccak/LaneRunner']
    for name in ordered:
        text = (root / (name + '.lean')).read_text()
        if re.search(r'\b(sorry|admit|native_decide|bv_decide|axiom)\b', text) or '--' in text or '/-' in text:
            raise RuntimeError('Forbidden source token: ' + name)
    run('incremental-cache', ['python3', 'Tests/Hub/cache_manager.py'] +
        [name.replace('/', '.') for name in ordered])
    run('rust-build', ['cargo', 'build', '--offline', '--release', '--manifest-path', 'Tests/Transcript/Rust/Cargo.toml'])
    rust = run('rust-output', [str(Path(env['CARGO_TARGET_DIR']) / 'release/shard-b-reference')])
    lean = run('lean-output', ['lean', 'Tests/Transcript/Differential.lean'])
    if rust != lean:
        raise RuntimeError('Rust/Lean mismatch; inspect evidence outputs')
    run('imported-native', ['python3', 'Tests/Keccak/native.py'])
    native = json.loads((out / 'keccak-imported-execution.json').read_text())
    evidence = dict(exit_code=None, rust_lean_equal=True, imported_native=native,
                    keccak_lengths=[0, 1, 135, 136, 137, 272, 1000], merkle_widths=[1, 2, 4, 8],
                    pow_bits=[0, 4, 8], output_sha256=hashlib.sha256(rust.encode()).hexdigest())
    (logs / 'verification.json').write_text(json.dumps(evidence, indent=2))
    try:
        run('axioms', ['lean', 'Tests/Transcript/AxiomAudit.lean'])
    except RuntimeError:
        evidence.update(exit_code=1, failed_gate='strict_transitive_axiom_audit')
        (logs / 'verification.json').write_text(json.dumps(evidence, indent=2))
        raise
    evidence.update(strict_transitive_axiom_audit=True)
    (logs / 'verification.json').write_text(json.dumps(evidence, indent=2))
    try:
        checked_mcp()
    except Exception:
        evidence.update(exit_code=1, mcp_gates_passed=False, failed_gate='mcp')
        (logs / 'verification.json').write_text(json.dumps(evidence, indent=2))
        raise
    evidence.update(exit_code=0, mcp_gates_passed=True,
                    heap_refinement_complete=True, prover_verifier_refinement_complete=True,
                    native_kernel_lowered=True)
    (logs / 'verification.json').write_text(json.dumps(evidence, indent=2))
    print(json.dumps(evidence, indent=2))


if __name__ == '__main__':
    main()
