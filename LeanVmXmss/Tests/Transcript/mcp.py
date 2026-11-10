import hashlib
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'Hub'))
import mcp_client

root = Path(__file__).resolve().parents[2]
out = root.parent.parent / 'p1-shard-b-out'
receipts = []
targets = [('Proofs/Keccak/Registers.lean', 'registers_permutation_refines_spec'),
           ('Proofs/Transcript/Registers.lean', 'grind_refines'),
           ('Proofs/Merkle/Contracts.lean', 'heap_verifyPath_complete'),
           ('Proofs/Transcript/Replay.lean', 'prover_session_verifier_refinement')]


def call(method, params):
    reply = mcp_client.request(method, params)
    receipts.append(reply)
    response = reply['response']
    if 'error' in response or response.get('result', {}).get('isError'):
        raise RuntimeError(json.dumps(response))
    return response['result']


try:
    tools = call('tools/list', {})['tools']
    schemas = {tool['name']: tool['inputSchema'] for tool in tools}
    for file, decl in targets:
        for requested in ('turbo_fast_check', 'turbo_agent_step', 'turbo_audit_spec', 'turbo_check'):
            name = requested if requested in schemas else 'turbo_check_decl' if requested == 'turbo_check' else requested
            schema = schemas[name]
            args = dict(file=file, decl=decl, project_dir=str(root), compact=False,
                        tpu=False, backend='cpu', require_nonempty=True)
            args = {key: value for key, value in args.items() if key in schema.get('properties', {})}
            assert all(key in args for key in schema.get('required', []))
            result = call('tools/call', dict(name=name, arguments=args))
            payloads = [json.loads(item['text']) for item in result.get('content', []) if item.get('type') == 'text']
            assert payloads
            for payload in payloads:
                assert payload.get('ok') is True, payload
                assert payload.get('verified') is not False, payload
                if name == 'turbo_audit_spec':
                    assert payload.get('total_specs_audited', 0) > 0, payload
                    assert payload.get('vacuous_specs') == 0 and payload.get('trivial_specs') == 0, payload
                    assert not payload.get('horizontal_packing_warnings'), payload
                    assert not payload.get('forbidden_scope_decls'), payload
                if name in ('turbo_check', 'turbo_check_decl', 'turbo_agent_step'):
                    assert payload.get('verified') is True, payload
                    assert payload.get('stage') == 'stage2_kernel_verified', payload
            print(file, name, 'passed', flush=True)
    summary = dict(passed=True, calls=len(targets) * 4, targets=[dict(file=file, decl=decl,
                   source_sha256=hashlib.sha256((root / file).read_bytes()).hexdigest()) for file, decl in targets])
    (out / 'evidence/mcp-summary.json').write_text(json.dumps(summary, indent=2) + '\n')
finally:
    (out / 'evidence/mcp.json').write_text(json.dumps(receipts, indent=2) + '\n')
