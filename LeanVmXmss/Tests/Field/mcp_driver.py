import json
import os
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parents[2]
logs = root / 'Tests' / 'Field' / 'artifacts' / 'logs'
logs.mkdir(parents=True, exist_ok=True)
client = root / 'Tests/Hub/mcp_client.py'
env = dict(os.environ)
project = json.loads(sys.argv[2]).get('project_dir', str(root)) if len(sys.argv) > 2 else str(root)

def call(method, params):
    result = subprocess.run([sys.executable, str(client), method, json.dumps(params)],
                            cwd=root, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    (logs / 'mcp-stderr.log').open('a').write(result.stderr)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return json.loads(result.stdout)

try:
    schemas = call('tools/list', {})
    (logs / 'mcp-schemas.json').write_text(json.dumps(schemas, indent=2))
    transcript = [schemas]
    if len(sys.argv) > 1:
        transcript.append(call('tools/call', dict(name=sys.argv[1], arguments=json.loads(sys.argv[2]))))
finally:
    (logs / ('mcp-transcript-' + (sys.argv[1] if len(sys.argv) > 1 else 'discovery') + '.json')).write_text(json.dumps(transcript, indent=2))
print(json.dumps(transcript[-1], indent=2))
