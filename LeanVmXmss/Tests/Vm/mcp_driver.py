import json
import os
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parents[2]
client = root / 'Tests/Hub/mcp_client.py'
env = dict(os.environ)

def call(method, params):
    result = subprocess.run([sys.executable, str(client), method, json.dumps(params)],
                            cwd=root, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return json.loads(result.stdout)

if len(sys.argv) == 1:
    print(json.dumps(call('tools/list', {})['response']))
else:
    print(json.dumps(call('tools/call', dict(name=sys.argv[1], arguments=json.loads(sys.argv[2])))['response']))
