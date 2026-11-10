import json
import os
from pathlib import Path
import socket
import subprocess
import sys
import time

root = Path(__file__).resolve().parents[2]
hub = root.parent
runtime = hub / 'mcp-runtime'
runtime.mkdir(parents=True, exist_ok=True)
sock_path = Path('/tmp/tl-mcp-hub.sock')
pid_path = runtime / 'mcp.pid'
err_path = runtime / 'mcp.err'
schemas_path = runtime / 'schemas.json'
env = os.environ.copy()
env['TURBO_LEAN_HOME'] = str(hub / 'turbo-cache')
env.setdefault('TMPDIR', str(hub / 'tmp'))
env.setdefault('XDG_CACHE_HOME', str(hub / 'xdg-cache'))


def serve():
    if sock_path.exists():
        sock_path.unlink()
    proc = subprocess.Popen(
        ['turbo-lean', 'mcp', '--project-dir', str(root)], cwd=root, env=env,
        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=err_path.open('a'), text=True)
    seq = 0

    def rpc(method, params):
        nonlocal seq
        seq += 1
        request = dict(jsonrpc='2.0', id=seq, method=method, params=params)
        proc.stdin.write(json.dumps(request) + '\n')
        proc.stdin.flush()
        while True:
            line = proc.stdout.readline()
            if not line:
                raise RuntimeError('MCP closed')
            response = json.loads(line)
            if response.get('id') == seq:
                return dict(request=request, response=response)

    rpc('initialize', dict(protocolVersion='2024-11-05', capabilities={}, clientInfo=dict(name='hub-mcp', version='1')))
    proc.stdin.write(json.dumps(dict(jsonrpc='2.0', method='notifications/initialized')) + '\n')
    proc.stdin.flush()
    schemas = rpc('tools/list', {})['response']
    schemas_path.write_text(json.dumps(schemas, indent=2) + '\n')
    server = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    server.bind(str(sock_path))
    server.listen(16)
    pid_path.write_text(str(os.getpid()) + '\n')
    while True:
        conn, _ = server.accept()
        with conn:
            data = b''
            while True:
                chunk = conn.recv(65536)
                if not chunk:
                    break
                data += chunk
            payload = json.loads(data.decode())
            method = payload['method']
            if method == 'tools/list':
                reply = dict(request=dict(jsonrpc='2.0', id=0, method='tools/list', params={}), response=schemas)
            else:
                reply = rpc(method, payload.get('params', {}))
            conn.sendall(json.dumps(reply).encode())


def ensure_started():
    for _ in range(50):
        if sock_path.exists():
            try:
                with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as client:
                    client.connect(str(sock_path))
                    client.sendall(json.dumps(dict(method='tools/list', params={})).encode())
                    client.shutdown(socket.SHUT_WR)
                    if client.recv(65536):
                        return
            except OSError:
                pass
        if _ == 0:
            subprocess.Popen([sys.executable, str(Path(__file__).resolve()), '--daemon'],
                             cwd=root, env=env, start_new_session=True,
                             stdout=subprocess.DEVNULL, stderr=err_path.open('a'))
        time.sleep(0.1)
    raise RuntimeError('Persistent MCP daemon failed to start')


def request(method, params):
    ensure_started()
    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as client:
        client.connect(str(sock_path))
        client.sendall(json.dumps(dict(method=method, params=params)).encode())
        client.shutdown(socket.SHUT_WR)
        chunks = []
        while True:
            chunk = client.recv(65536)
            if not chunk:
                break
            chunks.append(chunk)
    return json.loads(b''.join(chunks).decode())


if __name__ == '__main__':
    if sys.argv[1:] == ['--daemon']:
        serve()
    elif not sys.argv[1:]:
        ensure_started()
        print(json.dumps(request('tools/list', {})['response']))
    else:
        print(json.dumps(request(sys.argv[1], json.loads(sys.argv[2]))))
