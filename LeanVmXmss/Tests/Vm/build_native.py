import os
from pathlib import Path
import re
import subprocess
import sys

root = Path(__file__).resolve().parents[2]
out = Path('/var/lib/orb-node/work/caches/p1-shard-c-out')
evidence = root / 'Tests/Vm/evidence'
env = os.environ.copy()
env['LEAN_PATH'] = str(root / '.lake/build/lib/lean') + ':' + env.get('LEAN_PATH', '')
env.setdefault('TMPDIR', str(out))
subprocess.run([sys.executable, str(root / 'Tests/Hub/cache_manager.py'),
                'Model.Vm.Kernel', 'Tests.Vm.Full', 'Proofs.Vm.Kernel'],
               cwd=root, env=env, check=True)
evidence.mkdir(parents=True, exist_ok=True)
kernel_ll = evidence / 'vm-kernel.lnir.ll'
subprocess.run(['lean-native', 'compile-llvm', '--input', str(root / 'Model/Vm/Kernel.lean'),
                '-o', str(kernel_ll)],
               cwd=root, env=env, check=True)
kernel_text = kernel_ll.read_text()
lowered = len(re.findall(r'; LNIRDecl:', kernel_text))
symbols = ['shard_c_xor_kernel', 'shard_c_keccak_theta', 'shard_c_keccak_chi',
           'shard_c_rotate_left', 'shard_c_rotate_right']
if lowered < 5 or any(f'@{name}(' not in kernel_text for name in symbols):
    raise RuntimeError('Missing lowered Model.Vm.Kernel LNIR declarations')
kernel_obj = evidence / 'vm-kernel.lnir.o'
subprocess.run(['clang', '-O3', '-DNDEBUG', '-c', str(kernel_ll), '-o', str(kernel_obj)],
               cwd=root, env=env, check=True)
for source, binary in [('Tests/Xmss/Main.lean', 'xmss-differential'), ('Tests/Vm/Full.lean', 'vm-full')]:
    result = subprocess.run(['lean-native', 'build-exe', '--input', str(root / source),
                             '-o', str(evidence / binary), '--dynamic-runtime'],
                            cwd=root, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (out / ('native-' + binary + '.log')).write_text(result.stdout)
    print(result.stdout, end='', flush=True)
    if result.returncode:
        raise RuntimeError(binary + ': ' + result.stdout)
vm_lnir = Path(str(evidence / 'vm-full') + '.lnir.ll').read_text()
if len(re.findall(r'; LNIRDecl:', vm_lnir)) < 5:
    raise RuntimeError('vm-full lowered fewer than 5 LCNF declarations')

