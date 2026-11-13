"""One fresh diagnostic E2E pass, byte parity, and independent Rust verification."""
from pathlib import Path
import subprocess,time,json,hashlib,re
from collections import defaultdict
root=Path('/var/lib/orb-node/work')
e=root/'pcs-opening-evidence'
out=e/'diag1400'
out.mkdir(exist_ok=True)
receipt={'status':'RUNNING_DIAGNOSTIC_NOT_CERTIFICATION','start':time.time()}
def save():
 p=out/'receipt.json.tmp';p.write_text(json.dumps(receipt,indent=2)+'\n');p.replace(out/'receipt.json')
save()
try:
 with (out/'run.log').open('w') as f:
  p=subprocess.Popen(['/usr/bin/time','-v','-o',str(out/'run.time'),str(e/'pcs-diagnostic'),str(root/'pcs-restored-oracle/xmss1400'),str(out/'proof.ethproof')],stdout=f,stderr=subprocess.STDOUT)
  receipt['pid']=p.pid;save();p.wait();receipt['exit_code']=p.returncode
 if p.returncode:raise RuntimeError('diagnostic process failed')
 proof=(out/'proof.ethproof').read_bytes();parent=(e/'unchanged-native-matched/p0-xmss1400-lean.ethproof').read_bytes()
 receipt['wire_equal_parent']=proof==parent
 receipt['wire_sha256']=hashlib.sha256(proof).hexdigest()
 if proof!=parent:raise RuntimeError('diagnostic transcript/wire mismatch')
 with (out/'verify.log').open('w') as f:
  p=subprocess.run([str(e/'rust-native-target/release/e2e-oracle'),'verify-eth',str(root/'pcs-restored-oracle/xmss1400/xmss-inputs.bin'),str(out/'proof.ethproof'),'1400','1'],stdout=f,stderr=subprocess.STDOUT)
 text=(out/'verify.log').read_text()
 receipt['verification_passes']=text.count('VERIFY_ETH|PASS')
 if p.returncode or receipt['verification_passes']!=3 or '|signers=1400\n' not in text:raise RuntimeError('independent verifier failed')
 sums=defaultdict(int);calls=defaultdict(int);level='setup'
 for line in (out/'run.log').read_text().splitlines():
  if line.startswith('PCS_DIAG|'):
   label=line.split('|')[1]
   if label=='fold':level=re.search(r'level=(\d+)',line)[1]
   for key in [label,level+':'+label]:
    sums[key]+=int(line.rsplit('nanos=',1)[1]);calls[key]+=1
 receipt['costs']={k:{'seconds':v/1e9,'calls':calls[k]} for k,v in sums.items()}
 receipt['status']='COMPLETE_DIAGNOSTIC_NOT_CERTIFICATION'
except Exception as exc:
 receipt['status']='FAILED';receipt['error']=str(exc)
finally:
 receipt['wall_seconds']=time.time()-receipt['start'];save()
