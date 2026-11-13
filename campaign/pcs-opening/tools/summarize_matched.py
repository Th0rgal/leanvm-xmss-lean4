"""Summarize retained matched evidence without selecting minimum runs."""
import argparse,json,statistics,re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('baseline',type=Path);p.add_argument('candidate',type=Path);p.add_argument('output',type=Path);a=p.parse_args()
receipts={name:json.loads((d/'receipt.json').read_text()) for name,d in [('baseline',a.baseline),('candidate',a.candidate)]}
assert all(d['status']=='COMPLETE' for d in receipts.values()),'both matrices must finish'
report={'acceptance':{'seconds_strict_lt':1,'rss_bytes_strict_lt':4294967296},'certified':False,'certification_note':'One fresh Rust/Lean pair per workload per revision; fewer than five candidate full1400 alternating pairs. No certification regardless of means.','workloads':{}}
def select(r,label):return next(x for x in r['records'] if x['label']==label)
for n in [4,16,1400]:
 row={}
 for name,directory in [('baseline',a.baseline),('candidate',a.candidate)]:
  receipt=receipts[name];rr={}
  for impl in ['lean','rust']:
   v=select(receipt,f'p0-xmss{n}-{impl}-bench');times=[x/1e9 for x in v['passes_nanos']]
   rr[impl]={'passes_seconds':times,'mean_seconds':statistics.mean(times),'sample_stdev_seconds':statistics.stdev(times),'min_seconds':min(times),'max_seconds':max(times),'warmup_seconds':v['warmup_nanos']/1e9,'peak_rss_bytes':v['peak_rss_bytes'],'wall_seconds':v['wall_seconds'],'wire_bytes':v['proof_bytes'],'vm_proof_bytes':v['proof_size'],'every_measured_pass_under_1s':all(t<1 for t in times),'memory_under_4gib':v['peak_rss_bytes']<4294967296}
  phase=json.loads((directory/f'p0-xmss{n}-phases.json').read_text())
  rr['lean']['mean_phases_seconds']={k:v/1e9 for k,v in phase['mean']['phases_nanos'].items()}
  verify=select(receipt,f'p0-xmss{n}-verify');log=(directory/f'p0-xmss{n}-verify.log').read_text()
  assert verify['verification_passes']==3 and verify['signers_match']
  rr['verification']={'passes_ms':list(map(int,re.findall(r'VERIFY_ETH\|PASS\|pass=\d+\|ms=(\d+)',log))),'process_wall_seconds':verify['wall_seconds'],'peak_rss_bytes':verify['peak_rss_bytes'],'passes':3}
  row[name]=rr
 b=row['baseline']['lean'];c=row['candidate']['lean'];row['comparison']={'aggregation_seconds_saved':b['mean_seconds']-c['mean_seconds'],'aggregation_fraction_saved':1-c['mean_seconds']/b['mean_seconds'],'pcs_seconds_saved':b['mean_phases_seconds']['5_pcs_open']-c['mean_phases_seconds']['5_pcs_open'],'pcs_fraction_saved':1-c['mean_phases_seconds']['5_pcs_open']/b['mean_phases_seconds']['5_pcs_open'],'rss_bytes_saved':b['peak_rss_bytes']-c['peak_rss_bytes'],'time_gap_to_1s_boundary':c['mean_seconds']-1,'rss_gap_to_4gib_boundary_bytes':c['peak_rss_bytes']-4294967296,'time_threshold_ratio':c['mean_seconds'],'rss_threshold_ratio':c['peak_rss_bytes']/4294967296}
 old=(a.baseline/f'p0-xmss{n}-lean.ethproof').read_bytes();new=(a.candidate/f'p0-xmss{n}-lean.ethproof').read_bytes();assert old==new;row['full_wire_equal_unchanged']=True
 report['workloads'][str(n)]=row
rust_hashes=[next(v for k,v in r['binaries'].items() if k.endswith('e2e-oracle')) for r in receipts.values()];assert len(set(rust_hashes))==1;report['unchanged_rust_binary_sha256']=rust_hashes[0]
a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report['workloads']['1400']['comparison'],indent=2))
