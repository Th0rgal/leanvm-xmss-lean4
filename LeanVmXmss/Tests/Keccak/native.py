from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys

root = Path(__file__).resolve().parents[2]
out = root.parent.parent / 'p1-shard-b-out'
env = dict(os.environ)
env['LEAN_PATH'] = str(root / '.lake/build/lib/lean') + ':' + env.get('LEAN_PATH', '')

subprocess.run([sys.executable, str(root / 'Tests/Hub/cache_manager.py'),
                'Tests.Keccak.Native', 'Tests.Keccak.NativeRefinement'],
               cwd=root, env=env, check=True)
build = subprocess.run(['lean-native', 'compile-static-lib', '--input',
                        str(root / 'Tests/Keccak/Native.lean'),
                        '-o', str(out / 'keccak-lanes.a'),
                        '--header', str(out / 'keccak-lanes.h')],
                       cwd=root, env=env, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, check=True).stdout
(out / 'keccak-lanes-build.log').write_text(build)
ir = out / 'keccak-lanes.lnir.ll'
subprocess.run(['lean-native', 'compile-llvm', '--input',
                str(root / 'Tests/Keccak/Native.lean'), '-o', str(ir)],
               cwd=root, env=env, check=True)
text = ir.read_text()
declarations = len(re.findall(r'; LNIRDecl:', text))
symbols = [f'shard_b_native_lane_{i:02d}' for i in range(25)] + [
    'shard_b_native_duplex_input_rate',
    'shard_b_native_pow_mask',
    'shard_b_native_pow_ok',
    'shard_b_native_round_constant',
]
if declarations < 29 or any(f'define dso_local i64 @{name}' not in text for name in symbols):
    raise RuntimeError('Missing lowered 25-lane + sponge/pow native kernel')
driver = out / 'keccak-lanes-driver.c'
lane_symbols = [f'shard_b_native_lane_{i:02d}' for i in range(25)]
args = ', '.join(f's[{j}]' for j in range(25))
calls = ',\n    '.join(f'{name}({args}, rc)' for name in lane_symbols)
driver.write_text(f'''#include <stdio.h>
#include <inttypes.h>
#include "keccak-lanes.h"

static void permute25(uint64_t s[25]) {{
  for (uint64_t i = 0; i < 24; ++i) {{
    uint64_t rc = shard_b_native_round_constant(i);
    uint64_t n[25] = {{ {calls} }};
    for (unsigned k = 0; k < 25; ++k) s[k] = n[k];
  }}
}}

typedef struct {{
  uint64_t state[25];
  uint64_t p[4][4];
  uint64_t pending;
}} sponge_t;

static void sponge_duplex(sponge_t *sp, uint64_t out[3]) {{
  uint64_t in[25];
  for (uint64_t slot = 0; slot < 4; ++slot) {{
    for (uint64_t lane = 0; lane < 4; ++lane) {{
      in[4 * slot + lane] = shard_b_native_duplex_input_rate(
          sp->pending, slot, lane,
          sp->p[slot][0], sp->p[slot][1], sp->p[slot][2], sp->p[slot][3]);
    }}
  }}
  for (unsigned k = 16; k < 25; ++k) in[k] = sp->state[k];
  permute25(in);
  for (unsigned k = 0; k < 25; ++k) sp->state[k] = in[k];
  sp->pending = 0;
  out[0] = in[0];
  out[1] = in[1];
  out[2] = in[2];
}}

static void sponge_absorb(sponge_t *sp, uint64_t c0, uint64_t c1, uint64_t c2, uint64_t tag) {{
  uint64_t dummy[3];
  if (sp->pending == 4) sponge_duplex(sp, dummy);
  uint64_t idx = sp->pending < 3 ? sp->pending : 3;
  sp->p[idx][0] = c0;
  sp->p[idx][1] = c1;
  sp->p[idx][2] = c2;
  sp->p[idx][3] = tag;
  sp->pending = idx + 1;
}}

int main(void) {{
  uint64_t s[25] = {{1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25}};
  permute25(s);
  printf("%" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 "\\n", s[0], s[1], s[2], s[16], s[24]);

  sponge_t sp = {{{{11, 22, 33, 44, 55, 66, 77, 88}}, {{{{0}}}}, 0}};
  permute25(sp.state);
  for (uint64_t k = 0; k < 6; ++k) {{
    sponge_absorb(&sp, k + 1, k * 17 + 3, k * 31 + 5, 1);
  }}
  uint64_t ch[3];
  sponge_duplex(&sp, ch);
  printf("%" PRIu64 " %" PRIu64 " %" PRIu64 "\\n", ch[0], ch[1], ch[2]);

  uint64_t found = 0;
  sponge_t after_pow = sp;
  for (uint64_t n = 0; n < 100000; ++n) {{
    sponge_t probe = sp;
    uint64_t out[3];
    sponge_absorb(&probe, n, 0, 0, 4);
    sponge_duplex(&probe, out);
    if (shard_b_native_pow_ok(out[0], 6)) {{
      found = n;
      after_pow = probe;
      break;
    }}
  }}
  uint64_t ch2[3];
  sponge_duplex(&after_pow, ch2);
  printf("%" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 "\\n", found, ch2[0], ch2[1], ch2[2]);
  return 0;
}}
''')
executable = out / 'keccak-lanes-driver'
subprocess.run(['cc', '-O2', str(driver), str(out / 'keccak-lanes.a'), '-o', str(executable)],
               cwd=out, env=env, check=True)
native = subprocess.run([str(executable)], text=True, stdout=subprocess.PIPE, check=True).stdout
reference = subprocess.run(['lean', '--run', 'Tests/Keccak/LaneRunner.lean'], cwd=root,
                           env=env, text=True, stdout=subprocess.PIPE, check=True).stdout
receipt = dict(module='Tests.Keccak.Native', native_stdout=native, reference_stdout=reference,
               equal=native == reference, lowered_declarations=declarations, lanes=25, rounds=24,
               kernel_refinement_checked=True,
               scope='full 25-lane 24-round register kernel + overwrite duplex sponge + PoW check',
               lnir_sha256=hashlib.sha256(ir.read_bytes()).hexdigest(),
               source_sha256=hashlib.sha256((root / 'Tests/Keccak/Native.lean').read_bytes()).hexdigest())
(out / 'keccak-imported-execution.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
if not receipt['equal']:
    raise RuntimeError('Native lanes differ from the register model')
