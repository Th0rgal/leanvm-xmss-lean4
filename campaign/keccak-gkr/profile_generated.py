#!/usr/bin/env python3
"""Instrument a COPY of Lean-generated C. Never use this object for timing gates.

Counts actual constructor/UInt64 boxing sites and potential ByteArray COW calls.
The input and application Lean sources are never changed. Each thread owns its
counters; a process destructor writes aggregates after the prover joins its tasks.
"""
import argparse
import json
from pathlib import Path
import re

p = argparse.ArgumentParser()
p.add_argument('input', type=Path)
p.add_argument('output', type=Path)
a = p.parse_args()
source = a.input.read_text()
sites = []
lines = []
function = ''
timed = {'buildMaskRangeFlat', 'loadWordBitplanes', 'linearBitplanes',
         'chiIotaBitplanes', 'productRangeFlat', 'fillInitialRangeFlat',
         'fillInitialTableFlat', 'pairSumsRangeFlat', 'foldRowsFlat',
         'localRoundFlat', 'fold1InPlace', 'linearTransposePlanar',
         'packEvalRangePacks', 'outputWordsRangePacks', 'proveReductionFlat'}
for number, line in enumerate(source.splitlines(), 1):
    match = re.match(r'(?:LEAN_EXPORT |static )?[^;{}]*?\b(\w+)\([^;]*\)\{', line)
    if match:
        function = match[1]
        if any(function.endswith('_' + name) for name in timed):
            index = len(sites)
            sites.append(dict(id=index, line=number, function=function,
                              kind='thread_cpu_nanos'))
            line += (f'\nCampaignTimer campaign_timer '
                     f'__attribute__((cleanup(campaign_stop))) = '
                     f'{{{index}, campaign_now()}};')
    # Generated calls occupy single lines; arguments are simple temporaries.
    for call in ['lean_alloc_ctor', 'lean_box_uint64', 'lean_byte_array_set']:
        if '= ' + call + '(' not in line:
            continue
        index = len(sites)
        sites.append(dict(id=index, line=number, function=function, kind=call))
        line = line.replace(call + '(', f'campaign_{call}({index}, ')
    lines.append(line)

header = r'''
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
typedef struct CampaignCounts {
  struct CampaignCounts *next;
  uint64_t calls[CAMPAIGN_SITES], bytes[CAMPAIGN_SITES];
} CampaignCounts;
static pthread_mutex_t campaign_lock = PTHREAD_MUTEX_INITIALIZER;
static CampaignCounts *campaign_all;
static _Thread_local CampaignCounts *campaign_thread;
static void campaign_count(unsigned site, uint64_t bytes) {
  if (!campaign_thread) {
    campaign_thread = calloc(1, sizeof(CampaignCounts));
    if (!campaign_thread) abort();
    pthread_mutex_lock(&campaign_lock);
    campaign_thread->next = campaign_all;
    campaign_all = campaign_thread;
    pthread_mutex_unlock(&campaign_lock);
  }
  campaign_thread->calls[site]++;
  campaign_thread->bytes[site] += bytes;
}
typedef struct { unsigned site; uint64_t start; } CampaignTimer;
static uint64_t campaign_now(void) {
  struct timespec t; clock_gettime(CLOCK_THREAD_CPUTIME_ID, &t);
  return (uint64_t)t.tv_sec * 1000000000 + t.tv_nsec;
}
static void campaign_stop(CampaignTimer *t) {
  campaign_count(t->site, campaign_now() - t->start);
}
static lean_object *campaign_lean_alloc_ctor(unsigned site, unsigned tag,
    unsigned objects, unsigned scalars) {
  campaign_count(site, sizeof(void*) * (objects + 1) + scalars);
  return lean_alloc_ctor(tag, objects, scalars);
}
static lean_object *campaign_lean_box_uint64(unsigned site, uint64_t value) {
  campaign_count(site, 16);
  return lean_box_uint64(value);
}
static lean_object *campaign_lean_byte_array_set(unsigned site, lean_object *b,
    lean_object *i, uint8_t value) {
  /* bytes = input payload exposed to COW; runtime capacity/header not included. */
  campaign_count(site, lean_is_exclusive(b) ? 0 : lean_sarray_size(b));
  return lean_byte_array_set(b, i, value);
}
__attribute__((destructor)) static void campaign_write_counts(void) {
  const char *path = getenv("CAMPAIGN_ALLOC_OUT");
  if (!path) return;
  FILE *f = fopen(path, "a");
  if (!f) return;
  for (unsigned i = 0; i < CAMPAIGN_SITES; i++) {
    uint64_t calls = 0, bytes = 0;
    for (CampaignCounts *t = campaign_all; t; t = t->next) {
      calls += t->calls[i]; bytes += t->bytes[i];
    }
    if (calls) fprintf(f, "%s,%u,%llu,%llu\n", CAMPAIGN_MODULE, i,
      (unsigned long long) calls, (unsigned long long) bytes);
  }
  fclose(f);
}
'''
# Insert after lean.h so the runtime's inline functions remain unmodified.
text = '\n'.join(lines) + '\n'
include = '#include <lean/lean.h>'
if text.count(include) != 1:
    raise SystemExit('Expected one generated lean.h include')
prefix = (f'#define CAMPAIGN_SITES {len(sites)}\n'
          f'#define CAMPAIGN_MODULE {json.dumps(a.input.stem)}\n')
text = text.replace(include, include + '\n' + prefix + header)
a.output.write_text(text)
a.output.with_suffix('.sites.json').write_text(json.dumps(sites, indent=2) + '\n')
print(f'{len(sites)} diagnostic sites; constructor bytes exclude allocator rounding')
