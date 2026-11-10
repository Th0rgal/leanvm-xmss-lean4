import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

root = Path(__file__).resolve().parents[2]
lib = root / '.lake/build/lib/lean'
ir = root / '.lake/build/ir'
native_c = root / '.lake/build/native-c'
manifest_path = root / '.lake/build/native-modules.json'
c_manifest_path = root / '.lake/build/native-c-cache.json'
env = os.environ.copy()
env['LEAN_PATH'] = str(lib) + ':' + env.get('LEAN_PATH', '')
env.setdefault('TMPDIR', str(root.parent / 'tmp'))
sysroot = subprocess.check_output(['lean', '--print-prefix'], text=True, env=env).strip()
records = json.loads(c_manifest_path.read_text()) if c_manifest_path.is_file() else (
    json.loads(manifest_path.read_text()) if manifest_path.is_file() else []
)
by_module = {record['module']: record for record in records}
done = set()


def run(args, cwd=root):
    result = subprocess.run(args, cwd=cwd, env=env, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(' '.join(args) + '\n' + result.stdout + result.stderr)
    return result.stdout + result.stderr


targets = sys.argv[1:]
build_targets = list(targets)
if (root / 'Tests/Hub/ShardAHw.lean').is_file() and 'Tests.Hub.ShardAHw' not in build_targets:
    build_targets.append('Tests.Hub.ShardAHw')
if build_targets:
    run(['turbo-lean', '--json', 'build', '--project-dir', '.'] + build_targets)
if manifest_path.is_file():
    for record in json.loads(manifest_path.read_text()):
        by_module.setdefault(record['module'], record)


def build(module):
    if module in done:
        return
    source = root / (module.replace('.', '/') + '.lean')
    if not source.is_file():
        return
    for line in source.read_text().splitlines():
        if line.startswith('import '):
            for dependency in line.split()[1:]:
                build(dependency)
    hw_source = root / 'Tests/Hub/ShardAHw.lean'
    digest_payload = 'pkg=LeanVmXmss\n' + source.read_text()
    if module == 'Model.Field.NativeKernel' and hw_source.is_file():
        digest_payload += '\nhw=' + hw_source.read_text()
    digest = hashlib.sha256(digest_payload.encode()).hexdigest()
    olean = lib / (module.replace('.', '/') + '.olean')
    cfile = ir / (module.replace('.', '/') + '.c')
    tmp_c = native_c / (module.replace('.', '/') + '.c')
    cached_obj = native_c / (module.replace('.', '/') + '.c.o.export')
    setup_json = native_c / (module.replace('.', '/') + '.setup.json')
    obj = Path(str(cfile) + '.o.export')
    previous = by_module.get(module)
    fresh = previous and previous.get('source_sha256') == digest and olean.is_file() and cached_obj.is_file()
    if not fresh:
        olean.parent.mkdir(parents=True, exist_ok=True)
        cfile.parent.mkdir(parents=True, exist_ok=True)
        tmp_c.parent.mkdir(parents=True, exist_ok=True)
        setup_json.write_text(json.dumps({
            'plugins': [],
            'package': 'LeanVmXmss',
            'options': {},
            'name': module,
            'isModule': False,
            'importArts': {},
            'dynlibs': [],
        }))
        run(['lean', '--setup=' + str(setup_json), '-c', str(tmp_c), str(source)])
        if module == 'Model.Field.NativeKernel' and (root / 'Tests/Hub/ShardAHw.lean').is_file():
            build('Tests.Field.Intrinsic')
            build('Tests.Hub.ShardAHw')
            raw_ll = native_c / 'Model/Field/NativeKernel.raw.ll'
            lnir_ll = native_c / 'Model/Field/NativeKernel.hw.lnir.ll'
            merged_ll = native_c / 'Model/Field/NativeKernel.merged.ll'
            opt_ll = native_c / 'Model/Field/NativeKernel.opt.ll'
            run(['clang', '-S', '-emit-llvm', '-O3', '-Xclang', '-disable-llvm-passes',
                 '-DNDEBUG', '-march=native', '-I' + sysroot + '/include', str(tmp_c), '-o', str(raw_ll)])
            run(['lean-native', 'compile-llvm', '--input', str(root / 'Tests/Hub/ShardAHw.lean'), '-o', str(lnir_ll)])
            run(['llvm-link', '-S', str(raw_ll), '--override=' + str(lnir_ll), '-o', str(merged_ll)])
            run(['opt', '-S', '-passes=default<O3>,loop-vectorize,slp-vectorizer', str(merged_ll), '-o', str(opt_ll)])
            run(['clang', '-O3', '-DNDEBUG', '-march=native', '-c', str(opt_ll), '-o', str(cached_obj)])
        else:
            run(['clang', '-O3', '-DNDEBUG', '-march=native', '-I' + sysroot + '/include', '-c', str(tmp_c), '-o', str(cached_obj)])
        shutil.copy2(cached_obj, obj)
        by_module[module] = dict(module=module, source_sha256=digest, olean=str(olean), object=str(obj), cached_object=str(cached_obj))
        c_manifest_path.write_text(json.dumps(list(by_module.values()), indent=2) + '\n')
        print('REBUILT', module, flush=True)
    else:
        if not obj.is_file():
            cfile.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(cached_obj, obj)
        print('REUSED', module, flush=True)
    done.add(module)


for target in targets:
    build(target)
