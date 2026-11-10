from pathlib import Path

root = Path(__file__).resolve().parents[2]
dest = root
for prefix in ['Spec', 'Model', 'Proofs', 'Tests']:
    target = dest / prefix / 'Field'
    if not target.is_dir():
        raise RuntimeError('Missing field sources: ' + str(target))
for name in ['lakefile.toml', 'lake-manifest.json', 'lean-toolchain']:
    if not (root / name).is_file():
        raise RuntimeError('Missing project file: ' + name)
print(dest)
