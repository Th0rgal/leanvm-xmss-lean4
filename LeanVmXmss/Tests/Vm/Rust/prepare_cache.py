from pathlib import Path
import shutil

source = Path('/var/lib/orb-node/work/caches/xmss-p0-59c2984-recovery/cargo-home/registry')
destination = Path(__file__).resolve().parent / 'cargo-home' / 'registry'
for name in ['index', 'cache']:
    shutil.copytree(source / name, destination / name, dirs_exist_ok=True)
print(destination.parent)
