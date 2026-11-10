from pathlib import Path
import textwrap

path = Path('/var/lib/orb-node/work/caches/p1-shard-c-out/shard-c-xmss-vm.tgz.b64')
encoded = ''.join(path.read_text().split())
path.write_text('\n'.join(textwrap.wrap(encoded, 120)) + '\n')
