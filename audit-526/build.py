"""Rebuild the exact pinned first-party dependency closure for Erdős 526."""
import concurrent.futures
import json
import os
from pathlib import Path
import subprocess
import urllib.request

root = Path.cwd() / 'proof-audit'
root.mkdir(exist_ok=True)
metadata = json.loads(Path('audit-526/order.json').read_text())
commit = metadata['source_commit']
order = metadata['order']

def fetch(module):
    relative = module.replace('.', '/') + '.lean'
    url = f'https://raw.githubusercontent.com/plby/lean-proofs/{commit}/src/latest/{relative}'
    destination = root / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    with urllib.request.urlopen(url, timeout=120) as response:
        destination.write_bytes(response.read())

with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
    list(pool.map(fetch, order))

(root / 'lean-toolchain').write_text('leanprover/lean4:v4.33.0\n')
(root / 'lakefile.toml').write_text('''name = "erdos526audit"
version = "0.1.0"
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "db584cd6d46c92f209a44c0f1c829460d327499d"
[[lean_lib]]
name = "ErdosProblems"
[[lean_lib]]
name = "Wikipedia"
''')
subprocess.run(['lake', 'update'], cwd=root, check=True)
subprocess.run(['lake', 'exe', 'cache', 'get'], cwd=root, check=True)
env = os.environ.copy()
lean_path = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=root, text=True).strip()
env['LEAN_PATH'] = str(root / '.lake/build/lib/lean') + ':' + lean_path
logs = root / 'logs'
logs.mkdir(exist_ok=True)
for index, module in enumerate(order, 1):
    relative = module.replace('.', '/')
    output = root / '.lake/build/lib/lean' / (relative + '.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    print(f'[{index}/{len(order)}] {module}', flush=True)
    result = subprocess.run(['lake', 'env', 'lean', '-M8192', '-o', str(output), relative + '.lean'],
                            cwd=root, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (logs / (module + '.log')).write_text(result.stdout)
    print(result.stdout, end='', flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
print('FULL DEPENDENCY BUILD COMPLETED', flush=True)
