"""Rebuild the exact pinned first-party dependency closure for Erdős 527."""
import concurrent.futures
import json
import os
from pathlib import Path
import subprocess
import urllib.request

root = Path.cwd() / 'proof-audit'
root.mkdir(exist_ok=True)
metadata = json.loads(Path('audit-527/order.json').read_text())
commit = metadata['source_commit']
order = metadata['order']

def fetch(module):
    relative = module.replace('.', '/') + '.lean'
    url = (f'https://raw.githubusercontent.com/frenzymath/FormalPantheon/ffbb65c21afc8a36ace67720f1b0df1c63d26bd1/BoundedGaps/{relative}' if module.startswith('BoundedGaps.') else f'https://raw.githubusercontent.com/plby/lean-proofs/{commit}/src/latest/{relative}')
    destination = root / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    with urllib.request.urlopen(url, timeout=120) as response:
        destination.write_bytes(response.read())

with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
    list(pool.map(fetch, order))

# Apply only the relevant sections of the exact pinned compatibility patches.
import re
for name in ['formalpantheon-v4.33.0.patch', 'formalpantheon-v4.33.0-s2.patch', 'boundedgaps-linter-v4.33.0.patch']:
    url=f'https://raw.githubusercontent.com/plby/lean-proofs/{commit}/src/latest/patches/{name}'
    patch=urllib.request.urlopen(url).read().decode()
    sections=re.split(r'(?=^diff --git )',patch,flags=re.M)
    wanted={'b/BoundedGaps/'+m.replace('.','/')+'.lean' for m in order if m.startswith('BoundedGaps.')}
    selected=''.join(section for section in sections if any('+++ '+path+'\n' in section for path in wanted))
    if selected:
        patchpath=root/name
        patchpath.write_text(selected)
        subprocess.run(['git','apply','-p2',str(patchpath)],cwd=root,check=True)

(root / 'lean-toolchain').write_text('leanprover/lean4:v4.33.0\n')
(root / 'lakefile.toml').write_text('''name = "erdos527audit"
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

(root / 'AxiomAudit.lean').write_text('import ErdosProblems.Erdos527\n#print axioms Erdos527.erdos_527\n')
subprocess.run(['lake','env','lean','AxiomAudit.lean'],cwd=root,env=env,check=True)
