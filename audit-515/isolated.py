"""Rebuild pinned external sources and prove the exact FC declaration in isolation."""
import concurrent.futures
import hashlib
import json
import os
import re
from pathlib import Path
import subprocess
import urllib.request

FC_COMMIT = '66f3fb70a35318c275d633dac2aea67c02c7c288'
EXTERNAL_COMMIT = '8822f7ddef30fadbd92e1c6ab4ed897af356af5e'
base = Path.cwd()
root = base / 'isolated-fc'
logs = base / 'isolated-logs'
logs.mkdir(exist_ok=True)
metadata = json.loads((base / 'audit-515/order.json').read_text())
assert metadata['source_commit'] == EXTERNAL_COMMIT

def run(args, cwd=root, env=None, log=None):
    print('RUN', ' '.join(map(str, args)), flush=True)
    result = subprocess.run(args, cwd=cwd, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True)
    print(result.stdout, end='', flush=True)
    if log:
        (logs / log).write_text(result.stdout)
    if result.returncode:
        raise SystemExit(result.returncode)
    return result.stdout

root.mkdir()
run(['git', 'init'])
run(['git', 'fetch', '--depth=1', 'https://github.com/AItoBit/formal-conjectures', FC_COMMIT])
run(['git', 'checkout', '--detach', 'FETCH_HEAD'])
assert run(['git', 'rev-parse', 'HEAD']).strip() == FC_COMMIT
run(['lake', '--version'])
run(['lake', 'exe', 'cache', 'get'], log='cache.log')
run(['lake', '--wfail', 'build', 'FormalConjecturesUtil'], log='fc-import-build.log')
env = os.environ.copy()
env['LEAN_PATH'] = run(['lake', 'env', 'printenv', 'LEAN_PATH']).strip()

def fetch(module):
    relative = module.replace('.', '/') + '.lean'
    url = f'https://raw.githubusercontent.com/plby/lean-proofs/{EXTERNAL_COMMIT}/src/latest/{relative}'
    with urllib.request.urlopen(url, timeout=120) as response:
        source = response.read()
    destination = root / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(source)
    return module, hashlib.sha256(source).hexdigest()

with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
    hashes = dict(pool.map(fetch, metadata['order']))
(logs / 'external-source-hashes.json').write_text(json.dumps(hashes, indent=2))
for index, module in enumerate(metadata['order'], 1):
    relative = module.replace('.', '/')
    output = root / '.lake/build/lib/lean' / (relative + '.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    print(f'EXTERNAL [{index}/{len(metadata["order"])}] {module}', flush=True)
    run(['lake', 'env', 'lean', '-M8192', '-o', str(output), relative + '.lean'],
        env=env, log=module + '.log')

source = (root / 'FormalConjectures/ErdosProblems/515.lean').read_bytes().decode('utf-8')
(logs / 'FC515.original.lean').write_text(source)
assert source.count('namespace Erdos515') == 1
assert source.count('end Erdos515') == 1
assert source.count('  sorry') == 1
marker = 'theorem erdos_515 :'
prefix, statement_and_proof = source.split(marker)
statement, placeholder = statement_and_proof.split(' := by\n', 1)
assert placeholder == '  sorry\n\nend Erdos515\n'
relocated = prefix.replace('namespace Erdos515', 'namespace FC515')
relocated = relocated.replace('public import FormalConjecturesUtil',
    'public import FormalConjecturesUtil\npublic import ErdosProblems.Erdos515')
bridge = (base / 'audit-515/Bridge.lean').read_text()
bridge = bridge.replace('FC515.', '')
theorem_doc_start = relocated.rindex('/--')
verified = (relocated[:theorem_doc_start] + bridge + '\n' +
            relocated[theorem_doc_start:] + marker + statement +
            ' := by\n  exact external_implies_fc\n\nend FC515\n')
assert verified.split(marker)[1].split(' := by\n')[0] == statement
for name in ['Erdos515.erdos_515', 'FC515.erdos_515']:
    verified += (f"\n/-- info: '{name}' depends on axioms: "
                 '[propext, Classical.choice, Quot.sound] -/\n'
                 f'#guard_msgs in\n#print axioms {name}\n')
for name in ['Erdos515.erdos_515', 'FC515.lineIntegral_toFC', 'FC515.erdos_515']:
    verified += f'\n#print axioms {name}\n'
(root / 'VerifiedFC515.lean').write_text(verified)
(logs / 'VerifiedFC515.lean').write_text(verified)
bridge_output = run(['lake', 'env', 'lean', '-DwarningAsError=true', 'VerifiedFC515.lean'],
                    env=env, log='bridge.log')
axiom_results = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", bridge_output)
assert len(axiom_results) == 3, axiom_results
permitted = {'propext', 'Classical.choice', 'Quot.sound'}
for name, axioms in axiom_results:
    actual = {axiom.strip() for axiom in axioms.split(',') if axiom.strip()}
    assert actual <= permitted, (name, actual)
provenance = {
    'fc_commit': FC_COMMIT,
    'external_commit': EXTERNAL_COMMIT,
    'fc_source_sha256': hashlib.sha256(source.encode()).hexdigest(),
    'fc_statement_preserved_byte_for_byte': True,
    'namespace_relocation': 'Erdos515 -> FC515 (external namespace unchanged)',
    'toolchain': (root / 'lean-toolchain').read_text().strip(),
    'mathlib': json.loads((root / 'lake-manifest.json').read_text())['packages'],
    'permitted_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
}
(logs / 'provenance.json').write_text(json.dumps(provenance, indent=2))
print('ISOLATED FC DECLARATION VERIFIED; ALL PERMITTED-AXIOM CHECKS PASSED', flush=True)
