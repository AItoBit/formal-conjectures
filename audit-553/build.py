import concurrent.futures
import json
import os
from pathlib import Path
import subprocess
import urllib.request

metadata=json.loads(Path('audit-553/order.json').read_text())
root=Path('proof-audit')
root.mkdir(exist_ok=True)
def fetch(module):
    relative=module.replace('.','/')+'.lean'
    url=f"https://raw.githubusercontent.com/plby/lean-proofs/{metadata['source_commit']}/src/latest/{relative}"
    dest=root/relative
    dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_bytes(urllib.request.urlopen(url,timeout=120).read())
with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
    list(pool.map(fetch,metadata['order']))
subprocess.run(['lake','exe','cache','get'],check=True)
subprocess.run(['lake','--wfail','build','FormalConjecturesUtil'],check=True)
env=os.environ.copy()
search=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],text=True).strip()
env['LEAN_PATH']=str(root.resolve())+':'+search
for module in metadata['order']:
    stem=root/module.replace('.','/')
    print('BUILD',module,flush=True)
    subprocess.run(['lake','env','lean','--root=proof-audit',str(stem)+'.lean','-o',str(stem)+'.olean'],env=env,check=True)
pr=json.loads(Path('audit-553/pr.json').read_text())
url=f"https://raw.githubusercontent.com/Konamiu/formal-conjectures/{pr['headRefOid']}/FormalConjectures/ErdosProblems/553.lean"
proposed=urllib.request.urlopen(url,timeout=120).read().decode()
(Path('FormalConjectures/ErdosProblems')/'553.lean').write_text(proposed)
subprocess.run(['lake','--wfail','build','FormalConjectures.ErdosProblems.«553»'],check=True)
(root/'Proposed553.lean').write_text(proposed.replace('Erdos553','Erdos553Proposed'))
subprocess.run(['lake','env','lean','--root=proof-audit',str(root/'Proposed553.lean'),'-o',str(root/'Proposed553.olean')],env=env,check=True)
(root/'Bridge553.lean').write_bytes(Path('audit-553/Bridge553.lean').read_bytes())
subprocess.run(['lake','env','lean','--root=proof-audit',str(root/'Bridge553.lean')],env=env,check=True)
print('PASS complete proof and exact statement bridge',flush=True)
