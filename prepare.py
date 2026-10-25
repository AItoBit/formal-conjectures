from pathlib import Path
import hashlib,json,urllib.request
p=Path(__file__).resolve().parent
m=json.loads((p/'source-provenance.json').read_text(encoding='utf-8'))
for entry in m['modules']:
    path=entry['path']; target=p/path.removeprefix('src/latest/')
    url='https://raw.githubusercontent.com/plby/lean-proofs/'+m['commit']+'/'+path
    data=target.read_bytes() if target.exists() else urllib.request.urlopen(url,timeout=90).read()
    if hashlib.sha256(data).hexdigest()!=entry['sha256']:raise SystemExit('Hash mismatch: '+path)
    target.parent.mkdir(parents=True,exist_ok=True)
    if not target.exists():target.write_bytes(data)
print('All10pinnedoriginalmodulesverified.')
