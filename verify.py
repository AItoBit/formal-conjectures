from pathlib import Path
import hashlib,json,re,subprocess
p=Path(__file__).resolve().parent
for name,expected in json.loads((p/'source-hashes.json').read_text()).items():
    assert hashlib.sha256((p/name).read_bytes()).hexdigest()==expected,name
for f in p.glob('*.lean'):
    s=f.read_text(encoding='utf-8')
    assert not re.search(r'\b(sorry|sorryAx|admit|unsafe|native_decide)\b',s),f
    assert not re.search(r'^\s*axiom\s',s,re.M),f
subprocess.run(['lake','--wfail','build','Definitions792','Construction792','Upper792','Main792','Target792'],cwd=p,check=True)
subprocess.run(['lake','env','lean','Audit792.lean'],cwd=p,check=True)
