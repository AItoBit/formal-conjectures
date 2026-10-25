from pathlib import Path
import hashlib,urllib.request
p=Path(__file__).resolve().parent/'Erdos797.lean'
expected='069c7310c36492867fdc8492041022a2b5d64f366db29cea253edb22025317a5'
url='https://raw.githubusercontent.com/plby/lean-proofs/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos797.lean'
data=p.read_bytes() if p.exists() else urllib.request.urlopen(url).read()
if hashlib.sha256(data).hexdigest()!=expected:raise SystemExit('Source hash mismatch')
if not p.exists():p.write_bytes(data)
print('Pinned original source verified:',expected)
