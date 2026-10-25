from pathlib import Path
import hashlib, urllib.request
p = Path(__file__).resolve().parent / 'Erdos795.lean'
expected = 'c80f70e965bc3f1874da9b308be6780a1584e24f636fd1e1efefa4f55ca4b1d4'
url = 'https://raw.githubusercontent.com/plby/lean-proofs/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos795.lean'
data = p.read_bytes() if p.exists() else urllib.request.urlopen(url).read()
if hashlib.sha256(data).hexdigest() != expected:
    raise SystemExit('Upstream source hash mismatch')
if not p.exists(): p.write_bytes(data)
print('Verified pinned upstream source:', expected)
