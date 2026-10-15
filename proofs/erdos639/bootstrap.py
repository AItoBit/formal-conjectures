"""Fetch one immutable Lean source as data and apply checked compatibility edits."""
from pathlib import Path
import argparse
import hashlib
import json
import urllib.request

ROOT = Path(__file__).resolve().parent

def sha(data):
    return hashlib.sha256(data).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, help='Use an already downloaded original source')
    args = parser.parse_args()
    manifest = json.loads((ROOT / 'source-manifest.json').read_text(encoding='utf8'))
    if args.source:
        data = args.source.read_bytes()
    else:
        request = urllib.request.Request(manifest['url'], headers={'User-Agent': 'Erdos639-proof-audit'})
        with urllib.request.urlopen(request, timeout=60) as response:
            data = response.read()
    if sha(data) != manifest['original_byte_sha256']:
        raise SystemExit('Original source checksum differs')
    text = data.decode('utf8').replace('\r\n', '\n')
    for before, after in manifest['edits']:
        if text.count(before) != 1:
            raise SystemExit('Compatibility edit does not have a unique match')
        text = text.replace(before, after)
    result = text.encode('utf8')
    if sha(result) != manifest['ported_lf_sha256']:
        raise SystemExit('Ported source checksum differs')
    path = ROOT / 'Erdos639.lean'
    if path.exists() and sha(path.read_text(encoding='utf8').encode('utf8')) != manifest['ported_lf_sha256']:
        raise SystemExit('Existing generated source has local changes')
    path.write_bytes(result)
    print('Prepared the attributed external proof; both source hashes checked')

if __name__ == '__main__':
    main()
