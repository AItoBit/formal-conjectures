"""Fetch and port the checksum-pinned Star Fleet Erdős 638 proof sources.

Only source data is read from the archive. Its verifier scripts are never executed.
"""
from pathlib import Path
import argparse
import hashlib
import io
import json
import urllib.request
import zipfile

ROOT = Path(__file__).resolve().parent
URL = "https://www.starfleetmath.com/downloads/verify/erdos-638/erdos-638-solution.zip"
PREFIX = "erdos-638/verified_math/F-028_ordinary-hereditary-negative-answer/lean/"

def digest(data):
    return hashlib.sha256(data).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, help="Use a previously downloaded source ZIP")
    args = parser.parse_args()
    manifest = json.loads((ROOT / "source-manifest.json").read_text(encoding="utf8"))
    if args.archive:
        data = args.archive.read_bytes()
    else:
        request = urllib.request.Request(URL, headers={"User-Agent": "Erdos638-proof-source-audit"})
        with urllib.request.urlopen(request, timeout=120) as response:
            data = response.read()
    if digest(data) != manifest["archive_sha256"]:
        raise SystemExit("Source archive checksum differs; refusing to use changed upstream content")
    outputs = []
    with zipfile.ZipFile(io.BytesIO(data)) as archive:
        for name, record in manifest["files"].items():
            original = archive.read(PREFIX + name)
            if digest(original) != record["original_byte_sha256"]:
                raise SystemExit("Original source hash differs: " + name)
            text = original.decode("utf8").replace("\r\n", "\n")
            for edit in reversed(record["edits"]):
                text = text[:edit["start"]] + edit["replacement"] + text[edit["end"]:]
            result = text.encode("utf8")
            if digest(result) != record["ported_lf_sha256"]:
                raise SystemExit("Ported source hash differs: " + name)
            destination = ROOT / name
            if destination.exists():
                current = destination.read_text(encoding="utf8").encode("utf8")
                if digest(current) != record["ported_lf_sha256"]:
                    raise SystemExit("Existing generated file has local changes: " + name)
            outputs.append((destination, result))
    for destination, result in outputs:
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(result)
    print(f"Prepared {len(outputs)} proof modules; all original and ported hashes checked")

if __name__ == "__main__":
    main()
