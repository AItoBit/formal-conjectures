"""Fetch the attributed external proof without redistributing it in this branch."""
from hashlib import sha256
from pathlib import Path
from urllib.request import Request, urlopen
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent.parent
URL = (
    "https://raw.githubusercontent.com/Jayyhk/erdos-lean/"
    "9c9f6d35da233a088e78be9dd418d2c0d17f31cc/problems/696/Erdos696.lean"
)
EXPECTED_SOURCE = "01eb45047a014fe9a61c2e6675c3a63ad126c4876ae0a95969f7756747cbe3ea"
EXPECTED_BODY = "a9e5ce94cb25e03454f12dfeb8ce53e867ba7c29910c9d7690cc678a08c4e7f5"
raw = urlopen(Request(URL, headers={"User-Agent": "Erdos696-proof-verification"})).read()
assert sha256(raw).hexdigest() == EXPECTED_SOURCE, "External source changed"
source = raw.decode("utf-8").replace("\r\n", "\n")
body = source[source.index("namespace Erdos696"):]
assert sha256(body.encode()).hexdigest() == EXPECTED_BODY, "Mathematical body changed"
imports = (HERE / "mathlib-imports.txt").read_text().splitlines()
assert all(line.startswith("import Mathlib.") for line in imports)
header = "module\n" + "\n".join("public " + line for line in imports)
header += "\n\n@[expose] public section\n\n"
assert source.startswith("import Mathlib\n")
adapted = source.replace("import Mathlib\n", header, 1)
assert adapted[adapted.index("namespace Erdos696"):] == body
(ROOT / "Erdos696External.lean").write_text(adapted, encoding="utf-8", newline="\n")
logs = HERE / "logs"
logs.mkdir(exist_ok=True)
(logs / "source-hashes.json").write_text(json.dumps({
    "url": URL,
    "upstream_sha256": EXPECTED_SOURCE,
    "normalized_mathematical_body_sha256": EXPECTED_BODY,
    "adapted_sha256": sha256(adapted.encode()).hexdigest(),
    "changes": "module visibility and explicit Mathlib imports only",
}, indent=2) + "\n")
print("Pinned source and unchanged mathematical body hashes verified.")
