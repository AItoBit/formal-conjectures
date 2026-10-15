"""Build the fetched proof and audit the exact repository-statement bridge."""
from pathlib import Path
import os
import re
import subprocess

ROOT = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED = [
    "Erdos638.erdos638_ordinaryHereditary_answer_is_no",
    "Erdos638FC.frozen_literal",
    "Erdos638FC.frozen_subgraph_closed",
]

def run(command, log_name):
    environment = dict(os.environ)
    environment.setdefault("LEAN_NUM_THREADS", "1")
    with (ROOT / log_name).open("w", encoding="utf8") as log:
        result = subprocess.run(command, cwd=ROOT, env=environment,
                                stdout=log, stderr=subprocess.STDOUT)
    if result.returncode:
        raise SystemExit(f"Command failed ({result.returncode}); inspect {log_name}")
    return (ROOT / log_name).read_text(encoding="utf8")

def main():
    run(["lake", "build", "Research"], "build.log")
    output = run(["lake", "env", "lean", "-E", "warning", "Bridge638.lean"], "axioms.log")
    for name in EXPECTED:
        match = re.search(re.escape("'" + name + "' depends on axioms: [") + r"([^]]*)\]", output)
        if not match:
            raise SystemExit("Missing axiom report: " + name)
        actual = {x.strip() for x in match.group(1).split(",") if x.strip()}
        if not actual <= ALLOWED:
            raise SystemExit("Unexpected axioms for " + name + ": " + repr(actual))
    print("PASS: complete hereditary proof and both exact frozen statements use only standard axioms")

if __name__ == "__main__":
    main()
