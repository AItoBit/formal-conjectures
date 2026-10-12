"""Check each external source module with Lean, in dependency order."""
import json
from pathlib import Path
import subprocess
import time

root = Path("proof-audit")
modules = json.loads((root / "build-order.json").read_text())
for index, module in enumerate(modules, 1):
    path = module.replace(".", "/")
    output = Path(".lake/build/lib/lean") / (path + ".olean")
    (root / output).parent.mkdir(parents=True, exist_ok=True)
    print(f"[{index}/{len(modules)}] Checking {module}", flush=True)
    started = time.monotonic()
    subprocess.run(["lake", "env", "lean", "-DrelaxedAutoImplicit=false",
                    "-DmaxSynthPendingDepth=3", "-o", str(output), path + ".lean"],
                   cwd=root, check=True, timeout=1800)
    print(f"Finished in {time.monotonic() - started:.1f}s", flush=True)
subprocess.run(["lake", "env", "lean", "Audit.lean"], cwd=root, check=True)
