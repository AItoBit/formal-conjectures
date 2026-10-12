"""Prepare an isolated verification of a fixed external Lean proof snapshot."""
import concurrent.futures
import json
from pathlib import Path
import re
import urllib.request

SOURCE_COMMIT = "8822f7ddef30fadbd92e1c6ab4ed897af356af5e"
MATHLIB_COMMIT = "db584cd6d46c92f209a44c0f1c829460d327499d"
paths = json.loads(Path(".github/erdos622-closure.json").read_text())
root = Path("proof-audit")
root.mkdir(exist_ok=True)

def fetch(path):
    relative = Path(path).relative_to("src/latest")
    if relative.is_absolute() or ".." in relative.parts or relative.suffix != ".lean":
        raise ValueError(path)
    url = f"https://raw.githubusercontent.com/plby/lean-proofs/{SOURCE_COMMIT}/{path}"
    data = urllib.request.urlopen(url, timeout=120).read()
    target = root / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(data)
    return relative.with_suffix("").as_posix().replace("/", "."), data.decode()

with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
    sources = dict(pool.map(fetch, paths))

deps = {}
for name, source in sources.items():
    imports = re.findall(r"^\s*(?:public\s+)?import\s+([^\n]+)", source, re.M)
    deps[name] = []
    for line in imports:
        for imported in line.split("--", 1)[0].split():
            if imported in sources:
                deps[name].append(imported)
            elif imported != "Mathlib" and not imported.startswith("Mathlib."):
                raise ValueError(f"Unexpected external import in {name}: {imported}")

ordered, active, done = [], set(), set()
def visit(name):
    if name in active:
        raise ValueError(f"Cyclic import at {name}")
    if name in done:
        return
    active.add(name)
    for dependency in deps[name]:
        visit(dependency)
    active.remove(name)
    done.add(name)
    ordered.append(name)
visit("ErdosProblems.Erdos622")
assert len(ordered) == len(sources), "Closure contains unused files"
(root / "build-order.json").write_text(json.dumps(ordered))
(root / "lean-toolchain").write_text("leanprover/lean4:v4.33.0\n")
(root / "lakefile.toml").write_text(f'''name = "erdos622_verification"
version = "0.1.0"

[leanOptions]
relaxedAutoImplicit = false
maxSynthPendingDepth = 3

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "{MATHLIB_COMMIT}"

[[lean_lib]]
name = "ErdosProblems"
''')
(root / "Audit.lean").write_text('''import ErdosProblems.Erdos622

#check Erdos622.erdos_622
#print axioms Erdos622.erdos_622

open scoped Classical in
theorem erdos622_positive_density :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in Filter.atTop,
      ∀ G : SimpleGraph (Fin (2 * n)), G.IsRegularOfDegree (n + 1) →
        c * (2 : ℝ) ^ (2 * n) ≤ (Erdos622.cycleSpannedSubsets G).card := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  simpa using Erdos622.erdos_622 (1 / 4) (by norm_num)

#print axioms erdos622_positive_density
''', encoding="utf-8")
print(f"Prepared {len(ordered)} modules from {SOURCE_COMMIT}")
