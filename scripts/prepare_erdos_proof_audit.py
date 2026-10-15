# Copyright 2026 The Formal Conjectures Authors.
# Licensed under the Apache License, Version 2.0.
"""Prepare an isolated reproduction of a pinned public Lean proof."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil

parser = argparse.ArgumentParser()
parser.add_argument("--source", type=Path, required=True)
parser.add_argument("--output", type=Path, required=True)
parser.add_argument("--problem", choices=("636", "637"), required=True)
args = parser.parse_args()
modules = {}

def visit(module):
    if module in modules or module == "Mathlib" or module.startswith(
        ("Mathlib.", "Lean.", "Init.", "Std.")
    ):
        return
    relative = Path(*module.split(".")).with_suffix(".lean")
    original = args.source / relative
    content = original.read_bytes()
    modules[module] = {"path": str(relative), "sha256": hashlib.sha256(content).hexdigest()}
    for dependency in re.findall(
        r"^\s*(?:(?:public|private|meta)\s+)*import\s+([A-Za-z0-9_.]+)",
        content.decode("utf-8-sig"), re.M,
    ):
        visit(dependency)
    destination = args.output / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(content)

visit(f"ErdosProblems.Erdos{args.problem}")
shutil.copyfile(args.source / "LICENSE", args.output / "LICENSE")
(args.output / "lean-toolchain").write_text("leanprover/lean4:v4.33.0\n")
(args.output / "lakefile.toml").write_text('''name = "erdos_proof_reproduction"
version = "0.1.0"

[leanOptions]
pp.unicode.fun = true
relaxedAutoImplicit = false
weak.linter.mathlibStandardSet = true
maxSynthPendingDepth = 3

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.33.0"

[[lean_lib]]
name = "ErdosProblems"

[[lean_lib]]
name = "Util"
''')
name = "Erdos636.erdos636_rpow" if args.problem == "636" else "Erdos637.erdos_637"
(args.output / "Audit.lean").write_text(
    f"import ErdosProblems.Erdos{args.problem}\n\n#check {name}\n#print axioms {name}\n"
)
(args.output / "provenance.json").write_text(json.dumps({
    "repository": "https://github.com/plby/lean-proofs",
    "commit": "8822f7ddef30fadbd92e1c6ab4ed897af356af5e",
    "target": name,
    "toolchain": "leanprover/lean4:v4.33.0",
    "source_changes": [],
    "modules": modules,
}, indent=2))
print(f"Prepared {len(modules)} unchanged source modules for {name}")
