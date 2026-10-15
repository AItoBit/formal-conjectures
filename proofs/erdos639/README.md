# Erdős 639: the eventual bound and the six-vertex exception

The mathematical result is due to Keevash and Sudakov. The main formal proof is by Aristotle and Parcly Taxel, hosted by plby at commit `68da20b96673899166e94638f5a7fffeb7231d35`. This project reproduces that proof on Lean 4.33.1 and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

`bootstrap.py` fetches the one immutable source file as data, verifies its SHA-256, applies two recorded proof-body compatibility edits, and checks the result's hash. The edits remove premature unfolding of subtype embeddings from simplification. All mathematical targets and hypotheses are unchanged. No upstream scripts are executed. The generated original source is ignored by Git; its authorship and licensing are not replaced by this repository's license.

`Bridge639.lean` identifies the repository's set of unordered uncovered edges with the source proof's graph edge set. It proves both the exact eventual repository clause and the bound for every `n >= 10`. `SmallSix639.lean` gives a concrete colouring with ten uncovered edges and checks it by kernel `decide`.

The checked declarations use only `propext`, `Classical.choice`, and `Quot.sound`. These results do not by themselves establish the exact all-orders maximum: the upper bounds for six through nine vertices and attainment require additional proofs.

## Reproduce

With Python 3 and the pinned Lean toolchain installed:

```
python bootstrap.py
lake update
lake exe cache get
python verify.py
```

An already downloaded original source may be supplied with `python bootstrap.py --source /path/to/Erdos639.lean`. The source and resulting port must match the recorded hashes. The verifier checks actual printed axioms; successful compilation alone is insufficient.

Primary mathematical source: Peter Keevash and Benny Sudakov, *On the number of edges not covered by monochromatic copies of a fixed graph*, J. Combin. Theory Ser. B 90 (2004), 41–53, [DOI](https://doi.org/10.1016/S0095-8956(03)00075-3).
