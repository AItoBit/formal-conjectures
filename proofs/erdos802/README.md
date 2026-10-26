# Erdős Problem 802: complete Lean proof

This package proves the full Formal Conjectures statement: for every clique size `r`, there is a positive constant `c` such that every finite `K_r`-free graph of average degree `d` has an independent set of size at least `c * n * log(d) / d`.

`Bridge802.lean` is the exact all-`r`, all-degree bridge theorem `Erdos802Bridge.erdos_802`. It reduces to the released logarithmic independence theorem for `r >= 4` and `d >= 2`; for smaller `r`, it uses monotonicity of clique-freeness, and for `d < 2` it applies the release's bounded-maximum-degree estimate after retaining at least half the vertices. The bridge also identifies the Formal Conjectures rational average degree with the proof's real average degree.

The 31 modules in `OAI/Combinatorics/CliqueFree/` reproduce the proof in OpenAI's *A logarithmic independence bound for clique-free graphs* (September 25, 2026). They are copied from [`openai/math` at commit `1581d4cbdd69a0faf34b2089614fe2a814316a6a`](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-Logarithmic-Independence-Bound-for-Clique-Free-Graphs-September-25-2026). The original Apache-2.0 license and source file hashes are preserved.

## Reproduce

The package pins Lean 4.34.1 and Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`.

```sh
lake update
python verify.py --fresh
```

`verify.py` checks the pinned versions and every copied source hash, compiles all 31 release modules and the bridge/results, rejects proof holes and unsafe declarations, and runs `#print axioms` on the main theorem and four variants. The only axioms are Lean/Mathlib's standard `propext`, `Classical.choice`, and `Quot.sound`.
