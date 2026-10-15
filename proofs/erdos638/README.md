# Erdős 638: proof and exact statement bridge

This project verifies negative answers to the literal and ordinary-hereditary readings of Erdős 638. The mathematical counterexample is credited to Brian Saturnino / InfiniteInsights. The completed sparse Ramsey construction and hereditary reduction are from Star Fleet Math. No mathematical novelty is claimed here.

The source archive is fetched as data from:
https://www.starfleetmath.com/downloads/verify/erdos-638/erdos-638-solution.zip

Its required SHA-256 is:
`a90f7b27fe3fcb2b23b2919fbc978cc5ad6a7b70ea1847a161400cb6d70f9880`.
The bootstrap never executes the archive's scripts. It extracts only the 41 named Lean modules after checking their original hashes, applies the recorded compatibility edits, and checks the resulting normalized source hashes. Generated sources are ignored by Git; original third-party licensing is not replaced by this repository's license.

The original project pins Lean4.31.0 and Mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`. This port uses Lean4.33.1 and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Changes provide explicit reflexivity and constructor-disjointness proofs, expose definitional adjacency and embedding reductions, replace rewriting with rewriting through semireducible definitions where required, and repair a local instance binding. All mathematical declaration targets are preserved.

## Reproduce

Install Python3 and the pinned Lean toolchain. In this directory:

```
python bootstrap.py
lake update
lake exe cache get
python verify.py
```

For an already downloaded archive, use `python bootstrap.py --archive /path/to/erdos-638-solution.zip`. The complete external project builds with newer-Mathlib style warnings; these are recorded separately from proof validity. No linter is disabled. The bridge itself is checked with warnings as errors.

The verifier builds the complete `Research` library, compiles `Bridge638.lean`, and checks that each of these reports only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`:

- `Erdos638.erdos638_ordinaryHereditary_answer_is_no` (the external full hereditary theorem)
- `Erdos638FC.frozen_literal`
- `Erdos638FC.frozen_subgraph_closed`

The two frozen targets copy the repository theorem clauses exactly, with a separate namespace to avoid importing the statement repository's intentional placeholders. The bridge converts bundled finite graphs to families indexed by their order and proves that ordinary containment agrees with injective graph homomorphisms. Its triangle predicate is definitionally the external one. Ordinary heredity implies isomorphism closure via the inverse isomorphism.

This answers the two stated readings. It does not claim that every possible additional interpretation involving joint embedding or amalgamation has been settled.
