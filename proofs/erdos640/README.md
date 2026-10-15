# Erdős 640: the known three-colour case

This project proves the known case `k = 3`, with threshold `N = 3`, of Erdős and Hajnal's question. The full problem remains open. No solution of the general problem or mathematical novelty is claimed.

The source first proves that an odd closed walk contains a simple odd cycle, by strong induction on its length. A non-simple tail contains a nonempty closed subwalk. If that subwalk is odd, recurse on it; otherwise delete it and recurse on the shorter odd closed walk.

The cycle is transported to the graph induced by its entire vertex support. Its odd length excludes a two-colouring of that induced graph. All chords of the ambient graph are retained. A cycle is not required to be induced.

The final declaration `Erdos640.erdos_640.variants.three` copies the finite-graph statement in the contribution. It follows from the stronger arbitrary-vertex-type theorem `Erdos640.hasHighChromaticOddCycle_three`.

The checked endpoint axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. The source has no proof placeholders or native evaluation. It imports only the required Mathlib graph modules.

## Reproduce

With the pinned Lean toolchain installed, run in this directory:

```
lake update
lake exe cache get
lake --wfail build Erdos640
lake env lean Erdos640.lean
```

The final command prints the actual axiom dependencies. The `lake-manifest.json` records the dependency revisions used for the original check.

Source: [Erdős Problem 640](https://www.erdosproblems.com/640), including the known `k = 3` observation. Main question: P. Erdős, *Some recent problems and results in graph theory*, Discrete Mathematics 164 (1997), 81–85, p.84.
