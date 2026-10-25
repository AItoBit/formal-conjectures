# Erdős797: complete existing proof reproduced

For finite simple graphs, let f(d) be the least palette size that acyclically
colours every graph of maximum degree at most d. A colouring is proper and
no cycle uses at most two colours. All colours are available, not necessarily
used. The source's exactly-d convention is equivalent: adjoin a disjoint
star of degree d and restrict the resulting colouring to the original graph.

The verified conclusions are, for fixed positive c,C and all sufficiently
large d:

    c*d^(4/3)/(log d)^(1/3) <= f(d) <= C*d^(4/3),
    f(d) = o(d^2).

This reproduces the known resolution by Alon, McDiarmid and Reed. The pinned
4,006-line source credits Codex and GPT-5.6 Sol. It proves exact cubic bounds,
a finite local lemma, the lower graph construction, and the little-o result.
This does not close the logarithmic gap between the upper and lower estimates
or claim a new solution. The full paper's additional edge-colouring and
excluded-subgraph variants are outside the delivered theorem scope.

## Sources and exact bridge

- Problem: https://www.erdosproblems.com/forum/thread/797
- Primary paper: https://doi.org/10.1002/rsa.3240020303
- Existing statement PR: https://github.com/google-deepmind/formal-conjectures/pull/6340
- Complete original Lean source: https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos797.lean

`Acyclic797.lean` introduces the reusable bundled `G.Coloring` API.
`Statement797.lean` specifies the universal extremal function and both targets.
`Bridge797.lean` proves equality with the original extremal function, both
targets and an actual colouring guarantee at its least palette. This last
theorem verifies nonemptiness/attainment, avoiding an empty natural infimum.
`Bounds797.lean` converts the cubic bounds to real powers and natural logs.
The constants can be C=1024 and c=(log(2)/2^67)^(1/3). The eventual lower
bound holds for every degree beyond a fixed threshold, not just a subsequence.

The shared chromatic number is extended-natural, so infinite graphs without
a finite acyclic palette receive infinity. Finite graphs have a proved finite
witness. Its finite bound characterization and comparison with the ordinary
chromatic number are proved. Empty graphs and palettes are retained.

## Reproduce

Install the exact toolchain in lean-toolchain, then run:

    python prepare.py
    lake exe cache get
    python verify.py

Pins: Lean4.33.0; Mathlib db584cd6d46c92f209a44c0f1c829460d327499d.
The verifier builds all five libraries and audits25declared theorems, allowing
only propext, Classical.choice and Quot.sound. No proof holes, additional
mathematical axioms, unsafe declarations or native_decide occur in these sources.
The original source is fetched with a fixed SHA-256; it is not redistributed
because no source license grant was found. LICENSE covers only our wrapper/API.

## Proof mechanism

The upper proof uses independent random vertex colours. Four classes of bad
events detect monochromatic edges, alternating short paths, selected
bichromatic4cycles and repeated colours on pairs with many common neighbours.
Exact finite-product counting proves their independence outside shared
coordinates. A finite local lemma supplies a colouring avoiding all events;
this excludes every bichromatic cycle and gives a cubic palette bound.

The lower construction counts graphs and possible small colour partitions.
Pairs of vertices within colour classes yield many edge-disjoint potential
bichromatic4cycles. A counting bound prevents every small-palette colouring
while keeping maximum degree controlled. Monotonicity interpolates scales.
Positive cube roots and comparison of base-two integer logs with natural
logs give the real estimates; the upper estimate yields little-o of d².

See source-audit.md for correspondence and verification limits. The separate
literature campaign is incomplete; proof reproduction is not100-paper coverage.
