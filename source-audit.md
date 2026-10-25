# Erdős 799 source and proof-interface audit

Reviewed 2026-10-25. This is a static/source audit; compilation of the ten-file closure is assigned separately.

## Statement and literature

The supplied source question asks whether the list chromatic number is o(n) for almost all graphs on n labelled vertices. My direct website HTTP request timed out; the parent obtained the website source. I independently checked the matching primary-paper statements and existing PR.

[Alon, Choice numbers of graphs; a probabilistic approach](https://web.math.princeton.edu/~nalon/PDFS/choice.pdf), published in Combinatorics, Probability and Computing 1 (1992), 107–114, states the stronger O(n log log n/log n) bound in Corollary 1.3. Its Section 4 proof embeds a typical random graph into a complete equipartite graph after using a coloring with small classes, then applies its multipartite choice-number estimate. I read the introduction, corollary, and this application proof; this is partial-text review, not whole-paper verification.

[Alon–Krivelevich–Sudakov, List coloring of random and pseudo-random graphs](https://web.math.princeton.edu/~nalon/PDFS/colaks9.pdf), introduction/Theorem 1.1, gives order np/log(np) for 2<np≤n/2. The introduction also attributes the sharper p=1/2 asymptotic equivalence with ordinary chromatic number to Kahn. Author publication lists give the journal version as Combinatorica 19 (1999), 453–472; distinguish that from a 1998/prepublication label. Only introductory/principal statements were reviewed here.

## Formal definitions and quantifiers

Pinned source: plby/lean-proofs, commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e, `src/latest/ErdosProblems/Erdos799.lean` and local imports.

`Erdos753.IsKChoosable` quantifies over every assignment of exactly k-element finite subsets of naturals, requiring a proper bundled coloring chosen from those lists. On a finite vertex set, arbitrary-palette lists have finite union, which embeds injectively into naturals; natural palettes are therefore faithful. This argument must not be generalized without qualification to arbitrary infinite graphs with uncountable palettes. Exactly k rather than at least k is equivalent by taking k-element sublists.

`listChromaticNumber` is a natural sInf. The imported file proves every finite graph is cardinality-of-vertices choosable by Hall, then `choosable_set_nonempty`. The finite domain thus excludes a vacuous empty-infimum/default-zero shortcut. Empty graphs have value zero; a nonempty graph cannot be zero-choosable.

`graphDensity P n` is the real cardinality of satisfying simple graphs on Fin n divided by the cardinality of all such graphs. There are 2^(n choose 2) labelled graphs; the denominator is positive even at n=0. This is uniform G(n,1/2), not uniform unlabelled isomorphism classes, not a fixed-edge-count distribution, and not arbitrary p. Requiring properties to be isomorphism-invariant is unnecessary for defining this probability; the list-coloring application is invariant.

The endpoint gives ONE deterministic b:ℕ→ℕ, b=o(n), and probability of χ_L(G)≤b(n) tending to one. It does not select b depending on the sampled graph or list assignment. This implies convergence χ_L(G)/n→0 in probability by eventual b(n)≤εn for each ε>0. Conversely the usual in-probability formulation admits a deterministic decreasing tolerance by diagonalization: choose increasing thresholds N_j≥j beyond which the failure probability at tolerance 1/j is at most 1/j, and let b(n)=ceil(n/j) on successive blocks. This gives b(n)/n≤1/j+1/n and failure→0. This equivalence is a mathematical quantifier audit, not an additional Lean theorem claimed here. It is not a pathwise almost-sure statement for an unspecified joint coupling across all n.

## Proof scope

The chosen threshold is `ramseyDiagonalBound`, the infimum of n/q+R(r(n),q)+1 over positive q. A witness q=1 proves the infimum set nonempty. The Ramsey/heavy-color argument bounds choice number when clique number is below the logarithmic cutoff; the large-clique exceptional density tends to zero. The root theorem uses this threshold's proved little-o property and complements the exceptional event.

This proves the full original affirmative o(n) clause. It does not formally prove Alon's quantitative log-log upper bound, AKS's Θ(n/log n), Kahn's sharp leading asymptotic, or sparse/pseudorandom generalizations. Those are known mathematical strengthenings outside the inspected endpoint, not unresolved original conjectures. The root file itself explicitly limits its claim to the shorter Ramsey-based proof.

## Provenance

Closure consists of root799, four799 helpers, Erdos1037, Erdos753, Erdos88/FiniteES, Erdos88/Foundations, and Util/Ramsey. Root799, 753, and the two88 files have explicit Apache notices. The four799 helpers, 1037, and Util/Ramsey have no license notice in the inspected headers; no blanket license grant is inferred. Keep mixed-license source fetch-only unless permissions are separately established. The 1037 introductory comment calls Lemma_Base assumed, but the actual declaration is a theorem; its proof and final axiom report, not that stale prose, determine trust status.

## Existing PR and current API

[PR6371](https://github.com/google-deepmind/formal-conjectures/pull/6371) is open at head f1305094dbb417e3eb6bfa3599eb81244014f218. Its main statement matches the endpoint, and its stronger two variants are placeholders. The [review request](https://github.com/google-deepmind/formal-conjectures/pull/6371#discussion_r4057838049) asks to share the general graph proportion and list-coloring definitions.

The CURRENT repository already has `SimpleGraph.IsKChoosable` and `SimpleGraph.listChromaticNumber` in ForMathlib/Combinatorics/SimpleGraph/Coloring/List.lean; do not duplicate or move them again. Their bodies match the upstream Erdos753 definitions. A minimal shared real-valued graph-proportion API remains useful. Mathlib already has `SimpleGraph.binomialRandom` and `ProbabilityTheory.uniformOn`; a proposed elementary counting wrapper should be documented as the uniform finite-graph proportion, not presented as a new probability construction.
