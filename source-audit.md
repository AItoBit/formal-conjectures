# Erdős 797 independent source and interface audit

Date: 2026-10-25. Scope: source fidelity and static proof-interface audit; full compilation is assigned separately and is not claimed here.

## Primary question and status

Read the live [problem](https://www.erdosproblems.com/797) and [forum](https://www.erdosproblems.com/forum/thread/797) by HTTP. The forum has zero comments. The question defines the maximal acyclic chromatic number at maximum degree exactly d, asks for estimates, and particularly asks whether it is o(d²). Properness and absence of two-coloured cycles are both explicit. The affirmative result is attributed to Alon–McDiarmid–Reed (1991).

## Primary paper reading

Source: [Acyclic Coloring of Graphs](https://web.math.princeton.edu/~nalon/PDFS/Publications2/Acyclic%20colouring%20of%20graphs.pdf), Alon, McDiarmid, Reed, Random Structures and Algorithms 2 (1991), 277–288.

Read the extracted text for the introduction and principal Section 2 argument, plus the Section 3 and 4 statements/discussion. This is **partial_text_reviewed**, not a fully checked transcription: several displayed formulas are damaged by PDF OCR.

Section 1 explicitly restricts to finite undirected simple graphs. Section 2 proves the O(d^(4/3)) upper bound by the nonsymmetric local lemma: avoid monochromatic edges, alternating length-four paths, certain bichromatic 4-cycles, and monochromatic pairs with many common neighbours. Its random-graph lower construction rules out small palettes by counting paired vertices within colour classes and forcing bichromatic 4-cycles; the resulting lower order is d^(4/3)/(log d)^(1/3). Section 3 studies excluded bipartite configurations and derives an edge-colouring consequence. Section 4 discusses the remaining logarithmic gap and other questions. No claim about the latter variants is required for problem 797's particular question.

## Exact Lean definitions

Audited `src/latest/ErdosProblems/Erdos797.lean` at plby/lean-proofs commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`.

- `IsAcyclicColoring G c` conjoins properness with prohibition of a pair of colours covering the support of any closed walk satisfying `IsCycle`. This quantifies over genuine graph cycles, not every closed walk. It does not merely forbid induced cycles, even cycles, or 4-cycles. Repeating the initial vertex in the support is harmless. The two colours may coincide, which expresses “at most two”; properness already rules out monochromatic cycles.
- `AcyclicBound d k` quantifies over every natural n and every simple graph on `Fin n` with maximum degree at most d. A map to `Fin k` means k available colours; surjectivity is not required. This is the usual “at most k colours” property.
- Coding finite graphs on `Fin n` loses no finite graph up to relabelling. The statement is not asserting an infinite-graph extension. Its type quantification therefore has no universe-sized supremum issue.
- Maximum degree at most d and exactly d give the same extremal palette number: adjoin a disjoint star K_(1,d) to any graph of degree at most d, then restrict a colouring of the resulting graph. The opposite comparison is immediate. For d=0 all graphs involved are edgeless. This reduction is a mathematical fidelity justification; I did not locate a separately named Lean theorem formalizing this exact-degree equivalence.

## Nonvacuity and small cases

The extremal definition is `sInf {k : ℕ | AcyclicBound d k}`, not `Nat.find`. The file proves `UpperBound.acyclicBound_cubeCeil d` for every d, giving a member `64 * (Nat.nthRoot 3 d + 1)^4`. Thus this set is nonempty, including at d=0. `LowerBound.extremalAcyclicNumber_spec` applies `Nat.sInf_mem` to that witness. The lower-bound argument consequently cannot exploit an empty-set infimum.

`Fin 0` permits the empty graph; `Fin 1` supplies a nonempty edgeless graph. These conventions do not force the universal palette to zero at degree zero. The upper numerical cube bound explicitly assumes d≥1. `Nat.find` occurs later only in `scaleIndex`, supplied with a proved `exists_scale_above d`; it has no unproved existence premise.

## Endpoint and scope

`erdos_797` has no additional graph or probabilistic hypotheses. Its conjunction asserts:

1. For all d≥1, f(d)^3 ≤ 1024^3 d^4.
2. For every d above the explicit `LowerBound.lowerD 1` threshold, d^4 ≤ 2^67 (Nat.log 2 d) f(d)^3.
3. The real-cast f is little-o of d² at infinity.

Positive cube roots and comparison of integer base-two logarithm with natural logarithm give the reported upper/lower asymptotic estimates. The lower bound is eventually for every d, not merely on a subsequence: the file explicitly interpolates adjacent scales using monotonicity. The constants differ from the original paper but preserve its asymptotic orders. The third conjunct exactly answers the particular question affirmatively. The logarithmic gap between the first two estimates remains; this is not an exact asymptotic equivalent or a resolution of that stronger question.

The inspected source uses Mathlib/tactic imports and contains no lexical `sorry`, `admit`, explicit axiom declarations, `native_decide`, or unsafe declarations. This scan is supplementary; the separate compiler and axiom audit determine kernel-verification status.

## Existing PR and useful follow-up

[PR #6340](https://github.com/google-deepmind/formal-conjectures/pull/6340) is open, not draft, and labelled awaiting-author at reviewed head `52d885d781f531bdc7369e7e0e151ad438586c91`. It already adds the two estimates and the affirmative little-o statement, linking the same proof and giving an extremal-definition bridge.

The sole fetched inline review is [mo271's September 20 comment](https://github.com/google-deepmind/formal-conjectures/pull/6340#discussion_r4057830947): put the standard acyclic-colouring/chromatic-number notions under a shared `Coloring/` module and phrase the former using `G.Coloring C`. This is a meaningful reusable-API improvement. A bundled proper colouring makes properness structural; its extra acyclicity predicate must still forbid all bichromatic cycles. A compatibility equivalence with the upstream function predicate should be proved before reusing the external theorem. No duplicate problem-797 statement submission is needed to address that review.

Mathematical attribution remains Alon–McDiarmid–Reed; the source credits Codex and GPT-5.6 Sol/OpenAI Codex for formalization. This is existing-proof verification, not a novelty claim.
