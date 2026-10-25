# Proof of the original little-o assertion

This explains the Ramsey and heavy-color argument in the reproduced Lean proof.
The affirmative result is already known; no novelty is claimed. The displayed
cutoff below is a convenient mathematical choice, rather than a claim that its
rounding is identical to the source's `r_val`.

Let `R(r,q)` be the least integer such that every graph with that many vertices
contains a clique of size `r` or an independent set of size `q`.

## A deterministic list-coloring bound

Suppose `G` has `n` vertices and has no clique of size `r`, where `r ≥ 2`.
For any positive integer `q`, put `R = R(r,q)` and

    k = floor(n/q) + R + 1.

We show that every assignment of lists of `k` colors admits a proper coloring.

Whenever a color occurs in the lists of at least `R` uncolored vertices,
Ramsey's theorem supplies `q` independent vertices among those vertices.
Color these vertices with that color, delete the vertices, and remove the used
color from all remaining lists. Repeat until no such color remains. Every
stage deletes `q` vertices, so there are at most `floor(n/q)` stages.
Consequently each remaining list has at least `R+1` colors.

At termination each color occurs in fewer than `R` remaining lists. For any
set `S` of remaining vertices, count incidences between `S` and its available
colors. There are at least `(R+1)|S|` incidences and at most `R|U(S)|`, where
`U(S)` is the union of the lists at `S`. Since `R ≥ 1`, this implies
`|U(S)| ≥ |S|`. Hall's theorem therefore supplies distinct representatives for
all the remaining lists. Assign those colors to the remaining vertices.

This is proper: each earlier color class is independent, different stages use
different colors, and all colors assigned at the end are distinct and were
never used earlier. Thus

    chi_list(G) ≤ floor(n/q) + R(r,q) + 1.                 (1)

The empty remainder causes no exception; Hall's condition is then vacuous.

## A single sublinear threshold

For large `n`, choose `r(n) = ceil(3 log₂ n)`; set it to at least `2` for small
`n`. The elementary Ramsey recurrence gives

    R(r,q) ≤ binomial(r+q-2,q-1).

For each fixed positive `q`, it follows that `R(r(n),q)` is bounded by a
polynomial in `log n`, and hence `R(r(n),q)/n → 0`.

Define the deterministic integer threshold

    b(n) = min_{q ≥ 1} [floor(n/q) + R(r(n),q) + 1].

This minimum exists because the set is a nonempty subset of the natural
numbers: `q=1` gives a value. For `n ≥ 1` and each fixed `q`,

    0 ≤ b(n)/n ≤ 1/q + R(r(n),q)/n + 1/n.

Given any positive epsilon, first choose `q` with `1/q < epsilon/2`, then take
`n` large enough to make the other two terms smaller than `epsilon/2`.
Therefore `b(n)/n → 0`. By (1), every graph with no clique of size `r(n)` has
list chromatic number at most `b(n)`.

## Almost all labelled graphs

In the uniform random graph on `n` labelled vertices, each edge is present
independently with probability one half. A union bound gives

    Pr[there is an r-clique] ≤ binomial(n,r) 2^(-r(r-1)/2)
                            ≤ n^r 2^(-r(r-1)/2).

For `r = ceil(3 log₂ n)`, the base-two logarithm of the last expression is
`-(3/2)(log₂ n)^2 + O(log n)`, which tends to minus infinity. Thus the
probability of an `r(n)`-clique tends to zero. It follows that

    Pr[chi_list(G) ≤ b(n)] → 1,       b(n) = o(n).

This is the full original assertion. Quantitative improvements such as
`O(n log log n/log n)` or order `n/log n` are outside this argument's claimed
scope.

The Lean endpoint is `Erdos799.erdos_799`. `Erdos799Bridge.erdos_799` proves the
same result using the current shared list-coloring and graph-proportion APIs.
