# Negative answer to the explicit asymptotic question in Erdős problem 791

This development proves **g(n) is not asymptotic to 2 sqrt(n)**. It does not
determine the sharp asymptotic constant or resolve the full estimation problem.
The negative answer is known: Mrose (1979). We formalize the simpler
seven-segment presentation in Kohonen (2017), Example 2.

## Exact statement

`IsBasis n A` means `A` is a finite subset of the natural interval `[0,n]`
and every `m <= n` equals `a+b` for members of `A`. Repeated summands are
allowed. The necessary zero counts toward cardinality. `g n` is the least
possible full cardinality, implemented using `Nat.find` with a proved witness.

The final theorem `Erdos791.not_erdos_791` has no assumptions and proves
that `g(n)/sqrt(n)` does not tend to 2 at infinity. This is the usual negative
answer to `g(n) ~ 2 sqrt(n)`. In particular, the definition is not replaced
by a convenient proxy or an unspecified function.

## Mathematical proof

For an integer t >= 2, put V=[0,t], H={t i:0<=i<t}, and
S={(t+1)i:0<=i<t}. Take the union of V translated by 0,6t^2,10t^2;
H translated by 0,t^2,2t^2; and S translated by 3t^2.
The resulting A has at most 7(t+1) elements.

Both V+H and V+S cover Q=[0,t^2-1], by division by t and t+1 respectively.
For P=H+S, P union (P+t^2) covers Q+t^2. To see this, write r=a t+b<t^2.
If b>a, take j=b and i=t+a-b; then t i+(t+1)j=t^2+r.
If b<=a, take j=b and i=a-b; then t i+(t+1)j+t^2=t^2+r.
In both cases i,j<t.

The V+H and V+S translates cover blocks 0,1,2,3,6,...,13, where block q
means Q+q t^2. The H+S translates occur at blocks 3,4,5; the preceding
parallelogram fact fills blocks 4 and 5. Thus A+A covers [0,14t^2-1].
Filtering A by that endpoint preserves every representation, since both
summands are nonnegative. Consequently g(14t^2-1)<=7(t+1).

Suppose g(n)/sqrt(n) tends to 2. Beyond some N it exceeds 39/20.
Choose t=N+100 and n=14t^2-1, so n>=N and sqrt(n)>=(37/10)t.
Then g(n)>(39/20)(37/10)t=7.215t, while g(n)<=7t+7.
These inequalities contradict t>=100.

## Files and verification

- `Construction791.lean`: elementary segment witnesses, cardinality and coverage.
- `Endpoint791.lean`: the exact minimum and the analytic contradiction lemma.
- `Main791.lean`: discharges the construction hypothesis and proves the result.

All three modules compiled with Lean 4.33.0 and canonical Mathlib commit
db584cd6d46c92f209a44c0f1c829460d327499d. All seven printed axiom reports
contain only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`,
`admit`, custom axiom, `unsafe`, or `native_decide` occurs in the proof sources.
An independent agent audited the correspondence with Kohonen's construction,
the source problem, the quantifiers, zero, and the filtering argument.

To reproduce: `lake update`, `lake exe cache get Mathlib`, then `python verify.py`.
The script compiles the three modules sequentially. `lake build Main791` also
builds the development. See `verification.log` and `source-hashes.json`.

## Sources and provenance

- Erdős problem 791: https://www.erdosproblems.com/791
- Jukka Kohonen, *An improved lower bound for finite additive 2-bases*,
  J. Number Theory 174 (2017), 518-524. https://arxiv.org/abs/1606.04770
  Example 2 supplies the seven-segment construction used here.
- Arnulf Mrose, *Untere Schranken für die Reichweiten von Extremalbasen
  fester Ordnung*, Abh. Math. Sem. Univ. Hamburg 48 (1979), 118-124.
  Original disproof, credited as prior work; no novelty claim.

The Lean code was generated and checked using Codex with a construction agent
and a separate source/proof auditor. This is a new formalization of an existing
mathematical argument, not a new solution of the open sharp-estimate problem.
Code license: Apache-2.0. Paper copyrights are unaffected.

Research coverage: 5 works discovered, 1 screened, 1 full-text reviewed for
the relevant argument and proof structure, 1 used in this formal proof;
1 unique arXiv paper. This is not a completed 100-paper literature campaign.
