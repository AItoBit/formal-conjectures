# Erdős799: existing complete proof reproduced

The original question has an affirmative answer. There is a deterministic
function b(n)=o(n) such that the fraction of labelled graphs G on n vertices
with list chromatic number at most b(n) tends to one.

The list chromatic number quantifies over every assignment of k-element lists,
and requires a proper coloring chosen from those lists. All graph fractions
use the uniform distribution on labelled graphs, equivalently G(n,1/2).
This package reproduces the known solution; it makes no novelty claim.

See [Proof.md](Proof.md) for a complete mathematical argument for the original
little-o assertion, corresponding to the Ramsey/heavy-color route.

The pinned source proves the full original little-o question using a
logarithmic clique cutoff, finite Ramsey theory, heavy-color packing, Hall's
theorem and a slow diagonal Ramsey bound. Its exceptional graph density tends
to zero. It does not formalize the sharper quantitative Alon log-log bound,
AKS order n/log n, Kahn leading asymptotic, or sparse graph variants.

## Sources

- Problem: https://www.erdosproblems.com/forum/thread/799
- Alon1992: https://web.math.princeton.edu/~nalon/PDFS/choice.pdf
- Alon–Krivelevich–Sudakov1999: https://web.math.princeton.edu/~nalon/PDFS/colaks9.pdf
- Existing statement PR: https://github.com/google-deepmind/formal-conjectures/pull/6371
- Original source: https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos799.lean

## Reproduce

Install the exact toolchain, then run:

    python prepare.py
    lake exe cache get
    python verify.py

Lean4.33.0; Mathlib db584cd6d46c92f209a44c0f1c829460d327499d.
Ten original modules,5395lines, are fetched at an immutable commit and checked
against individual SHA256 hashes. They are not included in the public package
because their license notices differ. New files are Apache2.0.

The verifier builds the complete proof and checks the principal theorem and
bridges for axioms beyond propext, Classical.choice and Quot.sound. Delivered
Lean sources contain no proof holes or native_decide. The bridge uses the
current shared SimpleGraph list-coloring definitions rather than importing a
problem statement from formal-conjectures. Finite choosability witnesses
exclude empty-infimum shortcuts. See source-audit.md for the quantifier audit.

The separate literature campaign is incomplete. Reading relevant theorem and
proof sections is recorded as partial review, not full-paper review.
