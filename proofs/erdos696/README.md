# Erdős 696 complete-proof reproduction

Status: verification pending. This branch is a verification project, not a claim
that a new solution has been found. No upstream pull request should claim a
complete formal proof until the final build and axiom audit succeed.

The mathematical source is the external development at
[Jayyhk/erdos-lean, revision 9c9f6d3](https://github.com/Jayyhk/erdos-lean/blob/9c9f6d35da233a088e78be9dd418d2c0d17f31cc/problems/696/Erdos696.lean).
It credits David Turturean, plby/lean-proofs, and the BoundedGaps library of
frenzymath/FormalPantheon. The 61,900-line source is downloaded during verification;
it is not redistributed by this branch. Its SHA-256 and normalized mathematical
body hash are checked before compilation. Only imports and module visibility are
adapted to reduce import memory use. This branch uses the repository's pinned
Lean 4.33.1 and Mathlib revision, rather than silently changing its dependencies.

`Bridge.lean` compares the external chain definitions with the current repository
definitions and transfers the ratio limit to the exact negative answer stated in
Formal Conjectures. It handles the differing H(1) convention through a finite
exception bound. `Complete.lean` supplies the external theorem to this bridge and
rejects every transitive axiom except `propext`, `Classical.choice`, and `Quot.sound`.

The external theorem proves all three sharp estimates: h(n) has normal order
(1/2) log_* n, H(n) has normal order log_* n, and their ratio tends to two in
natural density. These are attributed existing results, not new results of this
verification work.

Run the commands in `.github/workflows/verify-erdos696.yml` to reproduce the check.
Generated source, compiled artifacts, and logs are not intended for the upstream
statement repository. The final upstream contribution should follow its external
`formal_proof` convention for long proofs.
