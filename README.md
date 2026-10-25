# Erdős 795: reproduced complete proof and shared-definition bridge

This project reproduces an existing full proof of the original question:

    g(n) <= pi(n) + pi(sqrt(n)) + o(sqrt(n)/log(n)).

The informal result is due to Rushil Raghavan. The pinned upstream Lean file
credits Codex and GPT-5.6 Sol. This reproduction makes no novelty claim.

The 6,678-line upstream file is fetched by `prepare.py` with an exact SHA-256
check. It is not redistributed or relicensed here because no source license
was found in the pinned repository. Its permanent source is:
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos795.lean

Our `Statement795.lean` uses the same bounded `sSup` maximum and quantified
error function as open formal-conjectures PR #6338. `Bridge795.lean` proves
the exact target and the matching primes-and-squares lower bound. Its finite
predicate comes from the shared multiplicative/additive API proposed for 350
and 795. `g_eq` proves equivalence with the upstream powerset maximum.

The domain is [1,n]. Every subset, including the empty subset, participates.
Consequently 1 cannot belong to an admissible set. Empty intervals and n=0
are handled by the empty admissible set and the bound on its cardinality.
`Nat.sqrt` gives the exact prime-counting cutoff at the real square root.

## Reproduce

Install the exact toolchain in `lean-toolchain`, then run:

    python prepare.py
    lake exe cache get
    python verify.py

Pins: Lean 4.33.0, Mathlib db584cd6d46c92f209a44c0f1c829460d327499d.
The verifier builds the complete project and checks eight axiom reports.
No holes, additional mathematical axioms, unsafe code, or native_decide are
used in the delivered Lean sources. The standard axioms are propext,
Classical.choice, and Quot.sound. Existing statement-only placeholders in
formal-conjectures are not part of this complete proof project.

## Mathematical argument

The primes together with their squares give a set of size
pi(n)+pi(sqrt(n)): at each prime, the exponent encodes the two membership
bits as 0,1,2,3, so unique factorization recovers every subset.

For the upper bound, the upstream development partitions prime factors into
small, medium, and large ranges. A counting argument bounds the information
carried by the small-prime valuations. After deleting a controlled number
of elements, the remaining medium/large valuation vectors are distinct and
nonzero. They define a prime-factorization graph, with prime-square elements
accounted for separately. Alternating products around short circuits give
equal medium/large valuations; too many independent circuits contradict
the small-prime information bound. Delete those circuits, control the
remaining short odd cycles, and apply a proved graph growth bound.

This proves the explicit finite upper bound in
`card_le_primeCounting_add_sqrt_add_finiteError`. The explicit `finiteError`
is little-o of sqrt(n)/log(n), proved in `finiteError_isLittleO`. Squeezing
the signed excess between zero and this error gives
`erdos_795_signed_error_isLittleO`. Choose that signed excess as the error
function to obtain the precise conjecture in `Bridge795.erdos_795`.

Raghavan's paper proves the stronger O(n^(5/12)) error, but this Lean file
does not establish that stronger rate or the additional cube-root lower
correction. Those are not claimed as verified here.

Sources:
- https://www.erdosproblems.com/795
- https://www.erdosproblems.com/forum/thread/795
- https://arxiv.org/html/2501.02695v2
- https://github.com/google-deepmind/formal-conjectures/pull/6338

The literature checkpoint is separate from proof verification. The relevant
Raghavan paper was read across all substantive sections; the Studio default
100-paper campaign is incomplete. See the research checkpoint for counts.
