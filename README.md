# Erdős 792: verified classical bounds and the zero convention

**Partial result. The full sharp-estimate problem is not solved.** This package
reproduces and strengthens an existing ATLAS formalization of a classical lower
bound and proves an elementary upper bound and an exact convention bridge.
It does not formalize Bedert's logarithmic-logarithmic improvement or the deep
Eberhard--Green--Manners leading-term upper bound.

## Exact functions and source fidelity

The website asks for the largest universally guaranteed sum-free subset in
every n-element set of integers. Repeated summands are allowed: a+a=b is forbidden.
The website allows zero, while the classical literature excludes it.

`Definitions792.lean` defines both conventions using a bounded maximum:

- `Erdos792.f n`: zero is allowed in the ambient n-element integer set.
- `Erdos792.fNonzero n`: the ambient set excludes zero.
- `SumFree B`: for every a,b in B, a+b is not in B.
- `Guarantees n k`: for every ambient A, some B contained in A has the
  sum-free property and cardinality at least k. The choice of B depends on A.

The search bound n is justified using the n-element interval [1,n]. Zero is
always a guaranteed threshold, including n=0, so no empty-search default is
used as mathematics. `f_spec` and the maximality lemmas verify the definitions.

The exact, fully proved convention bridge is

    f (n+1) = fNonzero n.

Forwards, add zero to a nonzero n-set; a sum-free subset must omit zero.
Backwards, remove zero from an arbitrary (n+1)-set and select an n-element
subset of what remains. This also proves f(0)=f(1)=0. The apparent universal
lower bound n/3 therefore needs the small-input exception in the literal domain.

| Informal clause | Formal representation | Edge cases |
|---|---|---|
| finite integer ambient set | `A : Finset ℤ`, `A.card = n` | negative inputs retained |
| conventional exclusion of zero | `0 ∉ A` | explicit, never silently inserted |
| no a+b=c | `SumFree`, equivalently repository `IsSumFree` | a=b is allowed |
| subset chosen for each A | `∀ A, ... → ∃ B ⊆ A, ...` | no global choice of B |
| maximum universal guarantee | `Nat.findGreatest ... n`, with proved API | empty and singleton checked |

## Verified theorems

1. `Erdos792.strict_nonzero_bound`: every nonempty nonzero integer set A has
   sum-free B contained in A with |A| < 3|B|. For integral cardinalities this
   is the known Alon--Kleitman bound |B| >= (|A|+1)/3, with no floor weakening.
2. `Erdos792.literal_lower_bound`: for every n>=2 and every n-element integer
   set A, including sets containing zero, some sum-free B has n <= 3|B|.
3. `Erdos792.literal_upper_bound`: for every n there exists an n-element A such
   that every sum-free B contained in A has 2|B| <= n.
4. `Erdos792.f_succ`: the exact convention shift above.
5. The function bounds `literal_f_lower` and `literal_f_upper` give
   n/3 <= f(n) <= n/2 for n>=2; the upper bound holds also at n=0,1.

The lower construction takes a prime p=3m+2 larger than all absolute values
in A. The residues R={m+1,...,2m+1} are sum-free modulo p: adding two such
residues falls above R before wraparound or below R after wraparound.
For each multiplier t, the pullback B_t is sum-free. Each fixed nonzero a has
exactly |R| multipliers with ta in R. Consequently

    sum_t |B_t| = |A| |R|,    3|R| = p+1 > p.

If all 3|B_t| were at most |A|, summing would contradict this identity for
nonempty A. Thus one B_t has strictly more than |A|/3 elements.

For the upper bound, let M be the largest element of a nonempty sum-free
S contained in [1,m]. The reflection M-S is disjoint from S, since an overlap
would give x+y=M in S. Both sets lie in [0,m], so 2|S| <= m+1.
The literal-domain witness is [0,n-1]; its sum-free subsets omit zero.

## Remaining mathematical target

The known leading term is f(n) ~ n/3. Bedert proves an eventual lower bound
n/3+c log log n, while Eberhard--Green--Manners give n/3+o(n) from above.
The sharp order of f(n)-n/3 is unresolved in the primary sources checked.

`Target792.lean` contains only proposition definitions for a proposed sharp
excess order, the known leading term, and Bedert's bound. These definitions
assert no proofs, supply no hidden hypotheses, and are not used to prove any
of the classical theorems. No full solution is claimed by compilation.

## Sources and provenance

- Problem and complete supplied forum discussion:
  https://www.erdosproblems.com/792 and /forum/thread/792 (checked 2026-10-25).
- P. Erdős, *Extremal problems in number theory*, Proc. Sympos. Pure Math. VIII
  (1965), 181–189, Theorem 2. https://www.renyi.hu/~p_erdos/1965-02.pdf
- N. Alon and D. J. Kleitman, *Sum-free subsets*, A Tribute to Paul Erdős
  (1990), 13–26, Propositions 1.1–1.2.
  https://web.math.princeton.edu/~nalon/PDFS/Publications2/Sum-free%20subsets.pdf
- S. Eberhard, B. Green and F. Manners, *Sets of integers with no large sum-free
  subset*, Ann. of Math. 180 (2014), 621–652; arXiv:1301.4579v3 (2026 correction).
- B. Bedert, *Large sum-free subsets of sets of integers via L¹-estimates for
  trigonometric series*, arXiv:2502.08624v1 (2025).
- Ben Green's *100 open problems*, December 2025 update, Problem 1.
- Adapted ATLAS source: facebookresearch/atlas-lean, commit
  7f27c3ad16289716586daf311cf568bcae4160d5, archived v1 Chapter2/SumFree.lean.
  The original theorem used natural division and formally guaranteed only the
  floor of n/3. The modified proof gives the genuine strict inequality.

Meta's copyright and original v1 LICENSE, including its introductory notice,
are retained. See NOTICE for changes. This is source-based formalization and
verification with OpenAI Codex and actual independent audit/construction
agents; no mathematical novelty or human expert peer review is asserted.

## Verification

Pinned Lean: leanprover/lean4:v4.35.0, compiler commit
eb6cafb7290e8bd5f2937522d8d804f58f02bafc.
Pinned Mathlib: 56a005855ea17e0b0958f73ec801ae140b0a1679.

Commands, after installing the exact Lean toolchain:

```
lake exe cache get
lake --wfail build Definitions792 Construction792 Upper792 Main792 Target792
lake env lean Audit792.lean
python verify.py
```

The complete five-module build succeeded with warnings treated as errors.
The separate audit prints the three PR endpoints and axiom dependencies.
All principal proved theorems use only propext, Classical.choice and Quot.sound.
There are no proof holes, new mathematical axioms, native_decide or unsafe
verification bypasses. Logs and source hashes are included. Standard axioms
are genuine dependencies; this is not an axiom-free claim.

Independent mathematical/source-fidelity audit passed, including the repository
IsSumFree definition, all three PR endpoints, repeated summands, both zero
conventions, reflection, empty sets and smallest inputs.

## Literature coverage

The relevant complete short proofs in Erdős pp.186–187 and Alon--Kleitman p.15
were checked from primary full text. The deep papers were screened in their
introductions and theorem statements, not completely proof-audited. This is
not a completed 100-paper research campaign; the separate research checkpoint
records coverage and the exact unresolved target.
