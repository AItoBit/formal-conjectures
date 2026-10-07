/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil

/-!
# Erdős Problem 381

*References:*
- [erdosproblems.com/381](https://www.erdosproblems.com/381)
- [Er44] Erdős, P., On highly composite numbers. J. London Math. Soc. (1944), 130-133.
- [Ni71] Nicolas, J.-L., Répartition des nombres hautement composés de Ramanujan.
  Canadian J. Math. (1971), 116-130.
-/

@[expose] public section

open Filter Real

namespace Erdos381

/--
A positive integer $n$ is highly composite if $\tau(m) < \tau(n)$ for all $m < n$, where
$\tau(m)$ counts the divisors of $m$.
-/
def HighlyComposite (n : ℕ) : Prop :=
  0 < n ∧ ∀ m < n, m.divisors.card < n.divisors.card

instance : DecidablePred HighlyComposite := fun n ↦ by
  unfold HighlyComposite
  infer_instance

/-- $Q(x)$ counts the highly composite numbers in $[1, x]$. -/
noncomputable def Q (x : ℝ) : ℕ :=
  ((Finset.Icc 1 ⌊x⌋₊).filter HighlyComposite).card

@[category test, AMS 11]
theorem not_highlyComposite_zero : ¬ HighlyComposite 0 := by
  decide

@[category test, AMS 11]
theorem highlyComposite_one : HighlyComposite 1 := by
  decide +kernel

@[category test, AMS 11]
theorem highlyComposite_twelve : HighlyComposite 12 := by
  decide +kernel

@[category test, AMS 11]
theorem not_highlyComposite_ten : ¬ HighlyComposite 10 := by
  decide +kernel

/-- The highly composite numbers up to $12$ are $1, 2, 4, 6, 12$. -/
@[category test, AMS 11]
theorem Q_twelve : Q 12 = 5 := by
  simp only [Q, Nat.floor_ofNat]
  decide +kernel

/-- There are infinitely many highly composite numbers. -/
@[category API, AMS 11]
theorem infinite_highlyComposite : {n | HighlyComposite n}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun N ↦ ?_
  have hex : ∃ n : ℕ, N < n.divisors.card :=
    ⟨2 ^ N, by simp [Nat.divisors_prime_pow Nat.prime_two]⟩
  have hN : N < (Nat.find hex).divisors.card := Nat.find_spec hex
  refine ⟨Nat.find hex, ⟨by grind [Nat.divisors_zero, Finset.card_empty], fun m hm ↦ ?_⟩,
    hN.trans_le (Nat.card_divisors_le_self _)⟩
  exact (not_lt.mp (Nat.find_min hex hm)).trans_lt hN

/--
A number $n$ is highly composite if $\tau(m) < \tau(n)$ for all $m < n$, where $\tau(m)$ counts
the divisors of $m$. Let $Q(x)$ count the highly composite numbers in $[1, x]$. Is it true that
$Q(x) \gg_k (\log x)^k$ for every $k \geq 1$?

The answer is no. Nicolas [Ni71] proved that $Q(x) \ll (\log x)^{O(1)}$.
-/
@[category research solved, AMS 11]
theorem erdos_381 : answer(False) ↔ ∀ k : ℕ, 1 ≤ k →
    (fun x : ℝ ↦ log x ^ k) =O[atTop] fun x ↦ (Q x : ℝ) := by
  sorry

/-- Erdős [Er44] proved that $Q(x) \gg (\log x)^{1 + c}$ for some constant $c > 0$. -/
@[category research solved, AMS 11]
theorem erdos_381.variants.lower_bound : ∃ c > (0 : ℝ),
    (fun x : ℝ ↦ log x ^ (1 + c)) =O[atTop] fun x ↦ (Q x : ℝ) := by
  sorry

/-- Nicolas [Ni71] proved that $Q(x) \ll (\log x)^{O(1)}$. -/
@[category research solved, AMS 11]
theorem erdos_381.variants.upper_bound : ∃ C : ℝ,
    (fun x : ℝ ↦ (Q x : ℝ)) =O[atTop] fun x ↦ log x ^ C := by
  sorry

end Erdos381
