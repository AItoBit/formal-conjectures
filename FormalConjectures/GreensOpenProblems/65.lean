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
# Ben Green's Open Problem 65

Is there $c > 0$ with the following property: whenever $A \subseteq [N]$ is a set of size
$N^{1-c}$, $A - A$ contains a nonzero square? What about $A - A$ containing a prime minus one?

Both questions were originally considered by Sárközy. The question for squares is open. The best
known bound is $|A| > Ne^{-c\sqrt{\log N}}$, due to Green and Sawhney. In the other direction
Ruzsa [Ru84] showed that one cannot take $c > 0.267$.

The question for shifted primes was answered positively by Green [Gr24], who obtained an upper
bound of shape $|A| \ll N^{1-c}$ for some $c > 0$. Thorner and Zaman [ThZa23] showed that
$c = 10^{-18}$ is permissible.

*References:*
- [Ben Green's Open Problem 65](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.65)
- [Ru84] Ruzsa, I. Z., *Difference sets without squares*. Period. Math. Hungar. 15 (1984),
  205--209.
- [Gr24] Green, B., *On Sárközy's theorem for shifted primes*. J. Amer. Math. Soc. 37 (2024),
  1121--1201. https://arxiv.org/abs/2206.08001
- [ThZa23] Thorner, J. and Zaman, A., *An explicit version of Bombieri's log-free density estimate
  and Sárközy's theorem for shifted primes*. Forum Math. (2023).
  https://doi.org/10.1515/forum-2023-0091
-/

@[expose] public section

open Filter

open scoped Pointwise

namespace Green65

/-- `d` is a nonzero square. -/
def IsNonzeroSquare (d : ℤ) : Prop := d ≠ 0 ∧ IsSquare d

/-- `d` is one less than a prime. -/
def IsPrimeSubOne (d : ℤ) : Prop := ∃ p : ℕ, p.Prime ∧ d = (p : ℤ) - 1

@[category test, AMS 11]
theorem isNonzeroSquare_four : IsNonzeroSquare 4 := ⟨by norm_num, 2, by norm_num⟩

@[category test, AMS 11]
theorem not_isNonzeroSquare_zero : ¬ IsNonzeroSquare 0 := fun h => h.1 rfl

@[category test, AMS 11]
theorem isPrimeSubOne_one : IsPrimeSubOne 1 := ⟨2, Nat.prime_two, by norm_num⟩

@[category test, AMS 11]
theorem isPrimeSubOne_two : IsPrimeSubOne 2 := ⟨3, Nat.prime_three, by norm_num⟩

/--
`PowerSavingAt c P` says that for all sufficiently large $N$, every $A \subseteq [N]$ with
$|A| \geq N^{1-c}$ satisfies `P d` for some `d` in the difference set $A - A$.

The restriction to large $N$ is needed. For $N = 1$ the only nonempty subset of $[N]$ is
$\{1\}$, whose difference set is $\{0\}$, so without it the statement would be false for every
`c` and every `P` with `¬ P 0`.
-/
def PowerSavingAt (c : ℝ) (P : ℤ → Prop) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ A ⊆ Finset.Icc (1 : ℤ) (N : ℤ),
    (N : ℝ) ^ (1 - c) ≤ A.card → ∃ d ∈ A - A, P d

/-- `PowerSaving P` says that `PowerSavingAt c P` holds for some `c > 0`. -/
def PowerSaving (P : ℤ → Prop) : Prop := ∃ c > (0 : ℝ), PowerSavingAt c P

/--
Is there $c > 0$ with the following property: whenever $A \subseteq [N]$ is a set of size
$N^{1-c}$, $A - A$ contains a nonzero square?
-/
@[category research open, AMS 11]
theorem green_65 : answer(sorry) ↔ PowerSaving IsNonzeroSquare := by
  sorry

/--
The same question for shifted primes: whenever $A \subseteq [N]$ is a set of size $N^{1-c}$, does
$A - A$ contain $p - 1$ for some prime $p$?

Green [Gr24] showed that it does, for some $c > 0$.
-/
@[category research solved, AMS 11]
theorem green_65.variants.shifted_primes : answer(True) ↔ PowerSaving IsPrimeSubOne := by
  sorry

/--
Ruzsa [Ru84] showed that one cannot take $c > 0.267$ for squares.

The elementary case $c \geq 1/2$ is `green_65.variants.not_powerSavingAt_half`.
-/
@[category research solved, AMS 11]
theorem green_65.variants.ruzsa_bound {c : ℝ} (hc : 0.267 < c) :
    ¬ PowerSavingAt c IsNonzeroSquare := by
  sorry

/--
No exponent $c \geq 1/2$ works for squares.

For a prime $p$ the progression $\{1 + kp : 0 \leq k < p\}$ is a subset of $[p^2]$ of size
$p = (p^2)^{1/2}$. Each of its differences is $(i - j)p$ with $|i - j| < p$, and a nonzero square
of this form would be divisible by $p^2$, forcing $|i - j| \geq p$.

This is the special case $c \geq 1/2$ of `green_65.variants.ruzsa_bound`.
-/
@[category research solved, AMS 11]
theorem green_65.variants.not_powerSavingAt_half {c : ℝ} (hc : 1 / 2 ≤ c) :
    ¬ PowerSavingAt c IsNonzeroSquare := by
  sorry

end Green65
