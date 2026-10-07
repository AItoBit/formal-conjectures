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
import Mathlib
import FormalConjecturesForMathlib.Data.Nat.MaxPrimeFac

/-!
# Erdős Problem 368 — complete development in a single file

*How large is the largest prime factor `F(n)` of `n(n+1)`?*

**Status: the problem remains OPEN.** This file contains every definition and proof of the
project in one place:

* definitions of `F` and the two open conjectures (stated as `Prop`s, NOT asserted);
* the Pell-equation valuation lemma (`finite_pell_smooth`);
* Størmer's theorem (`finite_smooth_consecutive`) and Pólya's `F(n) → ∞` (`tendsto_F_atTop`);
* sanity checks of `F` on small values;
* the upper-side result: for every `δ > 0`, `F(n) ≤ n^δ` infinitely often
  (`frequently_F_le_rpow`);
* the summary theorem `erdos_368_verified`.

No `sorry`, `admit`, `axiom` or `native_decide` is used.
-/

/-! ######## Part: Statement ######## -/



/-!
# Erdős Problem 368: definitions and the open statements

*How large is the largest prime factor of `n(n+1)`?*

We define `F n`, the largest prime factor of `n(n+1)`, and record (as propositions, **without**
asserting them) the two precise quantitative statements quoted on the problem page:

* `Erdos368.ProbableTruth`: `F(n) ≫ (log n)²` for all `n` (stated as "probably true");
* `Erdos368.ErdosConjecture`: for every `ε > 0` there are infinitely many `n` with
  `F(n) < (log n)^(2+ε)` (conjectured by Erdős [Er76d]).

Both are open; nothing in this project proves or refutes them.
-/


namespace Erdos368

open Filter

/-- The largest prime factor of a natural number `m`; by convention it is `0` when `m` has no
prime factor (i.e. `m = 0` or `m = 1`, since `Nat.primeFactors 0 = ∅`). -/
def largestPrimeFactor (m : ℕ) : ℕ := m.primeFactors.sup id

/-- `F n` is the largest prime factor of `n(n+1)`.  For `n ≥ 1` this is a genuine prime;
`F 0 = 0` by the convention of `largestPrimeFactor`. -/
def F (n : ℕ) : ℕ := largestPrimeFactor (n * (n + 1))

/-- "The truth is probably `F(n) ≫ (log n)²` for all `n`": there is an absolute constant
`c > 0` with `c (log n)² ≤ F(n)` for every `n ≥ 1`.  **Open; not asserted.** -/
def ProbableTruth : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → c * Real.log n ^ 2 ≤ (F n : ℝ)

/-- Erdős's conjecture [Er76d]: for every `ε > 0` there are infinitely many `n` with
`F(n) < (log n)^(2+ε)`.  **Open; not asserted.** -/
def ErdosConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop, (F n : ℝ) < Real.log n ^ (2 + ε)

end Erdos368

/-! ######## Part: PellValuation ######## -/



/-!
# `p`-adic valuations along the powers of a Pell solution

For a solution `b` of `x² - d y² = 1` and a prime `p ∣ b.y`, we show the lifting-the-exponent
identity `v_p((b^m).y) = v_p(b.y) + v_p(m)` (`m ≥ 1`).  From it we deduce that for a solution
`a` with `a.x > 1`, `a.y > 0`, the `y`-coordinates of the powers `a^k` are `B`-smooth for only
finitely many `k`.
-/


namespace Erdos368

open Pell

/-- `Smooth B m`: every prime factor of the natural number `m` is at most `B`.
(Note `Smooth B 0` is false, since every prime divides `0`.) -/
def Smooth (B m : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ m → p ≤ B

variable {d : ℤ}

/-- Expansion of the powers of a Pell solution modulo `b.y ^ 2`. -/
lemma pow_succ_expand (b : Solution₁ d) (j : ℕ) :
    ∃ Q R : ℤ, (b ^ (j + 1)).y = b.y * ((j + 1 : ℤ) * b.x ^ j + b.y ^ 2 * Q) ∧
      (b ^ (j + 1)).x = b.x ^ (j + 1) + b.y ^ 2 * R := by
  induction j with
  | zero => exact ⟨0, 0, by simp, by simp⟩
  | succ j ih =>
    obtain ⟨Q, R, hy, hx⟩ := ih
    refine ⟨R + Q * b.x, R * b.x + d * (j + 1) * b.x ^ j + d * b.y ^ 2 * Q, ?_, ?_⟩
    · rw [pow_succ, Solution₁.y_mul, hy, hx]; push_cast; ring
    · rw [pow_succ, Solution₁.x_mul, hy, hx]; ring

/-- If `p ∣ b.y` then `p ∤ b.x`. -/
lemma not_dvd_x_of_dvd_y (b : Solution₁ d) {p : ℕ} (hp : p.Prime) (h : (p : ℤ) ∣ b.y) :
    ¬ (p : ℤ) ∣ b.x := by
  intro hx
  have h1 : (p : ℤ) ∣ b.x ^ 2 - d * b.y ^ 2 :=
    dvd_sub (dvd_pow hx two_ne_zero) (dvd_mul_of_dvd_right (dvd_pow h two_ne_zero) _)
  rw [b.prop] at h1
  exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h1)

/-- Lifting the exponent, coprime step. -/
lemma padicValInt_y_pow_of_not_dvd (b : Solution₁ d) {p : ℕ} [hp : Fact p.Prime]
    (h : (p : ℤ) ∣ b.y) (hy : b.y ≠ 0) {j : ℕ} (hj : ¬ p ∣ j) :
    (b ^ j).y ≠ 0 ∧ padicValInt p (b ^ j).y = padicValInt p b.y := by
  obtain _ | j := j
  · exact absurd (dvd_zero p) hj
  obtain ⟨Q, R, hyj, -⟩ := pow_succ_expand b j
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hc : ¬ (p : ℤ) ∣ ((j + 1 : ℤ) * b.x ^ j + b.y ^ 2 * Q) := by
    intro hc
    have h2 : (p : ℤ) ∣ (j + 1 : ℤ) * b.x ^ j :=
      (dvd_add_left (dvd_mul_of_dvd_left (dvd_pow h two_ne_zero) _)).mp hc
    rcases hpp.dvd_or_dvd h2 with h3 | h3
    · exact hj (by exact_mod_cast h3)
    · exact not_dvd_x_of_dvd_y b hp.out h (hpp.dvd_of_dvd_pow h3)
  have hc0 : ((j + 1 : ℤ) * b.x ^ j + b.y ^ 2 * Q) ≠ 0 := fun h0 => hc (h0 ▸ dvd_zero _)
  refine ⟨hyj ▸ mul_ne_zero hy hc0, ?_⟩
  rw [hyj, padicValInt.mul hy hc0, padicValInt.eq_zero_of_not_dvd hc, add_zero]

/-- Lifting the exponent, the step `b ↦ b ^ p`. -/
lemma padicValInt_y_pow_self (b : Solution₁ d) {p : ℕ} [hp : Fact p.Prime]
    (h : (p : ℤ) ∣ b.y) (hy : b.y ≠ 0) :
    (b ^ p).y ≠ 0 ∧ padicValInt p (b ^ p).y = padicValInt p b.y + 1 := by
  obtain ⟨j, hj⟩ : ∃ j, p = j + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.out.one_lt.le).symm⟩
  obtain ⟨Q, R, hyj, -⟩ := pow_succ_expand b j
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  set c := ((j + 1 : ℤ) * b.x ^ j + b.y ^ 2 * Q) with hcdef
  have hyp : (b ^ p).y = b.y * c := by rw [hj]; exact hyj
  have hcast : ((j + 1 : ℤ)) = (p : ℤ) := by rw [hj]; push_cast; ring
  have hpy2 : (p : ℤ) ^ 2 ∣ b.y ^ 2 * Q := dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd h 2) _
  have hc1 : (p : ℤ) ^ 1 ∣ c := by
    rw [hcdef, hcast, pow_one]
    exact dvd_add (dvd_mul_right _ _) (dvd_trans (dvd_pow_self _ two_ne_zero) hpy2)
  have hc2 : ¬ (p : ℤ) ^ 2 ∣ c := by
    intro hc
    have h2 := (dvd_add_left hpy2).mp hc
    rw [hcast, pow_two] at h2
    have h3 := (mul_dvd_mul_iff_left (by exact_mod_cast hp.out.ne_zero : (p : ℤ) ≠ 0)).mp h2
    exact not_dvd_x_of_dvd_y b hp.out h (hpp.dvd_of_dvd_pow h3)
  have hc0 : c ≠ 0 := fun h0 => hc2 (h0 ▸ dvd_zero _)
  have hv : padicValInt p c = 1 := by
    have a1 := (padicValInt_dvd_iff 1 c).mp hc1
    have a2 : ¬ (2 ≤ padicValInt p c) := fun h2 => hc2 ((padicValInt_dvd_iff 2 c).mpr (Or.inr h2))
    omega
  refine ⟨hyp ▸ mul_ne_zero hy hc0, ?_⟩
  rw [hyp, padicValInt.mul hy hc0, hv]

/-- Lifting the exponent for Pell solutions: `v_p((b^m).y) = v_p(b.y) + v_p(m)`. -/
lemma padicValInt_y_pow (b : Solution₁ d) {p : ℕ} [hp : Fact p.Prime]
    (h : (p : ℤ) ∣ b.y) (hy : b.y ≠ 0) {m : ℕ} (hm : m ≠ 0) :
    padicValInt p (b ^ m).y = padicValInt p b.y + padicValNat p m := by
  have key : ∀ (a : ℕ) (b : Solution₁ d), (p : ℤ) ∣ b.y → b.y ≠ 0 →
      (b ^ p ^ a).y ≠ 0 ∧ padicValInt p (b ^ p ^ a).y = padicValInt p b.y + a := by
    intro a
    induction a with
    | zero => intro b _ hy; simpa using hy
    | succ a ih =>
      intro b h hy
      obtain ⟨h1, h2⟩ := padicValInt_y_pow_self b h hy
      have h3 : (p : ℤ) ∣ (b ^ p).y := by
        have := (padicValInt_dvd_iff 1 (b ^ p).y).mpr (Or.inr (by rw [h2]; omega))
        simpa using this
      obtain ⟨h4, h5⟩ := ih (b ^ p) h3 h1
      rw [pow_succ', pow_mul]
      exact ⟨h4, by rw [h5, h2]; ring⟩
  obtain ⟨e, j, hj, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm p hp.out.ne_one
  obtain ⟨h1, h2⟩ := key e b h hy
  have h3 : (p : ℤ) ∣ (b ^ p ^ e).y := by
    have := (padicValInt_dvd_iff 1 (b ^ p ^ e).y).mpr
      (Or.inr (by rw [h2]; have := (padicValInt_dvd_iff 1 b.y).mp (by simpa using h); omega))
    simpa using this
  rw [pow_mul, (padicValInt_y_pow_of_not_dvd _ h3 h1 hj).2, h2,
    padicValNat.mul (pow_ne_zero _ hp.out.ne_zero) (by rintro rfl; exact hj (dvd_zero p)),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hj, add_zero]

/-- Divisibility of `b.y` propagates to the powers of `b`. -/
lemma dvd_y_pow (b : Solution₁ d) {n : ℤ} (h : n ∣ b.y) (q : ℕ) : n ∣ (b ^ q).y := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [pow_succ, Solution₁.y_mul]
    exact dvd_add (dvd_mul_of_dvd_right h _) (dvd_mul_of_dvd_left ih _)

/-- Uniform valuation bound along the powers of a nontrivial Pell solution. -/
lemma exists_padicValInt_y_pow_le (a : Solution₁ d) (hx : 0 < a.x) (hy : 0 < a.y)
    (p : ℕ) [hp : Fact p.Prime] :
    ∃ C : ℕ, ∀ k : ℕ, k ≠ 0 → padicValInt p (a ^ k).y ≤ C + padicValNat p k := by
  classical
  have hne : ∀ k : ℕ, k ≠ 0 → (a ^ k).y ≠ 0 := by
    intro k hk
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    exact (Solution₁.y_pow_succ_pos hx hy k).ne'
  by_cases hex : ∃ r, 0 < r ∧ (p : ℤ) ∣ (a ^ r).y
  · obtain ⟨r, ⟨hr0, hrd⟩, hmin⟩ : ∃ r, (0 < r ∧ (p : ℤ) ∣ (a ^ r).y) ∧
        ∀ m < r, ¬ (0 < m ∧ (p : ℤ) ∣ (a ^ m).y) :=
      ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
    refine ⟨padicValInt p (a ^ r).y, fun k hk => ?_⟩
    by_cases hpk : (p : ℤ) ∣ (a ^ k).y
    · have hs : k % r = 0 := by
        by_contra hs
        have hlt : k % r < r := Nat.mod_lt _ hr0
        have hdecomp : a ^ k = (a ^ r) ^ (k / r) * a ^ (k % r) := by
          rw [← pow_mul, ← pow_add, Nat.div_add_mod]
        have h1 : (p : ℤ) ∣ ((a ^ r) ^ (k / r)).y := dvd_y_pow _ hrd _
        rw [hdecomp, Solution₁.y_mul] at hpk
        have h2 : (p : ℤ) ∣ ((a ^ r) ^ (k / r)).x * (a ^ (k % r)).y :=
          (dvd_add_left (dvd_mul_of_dvd_left h1 _)).mp hpk
        rcases (Nat.prime_iff_prime_int.mp hp.out).dvd_or_dvd h2 with h3 | h3
        · exact not_dvd_x_of_dvd_y _ hp.out h1 h3
        · exact hmin _ hlt ⟨Nat.pos_of_ne_zero hs, h3⟩
      obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero hs
      have hq : q ≠ 0 := by rintro rfl; simp at hk
      rw [pow_mul, padicValInt_y_pow _ hrd (hne r hr0.ne') hq,
        padicValNat.mul hr0.ne' hq]
      omega
    · rw [padicValInt.eq_zero_of_not_dvd hpk]; omega
  · push Not at hex
    refine ⟨0, fun k hk => ?_⟩
    rw [padicValInt.eq_zero_of_not_dvd (hex k (Nat.pos_of_ne_zero hk))]; omega

/-- A `B`-smooth number whose `p`-adic valuations are bounded by `C p + v_p(k)` is at most
`A * k` for a constant `A` depending only on `B` and `C`. -/
lemma smooth_le_mul (B : ℕ) (C : ℕ → ℕ) :
    ∃ A : ℕ, ∀ n k : ℕ, n ≠ 0 → k ≠ 0 → Smooth B n →
      (∀ p, p.Prime → p ≤ B → n.factorization p ≤ C p + k.factorization p) → n ≤ A * k := by
  refine ⟨∏ p ∈ (Finset.range (B + 1)).filter Nat.Prime, p ^ C p, fun n k hn hk hs hv => ?_⟩
  set A := ∏ p ∈ (Finset.range (B + 1)).filter Nat.Prime, p ^ C p with hA
  have hA0 : A ≠ 0 := by
    rw [hA, Finset.prod_ne_zero_iff]
    intro p hp
    exact pow_ne_zero _ (Finset.mem_filter.mp hp).2.ne_zero
  apply Nat.le_of_dvd (Nat.pos_of_ne_zero (mul_ne_zero hA0 hk))
  rw [← Nat.factorization_le_iff_dvd hn (mul_ne_zero hA0 hk)]
  intro q
  rw [Nat.factorization_mul hA0 hk, Finsupp.add_apply]
  by_cases hq : q.Prime
  · by_cases hqB : q ≤ B
    · have h1 : q ^ C q ∣ A := Finset.dvd_prod_of_mem _
        (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hq⟩)
      have h2 := (hq.pow_dvd_iff_le_factorization hA0).mp h1
      have h3 := hv q hq hqB
      omega
    · have : ¬ q ∣ n := fun h => hqB (hs q hq h)
      rw [Nat.factorization_eq_zero_of_not_dvd this]; omega
  · rw [Nat.factorization_eq_zero_of_not_prime _ hq]; omega

/-- Exponential growth of the `y`-coordinates. -/
lemma y_pow_ge (a : Solution₁ d) (hx : 1 < a.x) (hy : 0 < a.y) (k : ℕ) :
    2 ^ k ≤ (a ^ k).y + 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hxk := Solution₁.x_pow_pos (by omega : 0 < a.x) k
    have e : (a ^ (k + 1)).y = (a ^ k).x * a.y + (a ^ k).y * a.x := by
      rw [pow_succ, Solution₁.y_mul]
    have h1 : (1 : ℤ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have h0 : 0 ≤ (a ^ k).y := by linarith
    rw [e, pow_succ]
    nlinarith [mul_pos hxk hy, mul_le_mul_of_nonneg_left hx h0]

lemma sq_le_two_pow {k : ℕ} (hk : 4 ≤ k) : k ^ 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ 2, sq]; rw [sq] at ih; nlinarith

/-- Exponential beats linear. -/
lemma finite_two_pow_le (A : ℕ) : {k : ℕ | 2 ^ k ≤ A * k + 1}.Finite := by
  apply (Set.finite_Iic (A + 4)).subset
  intro k hk
  change 2 ^ k ≤ A * k + 1 at hk
  simp only [Set.mem_Iic]
  by_contra h
  have h1 := sq_le_two_pow (k := k) (by omega)
  nlinarith

/-- Along the powers of a nontrivial Pell solution, the `y`-coordinate is `B`-smooth only
finitely often. -/
theorem finite_smooth_y_pow (a : Solution₁ d) (hx : 1 < a.x) (hy : 0 < a.y) (B : ℕ) :
    {k : ℕ | Smooth B (a ^ k).y.natAbs}.Finite := by
  classical
  have hx0 : 0 < a.x := by omega
  let C : ℕ → ℕ := fun p =>
    if h : p.Prime then (@exists_padicValInt_y_pow_le d a hx0 hy p ⟨h⟩).choose else 0
  obtain ⟨A, hA⟩ := smooth_le_mul B C
  apply ((finite_two_pow_le A).union (Set.finite_singleton 0)).subset
  intro k hk
  change Smooth B (a ^ k).y.natAbs at hk
  by_cases hk0 : k = 0
  · exact Or.inr hk0
  left
  show 2 ^ k ≤ A * k + 1
  have hypos : 0 < (a ^ k).y := by
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    exact Solution₁.y_pow_succ_pos hx0 hy k'
  have hn0 : (a ^ k).y.natAbs ≠ 0 := by omega
  have hle := hA _ _ hn0 hk0 hk (fun p hp _ => by
    have hspec := (@exists_padicValInt_y_pow_le d a hx0 hy p ⟨hp⟩).choose_spec k hk0
    have hC : C p = (@exists_padicValInt_y_pow_le d a hx0 hy p ⟨hp⟩).choose := by
      simp [C, hp]
    rw [hC, Nat.factorization_def _ hp, Nat.factorization_def _ hp]
    exact hspec)
  have hg := y_pow_ge a hx hy k
  have habs : ((a ^ k).y.natAbs : ℤ) = (a ^ k).y := Int.natAbs_of_nonneg hypos.le
  rw [← habs] at hg
  have hg' : 2 ^ k ≤ (a ^ k).y.natAbs + 1 := by exact_mod_cast hg
  omega

/-- For a positive nonsquare `d`, only finitely many positive solutions of `x² - d y² = 1`
have `y` `B`-smooth. -/
theorem finite_pell_smooth (hd0 : 0 < d) (hd : ¬ IsSquare d) (B : ℕ) :
    {x : ℤ | ∃ y : ℤ, 0 < x ∧ 0 < y ∧ x ^ 2 - d * y ^ 2 = 1 ∧ Smooth B y.natAbs}.Finite := by
  obtain ⟨a₁, ha₁⟩ := IsFundamental.exists_of_not_isSquare hd0 hd
  apply ((finite_smooth_y_pow a₁ ha₁.1 ha₁.2.1 B).image (fun k => (a₁ ^ k).x)).subset
  rintro x ⟨y, hx, hy, h, hs⟩
  obtain ⟨n, hn⟩ := ha₁.eq_pow_of_nonneg (a := Solution₁.mk x y h)
    (by rw [Solution₁.x_mk]; exact hx) (by rw [Solution₁.y_mk]; exact hy.le)
  refine ⟨n, ?_, ?_⟩
  · show Smooth B (a₁ ^ n).y.natAbs
    rw [← hn, Solution₁.y_mk]; exact hs
  · show (a₁ ^ n).x = x
    rw [← hn, Solution₁.x_mk]

end Erdos368

/-! ######## Part: Stormer ######## -/



/-!
# Størmer–Pólya: `F(n) → ∞`

For every bound `B`, only finitely many `n` have `n(n+1)` `B`-smooth.  Proof: write
`4n(n+1) = (2n+1)² - 1 = D s²` with `D` squarefree; then `D` divides the primorial of `B`
(finitely many choices), `D` is not a square, and `(2n+1, s)` is a solution of the Pell equation
`x² - D y² = 1` with `s` `B`-smooth, of which there are finitely many by
`Erdos368.finite_pell_smooth`.
-/


namespace Erdos368

open Filter

lemma not_smooth_zero (B : ℕ) : ¬ Smooth B 0 := by
  intro h
  obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (B + 1)
  have := h p hp2 (dvd_zero p)
  omega

lemma Smooth.of_dvd {B a m : ℕ} (h : Smooth B m) (ha : a ∣ m) : Smooth B a :=
  fun p hp hpa => h p hp (dvd_trans hpa ha)

lemma smooth_four_mul {B m : ℕ} (h : Smooth B m) (h2 : 2 ∣ m) : Smooth B (4 * m) := by
  intro p hp hpd
  rcases (Nat.Prime.dvd_mul hp).mp hpd with h4 | hm
  · have : p ∣ 2 := by
      have : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [this] at h4; exact hp.dvd_of_dvd_pow h4
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
    exact hp2 ▸ h 2 Nat.prime_two h2
  · exact h p hp hm

/-- A squarefree `B`-smooth number divides the primorial of `B`. -/
lemma dvd_primorial_of_squarefree {B D : ℕ} (hD : Squarefree D) (hs : Smooth B D) :
    D ∣ primorial B := by
  rw [← Nat.prod_primeFactors_of_squarefree hD, primorial]
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  have hp' := Nat.prime_of_mem_primeFactors hp
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hs p hp' (Nat.dvd_of_mem_primeFactors hp))), hp'⟩

/-- Every natural number is `b ^ 2 * a` with `a` squarefree. -/
lemma exists_sq_mul_squarefree_nat (n : ℕ) : ∃ a b : ℕ, b ^ 2 * a = n ∧ Squarefree a := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨1, 0, by simp, squarefree_one⟩
    by_cases hsq : Squarefree n
    · exact ⟨n, 1, by simp, hsq⟩
    · obtain ⟨x, ⟨m, hm⟩, hx⟩ : ∃ x : ℕ, x * x ∣ n ∧ ¬ IsUnit x := by
        by_contra hc
        exact hsq fun x hx => by_contra fun hu => hc ⟨x, hx, hu⟩
      have hx2 : 2 ≤ x := by
        rcases x with _ | _ | x
        · simp at hm; omega
        · simp at hx
        · omega
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · subst h; simp at hm; omega
        · exact h
      have hlt : m < n := by
        have h4 : 4 ≤ x * x := by nlinarith
        rw [hm]; nlinarith
      obtain ⟨a, b, hab, hsa⟩ := ih m hlt
      exact ⟨a, x * b, by rw [hm, ← hab]; ring, hsa⟩

/-- **Størmer's theorem** (in the form needed here): for every `B`, only finitely many `n`
have every prime factor of `n(n+1)` at most `B`. -/
theorem finite_smooth_consecutive (B : ℕ) : {n : ℕ | Smooth B (n * (n + 1))}.Finite := by
  classical
  -- the cover indexed by the divisors `D` of the primorial of `B`
  let T : ℕ → Set ℕ := fun D =>
    {n | ∃ s : ℕ, 0 < s ∧ s ^ 2 * D = 4 * (n * (n + 1)) ∧ Smooth B s}
  have hT : ∀ D ∈ (primorial B).divisors, (T D).Finite := by
    intro D hD
    have hD0 : 0 < D := Nat.pos_of_mem_divisors hD
    by_cases hsq : IsSquare (D : ℤ)
    · -- no solutions at all
      convert Set.finite_empty
      ext n
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨s, hs0, hs, -⟩
      obtain ⟨c, hc⟩ := Int.isSquare_natCast_iff.mp hsq
      subst hc
      have hc0 : 0 < c := by
        rcases Nat.eq_zero_or_pos c with h | h
        · subst h; simp at hD0
        · exact h
      have h1 : 1 ≤ s * c := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have key : (s * c) ^ 2 + 1 = (2 * n + 1) ^ 2 := by
        calc (s * c) ^ 2 + 1 = s ^ 2 * (c * c) + 1 := by ring
          _ = (2 * n + 1) ^ 2 := by rw [hs]; ring
      have hlt : s * c < 2 * n + 1 := by nlinarith
      nlinarith
    · have hfin := finite_pell_smooth (d := (D : ℤ)) (by exact_mod_cast hD0) hsq B
      apply (hfin.preimage (f := fun n : ℕ => (2 * n + 1 : ℤ))
        (fun a _ b _ hab => by simp only at hab; omega)).subset
      rintro n ⟨s, hs0, hs, hsm⟩
      refine ⟨(s : ℤ), by positivity, by exact_mod_cast hs0, ?_, ?_⟩
      · have : ((s : ℤ) ^ 2 * D) = 4 * (n * (n + 1)) := by exact_mod_cast hs
        linear_combination -this
      · simpa using hsm
  apply ((primorial B).divisors.finite_toSet.biUnion hT).subset
  intro n hn
  change Smooth B (n * (n + 1)) at hn
  have hn0 : n * (n + 1) ≠ 0 := by
    rintro h0; rw [h0] at hn; exact not_smooth_zero B hn
  have hm := smooth_four_mul hn (Nat.even_mul_succ_self n).two_dvd
  obtain ⟨D, s, hDs, hsqf⟩ := exists_sq_mul_squarefree_nat (4 * (n * (n + 1)))
  have hm0 : 4 * (n * (n + 1)) ≠ 0 := by positivity
  have hs0 : s ≠ 0 := by rintro rfl; apply hm0; rw [← hDs]; ring
  have hD0 : D ≠ 0 := by rintro rfl; apply hm0; rw [← hDs]; ring
  refine Set.mem_biUnion (x := D) ?_ ?_
  · simp only [Finset.mem_coe, Nat.mem_divisors]
    exact ⟨dvd_primorial_of_squarefree hsqf (hm.of_dvd ⟨s ^ 2, by rw [← hDs]; ring⟩),
      primorial_pos B |>.ne'⟩
  · exact ⟨s, Nat.pos_of_ne_zero hs0, hDs,
      hm.of_dvd ⟨s * D, by rw [← hDs]; ring⟩⟩

/-- If `n ≥ 1` and `F n ≤ B`, then `n(n+1)` is `B`-smooth. -/
lemma smooth_of_F_le {n B : ℕ} (h : F n ≤ B) (hn : n ≠ 0) : Smooth B (n * (n + 1)) := by
  intro p hp hpd
  have hmem : p ∈ (n * (n + 1)).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hpd, by positivity⟩
  exact le_trans (Finset.le_sup (f := id) hmem) h

/-- **Pólya (1918) / Størmer (1897).**  The largest prime factor `F(n)` of `n(n+1)` tends to
infinity as `n → ∞`. -/
theorem tendsto_F_atTop : Tendsto F atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro B
  obtain ⟨N, hN⟩ := (finite_smooth_consecutive B).bddAbove
  refine ⟨N + 1, fun n hn => ?_⟩
  by_contra h
  have h := lt_of_not_ge h
  have : n ≤ N := hN (smooth_of_F_le h.le (by omega))
  omega

end Erdos368

/-! ######## Part: Examples ######## -/



/-!
# Sanity checks for the definition of `F`

* `F n` is a genuine prime dividing `n(n+1)` for every `n ≥ 1` (so the definition is not
  degenerate), and every prime factor of `n(n+1)` is `≤ F n`.
* A few kernel-checked values (by `decide +kernel`, no `native_decide`):
  `F 1 = 2`, `F 8 = 3` (`8·9 = 2³·3²`), `F 80 = 5` (`80·81 = 2⁴·3⁴·5`),
  `F 4374 = 7` (`4374·4375 = 2·3⁷·5⁴·7`).
* The equivalent "finitely many `n` with `F n ≤ B`" form of `F(n) → ∞`.
-/


namespace Erdos368

open Filter

lemma F_prime {n : ℕ} (hn : 1 ≤ n) : (F n).Prime ∧ F n ∣ n * (n + 1) := by
  have hne : (n * (n + 1)).primeFactors.Nonempty := by
    apply Nat.nonempty_primeFactors.mpr
    nlinarith
  obtain ⟨p, hp, hsup⟩ := Finset.exists_mem_eq_sup _ hne id
  have hF : F n = p := hsup
  rw [hF]
  exact ⟨Nat.prime_of_mem_primeFactors hp, Nat.dvd_of_mem_primeFactors hp⟩

lemma le_F {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime) (hd : p ∣ n * (n + 1)) : p ≤ F n :=
  Finset.le_sup (f := id) (Nat.mem_primeFactors.mpr ⟨hp, hd, by positivity⟩)

example : F 1 = 2 := by decide +kernel
example : F 8 = 3 := by decide +kernel
example : F 80 = 5 := by decide +kernel
example : F 4374 = 7 := by decide +kernel

/-- Equivalent form of Størmer–Pólya: for each `B`, only finitely many `n` have `F n ≤ B`. -/
theorem finite_F_le (B : ℕ) : {n : ℕ | F n ≤ B}.Finite := by
  apply ((finite_smooth_consecutive B).union (Set.finite_singleton 0)).subset
  intro n hn
  by_cases h0 : n = 0
  · exact Or.inr h0
  · exact Or.inl (smooth_of_F_le hn h0)

end Erdos368

/-! ######## Part: UpperBound ######## -/



/-!
# An upper-bound partial result: `F(n) ≤ n^δ` infinitely often

For `n = 2^m - 1` we have `n(n+1) = 2^m (2^m - 1)` and
`2^m - 1 = ∏_{d ∣ m} Φ_d(2)` with `0 < Φ_d(2) ≤ 3^{φ(d)} ≤ 3^{φ(m)}`, so
`F(2^m - 1) ≤ 3^{φ(m)}`.  Since `∑ 1/p` diverges, `φ(m)/m` can be made arbitrarily small, which
gives: for every `δ > 0` there are infinitely many `n` with `F(n) ≤ n^δ`.

This is a (much) weaker form of Schinzel's observation that `F(n) ≤ n^{O(1/log log log n)}`
infinitely often; it is far from Erdős's conjectured `(log n)^{2+ε}`.
-/


namespace Erdos368

open Polynomial Filter

lemma primeFactors_factorial (N : ℕ) :
    (N.factorial).primeFactors = (Finset.range (N + 1)).filter Nat.Prime := by
  ext p
  simp only [Nat.mem_primeFactors, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hp, hd, -⟩; exact ⟨Nat.lt_succ_of_le (hp.dvd_factorial.mp hd), hp⟩
  · rintro ⟨hlt, hp⟩; exact ⟨hp, hp.dvd_factorial.mpr (Nat.le_of_lt_succ hlt), N.factorial_ne_zero⟩

lemma sum_inv_le_neg_log_prod (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∑ p ∈ S, (1 / (p : ℝ)) ≤ - Real.log (∏ p ∈ S, (1 - (p : ℝ)⁻¹)) := by
  have hpos : ∀ p ∈ S, 0 < 1 - (p : ℝ)⁻¹ := by
    intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).two_le
    have : (p : ℝ)⁻¹ ≤ 1 / 2 := by rw [inv_eq_one_div]; gcongr
    linarith
  rw [Real.log_prod (fun p hp => (hpos p hp).ne'), ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have := Real.log_le_sub_one_of_pos (hpos p hp)
  rw [one_div]; linarith

lemma totient_factorial_ratio (N : ℕ) :
    ((N.factorial).totient : ℝ) = N.factorial *
      ∏ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) := by
  have := Nat.totient_eq_mul_prod_factors (N.factorial)
  rw [primeFactors_factorial] at this
  have h2 := congrArg (fun q : ℚ => (q : ℝ)) this
  push_cast at h2
  exact h2

/-- `φ(m)/m` is arbitrarily small for arbitrarily large `m` (from the divergence of `∑ 1/p`). -/
lemma exists_totient_le (ε : ℝ) (hε : 0 < ε) (M : ℕ) :
    ∃ m, M ≤ m ∧ (m.totient : ℝ) ≤ ε * m := by
  by_contra h
  simp only [not_exists, not_and, not_le] at h
  -- partial sums of `1/p` over primes `≤ N` are bounded for `N ≥ M`
  have hbound : ∀ N, M ≤ N →
      ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (1 / (p : ℝ)) ≤ - Real.log ε := by
    intro N hN
    have hfac : M ≤ N.factorial := le_trans hN (Nat.self_le_factorial N)
    have h1 := h _ hfac
    rw [totient_factorial_ratio, mul_comm ε] at h1
    have hpos : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
    have h2 : ε < ∏ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) :=
      lt_of_mul_lt_mul_left h1 hpos.le
    refine le_trans (sum_inv_le_neg_log_prod _ (fun p hp => (Finset.mem_filter.mp hp).2)) ?_
    have := Real.log_le_log hε h2.le
    linarith
  apply not_summable_one_div_on_primes
  refine summable_of_sum_le (c := - Real.log ε)
    (fun n => Set.indicator_nonneg (fun k _ => by positivity) n) (fun u => ?_)
  let N := max M (u.sup id)
  refine le_trans ?_ (hbound N (le_max_left _ _))
  have e : ∑ n ∈ u, Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) n =
      ∑ n ∈ u.filter Nat.Prime, (1 : ℝ) / n := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : n.Prime
    · rw [if_pos hn]; exact Set.indicator_of_mem (s := {p : ℕ | p.Prime}) hn _
    · rw [if_neg hn]
      exact Set.indicator_apply_eq_zero.mpr fun h => absurd h hn
  rw [e]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    obtain ⟨hqu, hqp⟩ := Finset.mem_filter.mp hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le ?_), hqp⟩
    exact le_trans (Finset.le_sup (f := id) hqu) (le_max_right _ _)
  · intro q _ _; positivity

lemma cyclotomic_eval_two_bound {d : ℕ} (hd : 0 < d) :
    0 < (cyclotomic d ℤ).eval 2 ∧ (cyclotomic d ℤ).eval 2 ≤ 3 ^ d.totient := by
  rcases (show d = 1 ∨ d = 2 ∨ 3 ≤ d by omega) with rfl | rfl | h3
  · simp
  · simp
  · have hcast : (((cyclotomic d ℤ).eval 2 : ℤ) : ℝ) = (cyclotomic d ℝ).eval 2 := by
      have := cyclotomic.eval_apply (2 : ℤ) d (Int.castRingHom ℝ)
      simpa using this.symm
    have h1 := cyclotomic_eval_lt_add_one_pow_totient (q := (2 : ℝ)) h3 (by norm_num)
    have h2 := cyclotomic_pos (by omega : 2 < d) (2 : ℤ)
    refine ⟨h2, ?_⟩
    rw [← hcast] at h1
    norm_num at h1
    exact_mod_cast h1.le

/-- A prime dividing a finite product divides one of the factors. -/
lemma exists_mem_dvd_of_prime_dvd_prod {ι : Type*} {s : Finset ι} {f : ι → ℤ} {p : ℤ}
    (hp : Prime p) (h : p ∣ ∏ i ∈ s, f i) : ∃ i ∈ s, p ∣ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact absurd (isUnit_of_dvd_one (by simpa using h)) hp.not_unit
  | insert j s hj ih =>
    rw [Finset.prod_insert hj] at h
    rcases hp.dvd_or_dvd h with h1 | h1
    · exact ⟨j, Finset.mem_insert_self j s, h1⟩
    · obtain ⟨i, hi, hpi⟩ := ih h1
      exact ⟨i, Finset.mem_insert_of_mem hi, hpi⟩

/-- Every prime factor of `2^m - 1` is at most `3^{φ(m)}`. -/
lemma prime_dvd_two_pow_sub_one_le {m p : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hd : p ∣ 2 ^ m - 1) : p ≤ 3 ^ m.totient := by
  have hprod : ∏ d ∈ m.divisors, (cyclotomic d ℤ).eval 2 = 2 ^ m - 1 := by
    rw [← eval_prod, prod_cyclotomic_eq_X_pow_sub_one hm]; simp
  have hdZ : (p : ℤ) ∣ ∏ d ∈ m.divisors, (cyclotomic d ℤ).eval 2 := by
    rw [hprod]
    have : ((2 ^ m - 1 : ℕ) : ℤ) = 2 ^ m - 1 := by
      rw [Nat.cast_sub (Nat.one_le_two_pow)]; push_cast; ring
    rw [← this]; exact_mod_cast hd
  obtain ⟨d, hdm, hpd⟩ := exists_mem_dvd_of_prime_dvd_prod (Nat.prime_iff_prime_int.mp hp) hdZ
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hdm
  obtain ⟨hpos, hle⟩ := cyclotomic_eval_two_bound hd0
  have h1 : (p : ℤ) ≤ 3 ^ d.totient := le_trans (Int.le_of_dvd hpos hpd) hle
  have h2 : d.totient ≤ m.totient :=
    Nat.le_of_dvd (Nat.totient_pos.mpr hm) (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hdm))
  have h3 : (3 : ℤ) ^ d.totient ≤ 3 ^ m.totient := pow_le_pow_right₀ (by norm_num) h2
  exact_mod_cast le_trans h1 h3

/-- `F(2^m - 1) ≤ 3^{φ(m)}` for `m ≥ 1`. -/
lemma F_two_pow_sub_one_le {m : ℕ} (hm : 0 < m) : F (2 ^ m - 1) ≤ 3 ^ m.totient := by
  unfold F largestPrimeFactor
  apply Finset.sup_le
  intro p hp
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  rw [Nat.sub_add_cancel Nat.one_le_two_pow] at hpd
  rcases (Nat.Prime.dvd_mul hp').mp hpd with h | h
  · exact prime_dvd_two_pow_sub_one_le hm hp' h
  · have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp' Nat.prime_two).mp (hp'.dvd_of_dvd_pow h)
    subst this
    have : 1 ≤ m.totient := Nat.totient_pos.mpr hm
    calc 2 ≤ 3 ^ 1 := by norm_num
      _ ≤ 3 ^ m.totient := Nat.pow_le_pow_right (by norm_num) this

/-- **Partial result (upper side).**  For every `δ > 0` there are infinitely many `n` with
`F(n) ≤ n^δ`. -/
theorem frequently_F_le_rpow (δ : ℝ) (hδ : 0 < δ) :
    ∃ᶠ n : ℕ in atTop, (F n : ℝ) ≤ (n : ℝ) ^ δ := by
  rw [Filter.frequently_atTop]
  intro a
  obtain ⟨m, hm, hφ⟩ := exists_totient_le (δ / 4) (by positivity) (a + 2)
  have hm0 : 0 < m := by omega
  refine ⟨2 ^ m - 1, ?_, ?_⟩
  · have := Nat.lt_two_pow_self (n := m); omega
  have hA : (F (2 ^ m - 1) : ℝ) ≤ (3 : ℝ) ^ m.totient := by
    exact_mod_cast F_two_pow_sub_one_le hm0
  have hB : (3 : ℝ) ^ m.totient ≤ (2 : ℝ) ^ ((2 * m.totient : ℕ) : ℝ) := by
    rw [Real.rpow_natCast, pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hn : (2 : ℝ) ^ (m - 1) ≤ ((2 ^ m - 1 : ℕ) : ℝ) := by
    have h1 : 2 ^ (m - 1) ≤ 2 ^ m - 1 := by
      have : 2 ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
      have : 1 ≤ 2 ^ (m - 1) := Nat.one_le_two_pow
      omega
    exact_mod_cast h1
  have hC : (2 : ℝ) ^ (((m - 1 : ℕ) : ℝ) * δ) ≤ ((2 ^ m - 1 : ℕ) : ℝ) ^ δ := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
    exact Real.rpow_le_rpow (by positivity) hn hδ.le
  have hD : ((2 * m.totient : ℕ) : ℝ) ≤ ((m - 1 : ℕ) : ℝ) * δ := by
    have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (by omega : 2 ≤ m)
    rw [hm1]; push_cast
    nlinarith
  calc (F (2 ^ m - 1) : ℝ) ≤ (3 : ℝ) ^ m.totient := hA
    _ ≤ (2 : ℝ) ^ ((2 * m.totient : ℕ) : ℝ) := hB
    _ ≤ (2 : ℝ) ^ (((m - 1 : ℕ) : ℝ) * δ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hD
    _ ≤ _ := hC

end Erdos368


open Filter in
/-- Summary of what is kernel-verified about `F(n)`, the largest prime factor of `n(n+1)`:
* (Størmer 1897 / Pólya 1918) `F(n) → ∞`;
* for every `δ > 0`, `F(n) ≤ n^δ` for infinitely many `n`. -/
theorem erdos_368_verified :
    Tendsto Erdos368.F atTop atTop ∧
      ∀ δ : ℝ, 0 < δ → ∃ᶠ n : ℕ in atTop, (Erdos368.F n : ℝ) ≤ (n : ℝ) ^ δ :=
  ⟨Erdos368.tendsto_F_atTop, Erdos368.frequently_F_le_rpow⟩
 

namespace Erdos368

/-- The supplied definition agrees with the repository's greatest-prime-factor API. -/
theorem F_eq_maxPrimeFac (n : ℕ) : F n = (n * (n + 1)).maxPrimeFac := by
  rcases n with _ | n
  · simp [F, largestPrimeFactor]
  · have hn : 1 ≤ n + 1 := by omega
    have hm : 1 < (n + 1) * (n + 1 + 1) := by nlinarith
    obtain ⟨hp, hd⟩ := F_prime hn
    apply le_antisymm
    · exact Nat.le_maxPrimeFac (by omega) hp hd
    · exact le_F hn (Nat.prime_maxPrimeFac_of_one_lt _ hm) Nat.maxPrimeFac_dvd

theorem tendsto_maxPrimeFac_atTop :
    Filter.Tendsto (fun n : ℕ => (n * (n + 1)).maxPrimeFac)
      Filter.atTop Filter.atTop := by
  simpa only [F_eq_maxPrimeFac] using tendsto_F_atTop

theorem frequently_maxPrimeFac_le_rpow (δ : ℝ) (hδ : 0 < δ) :
    ∃ᶠ n : ℕ in Filter.atTop, ((n * (n + 1)).maxPrimeFac : ℝ) ≤ (n : ℝ) ^ δ := by
  simpa only [F_eq_maxPrimeFac] using frequently_F_le_rpow δ hδ

end Erdos368