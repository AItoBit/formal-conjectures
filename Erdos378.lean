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

/-!
# Erdős Problem #378

Let `r ≥ 0`. Does the density of integers `n` for which `C(n,k)` is squarefree for at
least `r` values of `1 ≤ k < n` exist? Is this density `> 0`?
-/

open Filter Topology Finset

namespace Erdos378

/-- The number of `k` with `1 ≤ k < n` such that `C(n,k)` is squarefree. -/
def sqfreeBinomCount (n : ℕ) : ℕ :=
  ((Finset.Ico 1 n).filter (fun k => Squarefree (n.choose k))).card

/-- The counting function `#{n < N : C(n,k) is squarefree for at least r values 1 ≤ k < n}`. -/
def countUpTo (r N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => r ≤ sqfreeBinomCount n)).card

/-- The full Erdős #378 statement: for every `r`, the natural density of
`{n : C(n,k) squarefree for at least r values of 1 ≤ k < n}` exists and is positive. -/
def Erdos378Statement : Prop :=
  ∀ r : ℕ, ∃ d : ℝ, 0 < d ∧
    Tendsto (fun N : ℕ => (countUpTo r N : ℝ) / N) atTop (𝓝 d)

/-! ### An explicit product formula -/

/-- If `j ∣ n + 1` for all `1 ≤ j ≤ k`, then `C(n,k) = ∏_{j=1}^k ((n+1)/j - 1)`. -/
lemma choose_eq_prod (n : ℕ) : ∀ k, k ≤ n → (∀ j ∈ Icc 1 k, j ∣ n + 1) →
    n.choose k = ∏ j ∈ Icc 1 k, ((n + 1) / j - 1) := by
  intro k
  induction k with
  | zero => intro _ _; simp
  | succ k ih =>
    intro hk hdiv
    rw [Finset.prod_Icc_succ_top (by omega),
      ← ih (by omega) (fun j hj => hdiv j (by simp at hj ⊢; omega))]
    have hd : k + 1 ∣ n + 1 := hdiv (k+1) (by simp)
    obtain ⟨t, ht⟩ := hd
    have hq : (n + 1) / (k + 1) = t := by rw [ht]; exact Nat.mul_div_cancel_left t (by omega)
    rw [hq]
    have key := Nat.choose_succ_right_eq n k
    have h2 : n - k = (k + 1) * (t - 1) := by
      rw [Nat.mul_sub, ← ht]; omega
    rw [h2] at key
    apply Nat.eq_of_mul_eq_mul_right (show 0 < k + 1 by omega)
    rw [key]; ring

/-- The "good" residue/sieve condition used to manufacture many squarefree binomials:
`((2K)!)² ∣ n + 1`, and none of `n, n-1, …, n-K+1` is divisible by `p²` for a prime `p > 2K`.
For such `n`, `C(n,k)` is squarefree for every `k ≤ K` (`squarefree_choose_of_good`). -/
def Good (K n : ℕ) : Prop :=
  (2 * K).factorial ^ 2 ∣ n + 1 ∧
    ∀ i < K, ∀ p : ℕ, p.Prime → 2 * K < p → ¬ p ^ 2 ∣ n - i

lemma two_K_lt_of_good {K n : ℕ} (hK : 1 ≤ K) (h : Good K n) : 2 * K < n := by
  have h1 := Nat.le_of_dvd (by omega) h.1
  have h2 : 2 * K ≤ (2 * K).factorial := Nat.self_le_factorial _
  have h3 : 2 ≤ (2 * K).factorial := le_trans (by omega) h2
  nlinarith

/-- A prime dividing a finite product of naturals divides one of the factors
(proved directly to avoid depending on a lemma name that differs between Mathlib versions). -/
lemma exists_dvd_of_prime_dvd_prod {p : ℕ} (hp : p.Prime) (s : Finset ℕ) (f : ℕ → ℕ)
    (h : p ∣ ∏ j ∈ s, f j) : ∃ j ∈ s, p ∣ f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Nat.dvd_one] at h; exact absurd h hp.one_lt.ne'
  | insert a s ha ih =>
    rw [Finset.prod_insert ha] at h
    rcases (Nat.Prime.dvd_mul hp).1 h with h' | h'
    · exact ⟨a, Finset.mem_insert_self a s, h'⟩
    · obtain ⟨j, hj, hj'⟩ := ih h'
      exact ⟨j, Finset.mem_insert_of_mem hj, hj'⟩

/-- For good `n`, every `C(n,k)` with `k ≤ K` is squarefree. -/
lemma squarefree_choose_of_good {K n k : ℕ} (hK : 1 ≤ K) (h : Good K n) (hkK : k ≤ K) :
    Squarefree (n.choose k) := by
  have hnK := two_K_lt_of_good hK h
  have hjdvd : ∀ j ∈ Icc 1 k, j ∣ (2 * K).factorial :=
    fun j hj => Nat.dvd_factorial (by simp at hj; omega) (by simp at hj; omega)
  have hjn : ∀ j ∈ Icc 1 k, j ∣ n + 1 := fun j hj =>
    (hjdvd j hj).trans ((dvd_pow_self _ two_ne_zero).trans h.1)
  rw [choose_eq_prod n k (by omega) hjn]
  have hfac : ∀ j ∈ Icc 1 k, j * ((n + 1) / j - 1) = n - (j - 1) := by
    intro j hj
    have := Nat.mul_div_cancel' (hjn j hj)
    simp at hj
    rw [Nat.mul_sub, this]; omega
  have hsmall : ∀ j ∈ Icc 1 k, ∀ p : ℕ, p.Prime → p ≤ 2 * K → ¬ p ∣ (n + 1) / j - 1 := by
    intro j hj p hp hpK hpd
    have hpj : p * j ∣ n + 1 := by
      refine (Nat.mul_dvd_mul ((Nat.Prime.dvd_factorial hp).2 hpK) (hjdvd j hj)).trans ?_
      rw [← sq]; exact h.1
    obtain ⟨t, ht⟩ := hpj
    have hj0 : 0 < j := by simp at hj; omega
    have hq : (n + 1) / j = p * t := by
      rw [ht, show p * j * t = j * (p * t) by ring, Nat.mul_div_cancel_left _ hj0]
    rw [hq] at hpd
    have ht0 : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · simp [h0] at ht
      · exact h0
    have hp1 : p ∣ p * t - (p * t - 1) := Nat.dvd_sub (dvd_mul_right p t) hpd
    have : p * t - (p * t - 1) = 1 := by
      have : 1 ≤ p * t := Nat.mul_pos hp.pos ht0
      omega
    rw [this] at hp1
    exact hp.one_lt.ne' (Nat.dvd_one.1 hp1)
  have hlarge : ∀ i ∈ Icc 1 k, ∀ j ∈ Icc 1 k, i < j → ∀ p : ℕ, p.Prime → 2 * K < p →
      p ∣ (n + 1) / i - 1 → ¬ p ∣ (n + 1) / j - 1 := by
    intro i hi j hj hij p hp hpK hpi hpj
    have h1 : p ∣ n - (i - 1) := hfac i hi ▸ dvd_mul_of_dvd_right hpi i
    have h2 : p ∣ n - (j - 1) := hfac j hj ▸ dvd_mul_of_dvd_right hpj j
    have h3 := Nat.dvd_sub h1 h2
    simp at hi hj
    have h4 : n - (i - 1) - (n - (j - 1)) = j - i := by omega
    rw [h4] at h3
    have := Nat.le_of_dvd (by omega) h3
    omega
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  obtain ⟨j, hj, hpj⟩ :=
    exists_dvd_of_prime_dvd_prod hp _ _ (dvd_trans (dvd_mul_right p p) hpp)
  by_cases hpK : p ≤ 2 * K
  · exact hsmall j hj p hp hpK hpj
  replace hpK : 2 * K < p := by omega
  rw [← Finset.mul_prod_erase _ _ hj] at hpp
  have hcop : Nat.Coprime (p * p) (∏ i ∈ (Icc 1 k).erase j, ((n + 1) / i - 1)) := by
    apply Nat.Coprime.mul_left <;>
    · apply Nat.Coprime.prod_right
      intro i hi
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro hpi
      obtain ⟨hij, hi⟩ := Finset.mem_erase.1 hi
      rcases lt_or_gt_of_ne hij with hlt | hlt
      · exact hlarge i hi j hj hlt p hp hpK hpi hpj
      · exact hlarge j hj i hi hlt p hp hpK hpj hpi
  have hpp2 : p * p ∣ (n + 1) / j - 1 := hcop.dvd_of_dvd_mul_right hpp
  have : p ^ 2 ∣ n - (j - 1) := by
    rw [← hfac j hj, sq]; exact dvd_mul_of_dvd_right hpp2 j
  simp at hj
  exact h.2 (j - 1) (by omega) p hp hpK this

/-- For good `n`, at least `2K` of the binomials `C(n,k)`, `1 ≤ k < n`, are squarefree. -/
lemma two_mul_le_count_of_good {K n : ℕ} (hK : 1 ≤ K) (h : Good K n) :
    2 * K ≤ sqfreeBinomCount n := by
  have hnK := two_K_lt_of_good hK h
  have hsub : Icc 1 K ∪ Ico (n - K) n ⊆
      (Finset.Ico 1 n).filter (fun k => Squarefree (n.choose k)) := by
    intro k hk
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ico] at hk
    rw [Finset.mem_filter, Finset.mem_Ico]
    rcases hk with hk | hk
    · exact ⟨⟨hk.1, by omega⟩, squarefree_choose_of_good hK h hk.2⟩
    · refine ⟨⟨by omega, hk.2⟩, ?_⟩
      rw [← Nat.choose_symm (by omega)]
      exact squarefree_choose_of_good hK h (by omega)
  have hdisj : Disjoint (Icc 1 K) (Ico (n - K) n) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp at ha hb
    omega
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Nat.card_Icc, Nat.card_Ico] at this
  unfold sqfreeBinomCount
  omega

/-! ### Counting lemmas -/

lemma card_dvd_succ_ge (M N : ℕ) (hM : 0 < M) :
    N / M ≤ ((Finset.range N).filter (fun n => M ∣ n + 1)).card := by
  have : (Finset.Icc 1 (N / M)).image (fun t => M * t - 1) ⊆
      (Finset.range N).filter (fun n => M ∣ n + 1) := by
    intro n hn
    simp only [Finset.mem_image, Finset.mem_Icc] at hn
    obtain ⟨t, ⟨ht1, ht2⟩, rfl⟩ := hn
    have h1 : M ≤ M * t := Nat.le_mul_of_pos_right M ht1
    have h2 : M * t ≤ N := (Nat.le_div_iff_mul_le hM).1 ht2 |>.trans_eq' (mul_comm _ _)
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [Nat.sub_add_cancel (by omega)]; exact dvd_mul_right _ _
  have hinj : Set.InjOn (fun t => M * t - 1) (Finset.Icc 1 (N / M) : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
    have h1 : M ≤ M * a := Nat.le_mul_of_pos_right M ha.1
    have h2 : M ≤ M * b := Nat.le_mul_of_pos_right M hb.1
    have : M * a = M * b := by simp only at hab; omega
    exact Nat.eq_of_mul_eq_mul_left hM this
  have := Finset.card_le_card this
  rwa [Finset.card_image_of_injOn hinj, Nat.card_Icc, Nat.add_sub_cancel] at this

lemma card_dvd_succ_dvd_sub_le (M q N i : ℕ) (hM : 0 < M) (hq : 0 < q) (hcop : M.Coprime q) :
    ((Finset.range N).filter (fun n => M ∣ n + 1 ∧ q ∣ n - i ∧ i ≤ n)).card
      ≤ N / (M * q) + 1 := by
  have hMq : 0 < M * q := Nat.mul_pos hM hq
  have hmaps : Set.MapsTo (fun n => n / (M * q))
      ((Finset.range N).filter (fun n => M ∣ n + 1 ∧ q ∣ n - i ∧ i ≤ n) : Set ℕ)
      (Finset.range (N / (M * q) + 1) : Set ℕ) := by
    intro n hn
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn
    rw [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hn.1.le)
  have hinj : Set.InjOn (fun n => n / (M * q))
      ((Finset.range N).filter (fun n => M ∣ n + 1 ∧ q ∣ n - i ∧ i ≤ n) : Set ℕ) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
    simp only at hab
    have h1 : a ≡ b [MOD M] := by
      have : a + 1 ≡ b + 1 [MOD M] :=
        (Nat.modEq_zero_iff_dvd.2 ha.2.1).trans (Nat.modEq_zero_iff_dvd.2 hb.2.1).symm
      exact Nat.ModEq.add_right_cancel' 1 this
    have h2 : a ≡ b [MOD q] := by
      have ha' : a ≡ i [MOD q] := ((Nat.modEq_iff_dvd' ha.2.2.2).2 ha.2.2.1).symm
      have hb' : b ≡ i [MOD q] := ((Nat.modEq_iff_dvd' hb.2.2.2).2 hb.2.2.1).symm
      exact ha'.trans hb'.symm
    have h3 : a ≡ b [MOD M * q] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨h1, h2⟩
    rw [← Nat.div_add_mod a (M * q), ← Nat.div_add_mod b (M * q), hab, h3]
  have := Finset.card_le_card_of_injOn _ hmaps hinj
  simpa using this

lemma sum_inv_sq_Ioc_le (a : ℕ) (ha : 0 < a) (b : ℕ) :
    ∑ m ∈ Finset.Ioc a b, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 / a := by
  rcases le_or_gt a b with hab | hab
  · have key : ∀ b, a ≤ b → ∑ m ∈ Finset.Ioc a b, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 / a - 1 / b := by
      intro b hb
      induction b, hb using Nat.le_induction with
      | base => simp
      | succ b hb ih =>
        rw [Finset.sum_Ioc_succ_top hb]
        have hb0 : (0 : ℝ) < b := by exact_mod_cast (lt_of_lt_of_le ha hb)
        have : (1 : ℝ) / ((b + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / b - 1 / ((b + 1 : ℕ) : ℝ) := by
          push_cast
          rw [div_sub_div _ _ hb0.ne' (by positivity),
            div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        linarith
    have := key b hab
    have : (0 : ℝ) ≤ 1 / b := by positivity
    linarith
  · rw [Finset.Ioc_eq_empty (by omega)]; simp

open Classical in
/-- The good `n` have positive lower density (an explicit sieve with constant `1/(4·((2K)!)²)`). -/
lemma good_lower_density (K : ℕ) (hK : 1 ≤ K) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * N ≤ (((Finset.range N).filter (fun n => Good K n)).card : ℝ) := by
  set M := (2 * K).factorial ^ 2 with hMdef
  have hM : 0 < M := by positivity
  have hMbig : 2 * K + 2 ≤ M := by
    have h2 : 2 * K ≤ (2 * K).factorial := Nat.self_le_factorial _
    have h3 : 2 ≤ (2 * K).factorial := le_trans (by omega) h2
    rw [hMdef]; nlinarith
  refine ⟨1 / (4 * M), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop ((4 * M * (K + 1)) ^ 2)] with N hN
  set s := Nat.sqrt N with hs
  have hs_big : 4 * M * (K + 1) ≤ s := Nat.le_sqrt'.2 hN
  have hss : s * s ≤ N := Nat.sqrt_le N
  set A := (Finset.range N).filter (fun n => M ∣ n + 1)
  set P := (Finset.Ioc (2 * K) s).filter Nat.Prime
  set B : ℕ → ℕ → Finset ℕ := fun i p =>
    (Finset.range N).filter (fun n => M ∣ n + 1 ∧ p ^ 2 ∣ n - i ∧ i ≤ n)
  set U := (Finset.range K).biUnion (fun i => P.biUnion (B i))
  -- the sieve inclusion
  have hsub : A \ U ⊆ (Finset.range N).filter (fun n => Good K n) := by
    intro n hn
    rw [Finset.mem_sdiff] at hn
    obtain ⟨hnA, hnU⟩ := hn
    rw [Finset.mem_filter] at hnA ⊢
    refine ⟨hnA.1, hnA.2, ?_⟩
    intro i hi p hp hpK hpd
    apply hnU
    have hnM : M ≤ n + 1 := Nat.le_of_dvd (by omega) hnA.2
    have hni : 0 < n - i := by omega
    have hpn : p * p ≤ N := by
      have := Nat.le_of_dvd hni hpd
      have := Finset.mem_range.1 hnA.1
      rw [sq] at *; omega
    simp only [U, Finset.mem_biUnion]
    refine ⟨i, Finset.mem_range.2 hi, p, ?_, ?_⟩
    · simp only [P, Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨hpK, Nat.le_sqrt.2 hpn⟩, hp⟩
    · simp only [B, Finset.mem_filter]
      exact ⟨hnA.1, hnA.2, hpd, by omega⟩
  have h1 : A.card ≤ ((Finset.range N).filter (fun n => Good K n)).card + U.card :=
    (Finset.card_le_card_sdiff_add_card).trans (Nat.add_le_add_right (Finset.card_le_card hsub) _)
  have h2 : U.card ≤ ∑ i ∈ Finset.range K, ∑ p ∈ P, (B i p).card :=
    (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun i _ => Finset.card_biUnion_le)
  have h3 : ∀ i, ∀ p ∈ P, ((B i p).card : ℝ) ≤ (N : ℝ) / M * (1 / (p : ℝ) ^ 2) + 1 := by
    intro i p hp
    simp only [P, Finset.mem_filter, Finset.mem_Ioc] at hp
    have hcop : M.Coprime (p ^ 2) := by
      apply Nat.Coprime.pow
      apply Nat.Coprime.symm
      rw [Nat.Prime.coprime_iff_not_dvd hp.2, Nat.Prime.dvd_factorial hp.2]
      omega
    have := card_dvd_succ_dvd_sub_le M (p ^ 2) N i hM (by have := hp.2.pos; positivity) hcop
    have h' : ((N / (M * p ^ 2) : ℕ) : ℝ) ≤ (N : ℝ) / M * (1 / (p : ℝ) ^ 2) := by
      refine (Nat.cast_div_le).trans (le_of_eq ?_)
      push_cast; field_simp
    calc ((B i p).card : ℝ) ≤ ((N / (M * p ^ 2) + 1 : ℕ) : ℝ) := by exact_mod_cast this
      _ ≤ _ := by push_cast; linarith
  have h4 : ∀ i ∈ Finset.range K, (∑ p ∈ P, ((B i p).card : ℝ)) ≤ (N : ℝ) / M * (1 / (2 * K)) + s := by
    intro i _
    calc (∑ p ∈ P, ((B i p).card : ℝ))
        ≤ ∑ p ∈ P, ((N : ℝ) / M * (1 / (p : ℝ) ^ 2) + 1) := Finset.sum_le_sum (h3 i)
      _ ≤ ∑ p ∈ Finset.Ioc (2 * K) s, ((N : ℝ) / M * (1 / (p : ℝ) ^ 2) + 1) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => by positivity)
      _ = (N : ℝ) / M * ∑ p ∈ Finset.Ioc (2 * K) s, (1 / (p : ℝ) ^ 2)
            + ((Finset.Ioc (2 * K) s).card : ℝ) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]; simp
      _ ≤ (N : ℝ) / M * (1 / (2 * K : ℕ)) + s := by
          gcongr
          · exact sum_inv_sq_Ioc_le (2 * K) (by omega) s
          · rw [Nat.card_Ioc]; exact_mod_cast Nat.sub_le _ _
      _ = (N : ℝ) / M * (1 / (2 * K)) + s := by push_cast; ring
  have h5 : ((N / M : ℕ) : ℝ) ≥ (N : ℝ) / M - 1 := by
    have := Nat.lt_div_mul_add (a := N) hM
    have h' : (N : ℝ) < (N / M : ℕ) * M + M := by exact_mod_cast this
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    rw [ge_iff_le, sub_le_iff_le_add, div_le_iff₀ hM']
    linarith
  have hA : ((N / M : ℕ) : ℝ) ≤ A.card := by exact_mod_cast card_dvd_succ_ge M N hM
  have hU : (U.card : ℝ) ≤ K * ((N : ℝ) / M * (1 / (2 * K)) + s) := by
    calc (U.card : ℝ) ≤ ∑ i ∈ Finset.range K, ∑ p ∈ P, ((B i p).card : ℝ) := by exact_mod_cast h2
      _ ≤ ∑ i ∈ Finset.range K, ((N : ℝ) / M * (1 / (2 * K)) + s) := Finset.sum_le_sum h4
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h1' : (A.card : ℝ) ≤ ((Finset.range N).filter (fun n => Good K n)).card + U.card := by
    exact_mod_cast h1
  -- final arithmetic
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hs' : (4 * M * (K + 1) : ℝ) ≤ s := by exact_mod_cast hs_big
  have hss' : (s : ℝ) * s ≤ N := by exact_mod_cast hss
  have hKM : (K : ℝ) * ((N : ℝ) / M * (1 / (2 * K))) = (N : ℝ) / M / 2 := by
    field_simp
  have hfin : (N : ℝ) / M / 4 ≥ K * s + 1 := by
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hs1 : (1 : ℝ) ≤ s := by nlinarith
    have : (4 * M * (K + 1) : ℝ) * s ≤ N := by nlinarith
    rw [ge_iff_le, div_div, le_div_iff₀ (by positivity)]
    nlinarith
  have : (1 : ℝ) / (4 * M) * N = (N : ℝ) / M / 4 := by field_simp
  rw [this]
  nlinarith

/-- **Main partial result.** For every `r`, the set of `n` such that `C(n,k)` is squarefree
for at least `r` values `1 ≤ k < n` has positive lower density. -/
theorem lower_density_pos (r : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, c * N ≤ (countUpTo r N : ℝ) := by
  classical
  obtain ⟨c, hc, hev⟩ := good_lower_density (r + 1) (by omega)
  refine ⟨c, hc, hev.mono fun N hN => hN.trans ?_⟩
  have hsub : (Finset.range N).filter (fun n => Good (r + 1) n) ⊆
      (Finset.range N).filter (fun n => r ≤ sqfreeBinomCount n) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    have := two_mul_le_count_of_good (K := r + 1) (by omega) hn.2
    exact ⟨hn.1, by omega⟩
  exact_mod_cast Finset.card_le_card hsub

/-- Conditional answer to the second question: if the density exists, it is positive. -/
theorem density_pos_of_tendsto (r : ℕ) (d : ℝ)
    (hd : Tendsto (fun N : ℕ => (countUpTo r N : ℝ) / N) atTop (𝓝 d)) : 0 < d := by
  obtain ⟨c, hc, hev⟩ := lower_density_pos r
  refine lt_of_lt_of_le hc (ge_of_tendsto hd ?_)
  filter_upwards [hev, eventually_gt_atTop 0] with N hN hN0
  rw [le_div_iff₀ (by exact_mod_cast hN0)]
  exact hN

/-- The case `r = 0` of the full statement (density `1`). -/
theorem statement_zero :
    Tendsto (fun N : ℕ => (countUpTo 0 N : ℝ) / N) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  simp [countUpTo, Finset.filter_true_of_mem, hN.ne']

end Erdos378

/-! ### Small sanity checks (kernel-checked by `decide`) -/

namespace Erdos378

/-- `C(6,k)` for `k = 1,…,5` is `6, 15, 20, 15, 6`; all but `20` are squarefree. -/
example : sqfreeBinomCount 6 = 4 := by decide +kernel

/-- `C(4,k)` for `k = 1,2,3` is `4, 6, 4`; only `6` is squarefree. -/
example : sqfreeBinomCount 4 = 1 := by decide +kernel

end Erdos378
