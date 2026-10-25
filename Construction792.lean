module

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

@[expose] public section

/-! Adapted from facebookresearch/atlas-lean, commit
7f27c3ad16289716586daf311cf568bcae4160d5, Chapter2/SumFree.lean.
Changes: module/public exposure wrappers; all-scalar averaging restores the
known strict inequality |A| < 3|S| for nonempty A, rather than the upstream
natural-floor conclusion. This is not a new mathematical result.
Original Meta copyright and LICENSE are retained. This is a classical partial
result for problem 792, not the unresolved optimal-growth theorem. -/

set_option maxHeartbeats 400000

open Finset

namespace Atlas792

/-- A subset $S \subseteq \mathbb{Z}$ is sum-free if no two elements (possibly equal)
sum to a third, i.e., $a + b \neq c$ for all $a, b, c \in S$. -/
def IsSumFree (S : Finset ℤ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a + b ≠ c

/-- Key arithmetic fact: when $p \equiv 2 \pmod{3}$ and $p > 2$, the "middle third"
$(p/3, 2p/3]$ in $\mathbb{Z}/p\mathbb{Z}$ is sum-free, i.e., the sum of two elements of
this interval lies outside it. -/
lemma middleThird_sumFree {p : ℕ} [NeZero p] (hp3 : p % 3 = 2) (hp2 : 2 < p)
    {a b : ZMod p}
    (ha1 : p / 3 < ZMod.val a) (ha2 : ZMod.val a ≤ 2 * p / 3)
    (hb1 : p / 3 < ZMod.val b) (hb2 : ZMod.val b ≤ 2 * p / 3) :
    ¬(p / 3 < ZMod.val (a + b) ∧ ZMod.val (a + b) ≤ 2 * p / 3) := by
  rw [ZMod.val_add]
  have hav := ZMod.val_lt a
  have hbv := ZMod.val_lt b
  obtain ⟨m, hm⟩ : ∃ m, p = 3 * m + 2 := ⟨p / 3, by omega⟩
  subst hm
  have hpd : (3 * m + 2) / 3 = m := by omega
  have h2pd : 2 * (3 * m + 2) / 3 = 2 * m + 1 := by omega
  simp only [hpd, h2pd] at ha1 ha2 hb1 hb2 ⊢
  intro ⟨h1, h2⟩
  by_cases hc : a.val + b.val < 3 * m + 2
  · have hmod : (a.val + b.val) % (3 * m + 2) = a.val + b.val := Nat.mod_eq_of_lt hc
    rw [hmod] at h1 h2; omega
  · have hge : 3 * m + 2 ≤ a.val + b.val := by omega
    have hmod : (a.val + b.val) % (3 * m + 2) = a.val + b.val - (3 * m + 2) := by
      rw [Nat.mod_eq_sub_mod hge]; exact Nat.mod_eq_of_lt (by omega)
    rw [hmod] at h1 h2; omega

/-- For a nonzero $a \in \mathbb{Z}/p\mathbb{Z}$ (with $p$ prime) and any subset $B$,
right-multiplication by $a$ is a bijection, so $|\{t : t a \in B\}| = |B|$. -/
lemma card_filter_mul_right {p : ℕ} [Fact (Nat.Prime p)] {a : ZMod p} (ha : a ≠ 0)
    (B : Finset (ZMod p)) :
    (Finset.univ.filter (fun t : ZMod p => t * a ∈ B)).card = B.card := by
  rw [show (Finset.univ.filter (fun t : ZMod p => t * a ∈ B)) =
    B.map ⟨(· * a⁻¹), mul_left_injective₀ (inv_ne_zero ha)⟩ from by
    ext t
    simp only [mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
    constructor
    · intro ht; exact ⟨t * a, ht, by rw [mul_assoc, mul_inv_cancel₀ ha, mul_one]⟩
    · intro ⟨y, hy, hyt⟩; rw [← hyt, mul_assoc, inv_mul_cancel₀ ha, mul_one]; exact hy]
  exact Finset.card_map _

/-- The number of elements of $\mathbb{Z}/p\mathbb{Z}$ whose canonical representative
lies in the integer interval $(a, b]$ equals $b - a$, provided $b < p$. -/
lemma card_filter_val_Ioc (p : ℕ) [NeZero p] (a b : ℕ) (hb : b < p) :
    (Finset.univ.filter (fun x : ZMod p => a < ZMod.val x ∧ ZMod.val x ≤ b)).card = b - a := by
  have key : (Finset.univ.filter (fun x : ZMod p => a < ZMod.val x ∧ ZMod.val x ≤ b)) =
    ((Finset.Ioc a b).image (fun n : ℕ => (n : ZMod p))) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_image, Finset.mem_Ioc]
    exact ⟨fun ⟨h1, h2⟩ => ⟨ZMod.val x, ⟨h1, h2⟩, ZMod.natCast_zmod_val x⟩,
           fun ⟨n, ⟨hn1, hn2⟩, hnx⟩ => by
             rw [← hnx, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : n < p)]; exact ⟨hn1, hn2⟩⟩
  rw [key, Finset.card_image_of_injOn (fun x hx y hy hxy => by
    have hxm := (Finset.mem_Ioc.mp hx).2
    have hym := (Finset.mem_Ioc.mp hy).2
    have h := congr_arg ZMod.val hxy
    rwa [ZMod.val_natCast, ZMod.val_natCast,
         Nat.mod_eq_of_lt (show x < p by omega), Nat.mod_eq_of_lt (show y < p by omega)] at h)]
  exact Nat.card_Ioc a b

/-- Double-counting identity: summing over $t \in \mathbb{Z}/p\mathbb{Z}$ the number of
$a \in A$ with $t \cdot a \in B$ equals $|A| \cdot |B|$, when every element of $A$ is
nonzero mod $p$. -/
lemma double_count {p : ℕ} [Fact (Nat.Prime p)] (A : Finset ℤ) (B : Finset (ZMod p))
    (hA : ∀ a ∈ A, (a : ZMod p) ≠ 0) :
    ∑ t : ZMod p, (A.filter (fun a : ℤ => t * (a : ZMod p) ∈ B)).card = A.card * B.card := by
  have step1 : ∀ t : ZMod p, (A.filter (fun a : ℤ => t * (a : ZMod p) ∈ B)).card =
    ∑ a ∈ A, if t * (a : ZMod p) ∈ B then 1 else 0 := fun t => Finset.card_filter _ A
  simp_rw [step1, Finset.sum_comm (s := Finset.univ) (t := A)]
  have step2 : ∀ a ∈ A, ∑ t : ZMod p, (if t * (a : ZMod p) ∈ B then 1 else 0 : ℕ) = B.card := by
    intro a ha
    have h := card_filter_mul_right (hA a ha) B
    rw [Finset.card_filter] at h; exact h
  rw [Finset.sum_congr rfl step2, Finset.sum_const, smul_eq_mul]

/-- If a nonzero integer $a$ has $|a| < p$ (where $p$ is prime), then $a$ is nonzero
modulo $p$. -/
lemma intCast_ne_zero_of_lt {p : ℕ} [Fact (Nat.Prime p)] {a : ℤ}
    (ha : a ≠ 0) (hap : a.natAbs < p) : (a : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  intro hdvd
  have h1 : (p : ℤ) ≤ |a| := Int.le_of_dvd (abs_pos.mpr ha) ((dvd_abs _ _).mpr hdvd)
  rw [Int.abs_eq_natAbs] at h1
  exact absurd (show (a.natAbs : ℤ) < (p : ℤ) from by exact_mod_cast hap) (not_lt.mpr h1)

/-- **The classical strict one-third bound.** Every nonempty finite set
`A` of nonzero integers contains a sum-free `S ⊆ A` with `|A| < 3|S|`.
Erdős (1965), Theorem 2, gives the original one-third result; the strict
bound is stated by Alon--Kleitman (1990), Propositions 1.1 and 1.2.
The proof uses dilation modulo a prime `p ≡ 2 [MOD 3]` and averaging
across the middle third of `ZMod p`. -/
theorem erdos_sumFree_strict (A : Finset ℤ) (hA : ∀ a ∈ A, a ≠ 0)
    (hAne : A.Nonempty) :
    ∃ S ⊆ A, IsSumFree S ∧ A.card < 3 * S.card := by
  classical
  set M := A.sup' hAne (fun a => a.natAbs)

  have hprime_exists : ∃ p : ℕ, Nat.Prime p ∧ p % 3 = 2 ∧ M < p ∧ 4 < p := by
    have hinf := Nat.infinite_setOfPred_prime_and_eq_mod (a := (2 : ZMod 3)) (by decide)
    obtain ⟨p, hp, hN⟩ := hinf.exists_gt (max M 4)
    exact ⟨p, hp.1, (congr_arg ZMod.val hp.2).trans rfl, by omega, by omega⟩
  obtain ⟨p, hpp, hp3, hpM, hp4⟩ := hprime_exists
  have : Fact (Nat.Prime p) := ⟨hpp⟩
  have hp2 : 2 < p := by omega

  have hAmod : ∀ a ∈ A, (a : ZMod p) ≠ 0 := fun a ha =>
    intCast_ne_zero_of_lt (hA a ha) (Nat.lt_of_le_of_lt (Finset.le_sup' _ ha) hpM)

  set B := Finset.univ.filter (fun x : ZMod p => p / 3 < ZMod.val x ∧ ZMod.val x ≤ 2 * p / 3)

  have hBcard : B.card = 2 * p / 3 - p / 3 := card_filter_val_Ioc p (p / 3) (2 * p / 3) (by omega)
  have h0B : (0 : ZMod p) ∉ B := by
    simp only [B, mem_filter, mem_univ, true_and, ZMod.val_zero]
    omega

  have hsum : ∑ t : ZMod p, (A.filter (fun a : ℤ => t * (a : ZMod p) ∈ B)).card =
    A.card * B.card := double_count A B hAmod

  set f : ZMod p → ℕ := fun t => (A.filter (fun a : ℤ => t * (a : ZMod p) ∈ B)).card
  have hf : ∑ t : ZMod p, f t = A.card * B.card := hsum
  have hBlarge : p < 3 * B.card := by
    rw [hBcard]
    omega
  have havg : ∃ t : ZMod p, A.card < 3 * f t := by
    by_contra H
    push Not at H
    have hle : (∑ t : ZMod p, 3 * f t) ≤ ∑ _t : ZMod p, A.card := by
      exact Finset.sum_le_sum (fun t _ => H t)
    rw [← Finset.mul_sum, hf] at hle
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul] at hle
    have hpos : 0 < A.card := Finset.card_pos.mpr hAne
    nlinarith
  obtain ⟨t, ht_card⟩ := havg

  refine ⟨A.filter (fun a : ℤ => t * (a : ZMod p) ∈ B), Finset.filter_subset _ _, ?_, ht_card⟩
  intro a ha b hb c hc habc
  simp only [mem_filter] at ha hb hc
  have htc_eq : t * (c : ZMod p) = t * (a : ZMod p) + t * (b : ZMod p) := by
    rw [← habc]; push_cast; ring
  rw [htc_eq] at hc
  simp only [B, mem_filter, mem_univ, true_and] at ha hb hc
  exact middleThird_sumFree hp3 hp2 ha.2.1 ha.2.2 hb.2.1 hb.2.2 hc.2

end Atlas792

namespace Construction792
/-- Classical one-third theorem, with no natural-number floor weakening. -/
theorem erdos_one_third (A : Finset ℤ) (h0 : 0 ∉ A) :
    ∃ B ⊆ A, (∀ a ∈ B, ∀ b ∈ B, a+b ∉ B) ∧ A.card ≤ 3*B.card := by
  classical
  rcases A.eq_empty_or_nonempty with he | hn
  · subst A
    exact ⟨∅, by simp, by simp, by simp⟩
  · obtain ⟨B,hB,hs,hc⟩ := Atlas792.erdos_sumFree_strict A
      (by intro a ha h; exact h0 (h ▸ ha)) hn
    refine ⟨B,hB,?_,Nat.le_of_lt hc⟩
    intro a ha b hb hab
    exact hs a ha b hb (a+b) hab rfl
#print axioms erdos_one_third
#print axioms Atlas792.erdos_sumFree_strict
end Construction792

