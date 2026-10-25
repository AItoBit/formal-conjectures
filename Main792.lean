/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Definitions792
public import Construction792
public import Upper792
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

@[expose] public section

open scoped Pointwise

/-- The definition used in Formal Conjectures, copied to make the linked proof standalone. -/
def IsSumFree {M : Type*} [Add M] (S : Set M) : Prop := Disjoint (S + S) S

theorem isSumFree_iff {M : Type*} [Add M] {S : Set M} :
    IsSumFree S ↔ ∀ x ∈ S, ∀ y ∈ S, x + y ∉ S := by
  simp [IsSumFree, Set.disjoint_left, Set.mem_add]
  aesop

namespace Erdos792

theorem sumFree_iff (B : Finset ℤ) : SumFree B ↔ IsSumFree (B : Set ℤ) := by
  rw [isSumFree_iff]
  rfl

/-- The strict classical bound; this is the Alon--Kleitman improvement. -/
theorem strict_nonzero_bound (A : Finset ℤ) (h0 : 0 ∉ A) (hne : A.Nonempty) :
    ∃ B ⊆ A, IsSumFree (B : Set ℤ) ∧ A.card < 3 * B.card := by
  obtain ⟨B, hBA, hB, hc⟩ := Atlas792.erdos_sumFree_strict A
    (by intro a ha he; exact h0 (he ▸ ha)) hne
  refine ⟨B, hBA, (sumFree_iff B).mp ?_, hc⟩
  intro a ha b hb hab
  exact hB a ha b hb (a + b) hab rfl

theorem guaranteesNonzero_strict (n : ℕ) (hn : 0 < n) :
    GuaranteesNonzero n (n / 3 + 1) := by
  intro A h0 hcard
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨B, hBA, hB, hc⟩ := strict_nonzero_bound A h0 hne
  refine ⟨B, hBA, (sumFree_iff B).mpr hB, ?_⟩
  omega

theorem nonzero_f_lower (n : ℕ) (hn : 0 < n) : n + 1 ≤ 3 * fNonzero n := by
  have h := le_fNonzero_of_guarantees (guaranteesNonzero_strict n hn)
  omega

theorem literal_f_lower (n : ℕ) (hn : 2 ≤ n) : n ≤ 3 * f n := by
  cases n with
  | zero => omega
  | succ m =>
    rw [f_succ]
    exact nonzero_f_lower m (by omega)

/-- A verified lower bound for the literal domain, including sets containing zero. -/
theorem literal_lower_bound (n : ℕ) (hn : 2 ≤ n) (A : Finset ℤ) (hcard : A.card = n) :
    ∃ B ⊆ A, IsSumFree (B : Set ℤ) ∧ n ≤ 3 * B.card := by
  obtain ⟨B, hBA, hB, hc⟩ := f_spec n A hcard
  have hb := literal_f_lower n hn
  exact ⟨B, hBA, (sumFree_iff B).mp hB, by omega⟩

/-- An explicit interval witnesses the elementary upper bound for every input size. -/
theorem literal_upper_bound (n : ℕ) :
    ∃ A : Finset ℤ, A.card = n ∧
      ∀ B ⊆ A, IsSumFree (B : Set ℤ) → 2 * B.card ≤ n := by
  cases n with
  | zero =>
    refine ⟨∅, by simp, ?_⟩
    intro B hB _
    have hBe : B = ∅ := Finset.subset_empty.mp hB
    simp [hBe]
  | succ m =>
    refine ⟨Finset.Icc 0 (m : ℤ), by simp [Int.card_Icc], ?_⟩
    intro B hBA hB
    have hs : SumFree B := (sumFree_iff B).mpr hB
    have hB' : B ⊆ Finset.Icc (1 : ℤ) (m : ℤ) := by
      intro b hb
      have hb' := Finset.mem_Icc.mp (hBA hb)
      have hb0 : b ≠ 0 := by
        intro he
        exact hs.zero_not_mem (he ▸ hb)
      exact Finset.mem_Icc.mpr ⟨by omega, hb'.2⟩
    exact interval_sumFree_card_bound m B hB' hs

theorem literal_f_upper (n : ℕ) : 2 * f n ≤ n := by
  obtain ⟨A, hA, hb⟩ := literal_upper_bound n
  obtain ⟨B, hBA, hB, hc⟩ := f_spec n A hA
  have hu := hb B hBA ((sumFree_iff B).mp hB)
  omega

#print axioms strict_nonzero_bound
#print axioms literal_lower_bound
#print axioms literal_upper_bound
#print axioms literal_f_lower
#print axioms literal_f_upper

end Erdos792
