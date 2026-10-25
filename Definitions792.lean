/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Find
public import Mathlib.Tactic

@[expose] public section

namespace Erdos792

/-- Repeated summands are allowed in the forbidden equation. -/
def SumFree (B : Finset ℤ) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, a + b ∉ B

/-- The literal website convention, allowing zero in the ambient set. -/
def Guarantees (n k : ℕ) : Prop :=
  ∀ A : Finset ℤ, A.card = n →
    ∃ B ⊆ A, SumFree B ∧ k ≤ B.card

/-- The nonzero-integer convention used by the cited literature. -/
def GuaranteesNonzero (n k : ℕ) : Prop :=
  ∀ A : Finset ℤ, 0 ∉ A → A.card = n →
    ∃ B ⊆ A, SumFree B ∧ k ≤ B.card

theorem SumFree.zero_not_mem {B : Finset ℤ} (hB : SumFree B) : 0 ∉ B := by
  intro hz
  exact hB 0 hz 0 hz (by simpa using hz)

theorem guarantees_zero (n : ℕ) : Guarantees n 0 := by
  intro A _
  exact ⟨∅, Finset.empty_subset _, by simp [SumFree], by simp⟩

theorem guaranteesNonzero_zero (n : ℕ) : GuaranteesNonzero n 0 := by
  intro A _ _
  exact ⟨∅, Finset.empty_subset _, by simp [SumFree], by simp⟩

theorem guarantees_succ_iff (n k : ℕ) :
    Guarantees (n + 1) k ↔ GuaranteesNonzero n k := by
  constructor
  · intro h A hz hcard
    obtain ⟨B, hBA, hB, hk⟩ := h (insert 0 A) (by simp [hz, hcard])
    refine ⟨B, ?_, hB, hk⟩
    intro b hb
    rcases Finset.mem_insert.mp (hBA hb) with rfl | hmem
    · exact (hB.zero_not_mem hb).elim
    · exact hmem
  · intro h A hcard
    have he : n ≤ (A.erase 0).card := by
      by_cases hz : 0 ∈ A
      · rw [Finset.card_erase_of_mem hz, hcard]
        omega
      · rw [Finset.erase_eq_of_notMem hz, hcard]
        omega
    obtain ⟨C, hC, hCcard⟩ := Finset.exists_subset_card_eq he
    obtain ⟨B, hBC, hB, hk⟩ := h C (by
      intro hz
      exact Finset.notMem_erase 0 A (hC hz)) hCcard
    exact ⟨B, hBC.trans (hC.trans (Finset.erase_subset _ _)), hB, hk⟩

theorem card_positive_interval (n : ℕ) :
    (Finset.Icc (1 : ℤ) (n : ℤ)).card = n := by
  simp [Int.card_Icc]

theorem guarantees_le {n k : ℕ} (h : Guarantees n k) : k ≤ n := by
  obtain ⟨B, hB, _, hk⟩ := h (Finset.Icc 1 (n : ℤ)) (card_positive_interval n)
  exact hk.trans ((Finset.card_le_card hB).trans_eq (card_positive_interval n))

theorem guaranteesNonzero_le {n k : ℕ} (h : GuaranteesNonzero n k) : k ≤ n := by
  obtain ⟨B, hB, _, hk⟩ := h (Finset.Icc 1 (n : ℤ)) (by simp) (card_positive_interval n)
  exact hk.trans ((Finset.card_le_card hB).trans_eq (card_positive_interval n))

/-- Largest universally guaranteed cardinality with zero permitted. -/
noncomputable def f (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (Guarantees n) n

/-- Largest universally guaranteed cardinality for nonzero integer sets. -/
noncomputable def fNonzero (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (GuaranteesNonzero n) n

theorem f_spec (n : ℕ) : Guarantees n (f n) := by
  classical
  exact Nat.findGreatest_spec (Nat.zero_le n) (guarantees_zero n)

theorem fNonzero_spec (n : ℕ) : GuaranteesNonzero n (fNonzero n) := by
  classical
  exact Nat.findGreatest_spec (Nat.zero_le n) (guaranteesNonzero_zero n)

theorem le_f_of_guarantees {n k : ℕ} (h : Guarantees n k) : k ≤ f n := by
  classical
  exact Nat.le_findGreatest (guarantees_le h) h

theorem le_fNonzero_of_guarantees {n k : ℕ} (h : GuaranteesNonzero n k) :
    k ≤ fNonzero n := by
  classical
  exact Nat.le_findGreatest (guaranteesNonzero_le h) h

theorem f_succ (n : ℕ) : f (n + 1) = fNonzero n := by
  apply Nat.le_antisymm
  · exact le_fNonzero_of_guarantees ((guarantees_succ_iff n _).mp (f_spec (n + 1)))
  · exact le_f_of_guarantees ((guarantees_succ_iff n _).mpr (fNonzero_spec n))

theorem f_zero : f 0 = 0 := by
  classical
  simp [f]

theorem fNonzero_zero : fNonzero 0 = 0 := by
  classical
  simp [fNonzero]

theorem f_one : f 1 = 0 := by
  simpa using (f_succ 0).trans fNonzero_zero

#print axioms f_succ
#print axioms f_one

end Erdos792
