import Erdos795
import Statement795

open Filter Real

namespace Erdos795Statement

theorem distinctSubsetProducts_iff (A : Finset ℕ) :
    HasDistinctSubsetProducts A ↔ Erdos795.DistinctSubsetProducts A := by
  exact Finset.decidableDistinctSubsetProducts_iff_injOn A

theorem g_eq (n : ℕ) : g n = Erdos795.g n := by
  classical
  unfold g Erdos795.g
  apply le_antisymm
  · refine csSup_le ⟨0, ∅, by simp, ?_, by simp⟩ ?_
    · apply (distinctSubsetProducts_iff ∅).mpr
      exact Erdos795.empty_distinctSubsetProducts
    · rintro k ⟨A, hA, hd, rfl⟩
      exact Finset.le_sup (f := Finset.card)
        (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hA,
          (distinctSubsetProducts_iff A).mp hd⟩)
  · refine Finset.sup_le fun A hA => ?_
    rw [Finset.mem_filter, Finset.mem_powerset] at hA
    refine le_csSup ⟨n, ?_⟩ ⟨A, hA.1, (distinctSubsetProducts_iff A).mpr hA.2, rfl⟩
    rintro k ⟨B, hB, -, rfl⟩
    exact (Finset.card_le_card hB).trans (by simp)

/-- Full solution of the precise conjecture, using the reproduced upstream proof. -/
theorem erdos_795 : True ↔ Target := by
  rw [true_iff]
  refine ⟨fun n => (Erdos795.g n : ℝ) - Nat.primeCounting n -
    Nat.primeCounting (Nat.sqrt n), Erdos795.erdos_795_signed_error_isLittleO, fun n => ?_⟩
  rw [g_eq]
  ring_nf
  exact le_rfl

/-- Matching lower bound from all primes and their squares. -/
theorem baseline (n : ℕ) :
    Nat.primeCounting n + Nat.primeCounting (Nat.sqrt n) ≤ g n := by
  rw [g_eq]
  exact Erdos795.baseline_le_g n

end Erdos795Statement

