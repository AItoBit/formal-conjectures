import Erdos797
import Statement797
import Bounds797

namespace Erdos797Statement

theorem acyclicColorable_iff {V : Type*} (G : SimpleGraph V) (k : ℕ) :
    G.AcyclicColorable k ↔ ∃ c : V → Fin k, Erdos797.IsAcyclicColoring G c := by
  rw [SimpleGraph.acyclicColorable_iff_exists]
  constructor
  · rintro ⟨c, hp, hc⟩
    exact ⟨c, hp, fun {v} w hw => hc v w hw⟩
  · rintro ⟨c, hp, hc⟩
    exact ⟨c, hp, fun v w hw => hc w hw⟩

theorem f_eq (d : ℕ) : f d = Erdos797.extremalAcyclicNumber d := by
  classical
  unfold f Erdos797.extremalAcyclicNumber Erdos797.AcyclicBound Erdos797.graphMaxDegree
  congr 1
  ext k
  simp only [Set.mem_ofPred_eq, acyclicColorable_iff]

theorem parts_i : BoundsTarget := by
  simpa only [BoundsTarget, f_eq] using Erdos797Bounds.bounds

theorem parts_ii : True ↔ LittleOTarget := by
  rw [true_iff]
  simpa only [LittleOTarget, f_eq] using Erdos797.erdos_797.2.2

open scoped Classical in
/-- The extremal palette is actually attained as a universal bound. -/
theorem f_spec (d : ℕ) (n : ℕ) (G : SimpleGraph (Fin n)) (hG : G.maxDegree ≤ d) :
    G.AcyclicColorable (f d) := by
  rw [f_eq, acyclicColorable_iff]
  exact Erdos797.LowerBound.extremalAcyclicNumber_spec d n G hG

end Erdos797Statement


