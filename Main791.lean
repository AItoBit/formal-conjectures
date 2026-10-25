import Endpoint791
import Construction791

namespace Erdos791

/-- The seven-segment construction gives a strict improvement on the
coefficient two along an unbounded quadratic sequence. -/
theorem seven_segment_bound (t : ℕ) (ht : 2 ≤ t) :
    g (14 * t ^ 2 - 1) ≤ 7 * (t + 1) := by
  let n := 14 * t ^ 2 - 1
  let A := (Construction791.basis t).filter (fun a => a ≤ n)
  have htpos : 0 < t := by omega
  have hp : 0 < 14 * t ^ 2 := by positivity
  have hA : IsBasis n A := by
    constructor
    · intro a ha
      have := (Finset.mem_filter.mp ha).2
      simp only [Finset.mem_Icc]
      omega
    · intro m hm
      have hm' : m < 14 * t ^ 2 := by dsimp [n] at hm; omega
      obtain ⟨a, ha, b, hb, he⟩ := Construction791.covers ht hm'
      exact ⟨a, Finset.mem_filter.mpr ⟨ha, by omega⟩,
        b, Finset.mem_filter.mpr ⟨hb, by omega⟩, he⟩
  exact (g_le_of_basis hA).trans
    ((Finset.card_filter_le _ _).trans (Construction791.card_basis t))

/-- Negative answer to the explicit asymptotic question in Erdős problem 791.
This leaves the sharp asymptotic growth constant unresolved. -/
theorem not_erdos_791 :
    ¬ Filter.Tendsto (fun n : ℕ => (g n : ℝ) / Real.sqrt (n : ℝ))
      Filter.atTop (nhds 2) :=
  not_tendsto_two_of_family seven_segment_bound

end Erdos791

#print axioms Erdos791.seven_segment_bound
#print axioms Erdos791.not_erdos_791
