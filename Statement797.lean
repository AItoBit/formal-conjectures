import Acyclic797
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Defs

open Filter Real

namespace Erdos797Statement

/-- Least palette that acyclically colours every finite simple graph of degree at most d. -/
noncomputable def f (d : ℕ) : ℕ := by
  classical
  exact sInf {k | ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.maxDegree ≤ d →
    G.AcyclicColorable k}

/-- The two estimates supplied by Alon, McDiarmid and Reed. -/
def BoundsTarget : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ d : ℕ in atTop,
    c * (d : ℝ) ^ (4 / 3 : ℝ) / (log d) ^ (1 / 3 : ℝ) ≤ f d ∧
      (f d : ℝ) ≤ C * (d : ℝ) ^ (4 / 3 : ℝ)

/-- The original particular yes-or-no question. -/
def LittleOTarget : Prop :=
  (fun d : ℕ ↦ (f d : ℝ)) =o[atTop] fun d : ℕ ↦ (d : ℝ) ^ 2

end Erdos797Statement
