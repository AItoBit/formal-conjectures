import DistinctSubsetProducts
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.NumberTheory.PrimeCounting

open Filter Real

namespace Erdos795Statement

/-- All subsets, including the empty subset, have different products. -/
abbrev HasDistinctSubsetProducts (A : Finset ℕ) : Prop :=
  A.DecidableDistinctSubsetProducts

/-- Maximum cardinality in the interval [1,n], as in PR #6338. -/
noncomputable def g (n : ℕ) : ℕ :=
  sSup {k | ∃ A ⊆ Finset.Icc 1 n, HasDistinctSubsetProducts A ∧ A.card = k}

/-- The precise upper bound asked in Erdős problem 795. -/
def Target : Prop :=
  ∃ e : ℕ → ℝ, (e =o[atTop] fun n : ℕ ↦ √n / log n) ∧
    ∀ n, (g n : ℝ) ≤ Nat.primeCounting n + Nat.primeCounting (Nat.sqrt n) + e n

end Erdos795Statement
