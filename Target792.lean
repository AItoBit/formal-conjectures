/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Main792
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Erdős 792: unresolved target and literature statements

These are proposition definitions, not claimed proofs. The proved classical
bounds are in Main792. Determining an explicit sharp order for the excess is
the remaining target. No existential witness or proof of that target is asserted.
-/

@[expose] public section

open Filter Topology

namespace Erdos792

/-- A proposed positive function describes the sharp order of the excess. -/
def SharpExcessOrder (r : ℕ → ℝ) : Prop :=
  (∀ᶠ n in atTop, 0 < r n) ∧
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n in atTop,
      c * r n ≤ (f n : ℝ) - (n : ℝ) / 3 ∧
      (f n : ℝ) - (n : ℝ) / 3 ≤ C * r n

/-- The established leading term; its deep upper-bound proof is not reproduced here. -/
def KnownLeadingTerm : Prop :=
  Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ)) atTop (nhds (1 / 3 : ℝ))

/-- The quantitative improvement due to Bedert; not proved in this development. -/
def KnownBedertBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    (n : ℝ) / 3 + c * Real.log (Real.log (n : ℝ)) ≤ (f n : ℝ)

end Erdos792
