/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Bridge802
import Variants802

open Real

namespace Erdos802Bridge

open scoped Classical in
/-- The exact repository variant, deduced from the complete main bound. -/
theorem erdos_802.variants.aeks : ∀ r : ℕ, ∃ c > (0 : ℝ), ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    G.CliqueFree r →
      c * (log (log (G.averageDegree + 1)) / G.averageDegree) * n ≤ G.indepNum :=
  Erdos802Variants.aeks_of_main erdos_802

open scoped Classical in
/-- The exact repository variant, deduced from the complete main bound. -/
theorem erdos_802.variants.shearer : ∀ r : ℕ, ∃ c > (0 : ℝ), ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    G.CliqueFree r → 2 ≤ G.averageDegree →
      c * (log G.averageDegree / (log (log (G.averageDegree + 1)) * G.averageDegree)) * n ≤
        G.indepNum :=
  Erdos802Variants.shearer_of_main erdos_802

open scoped Classical in
/-- The exact repository variant, deduced from the complete main bound. -/
theorem erdos_802.variants.r_eq_three : ∃ c > (0 : ℝ), ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    G.CliqueFree 3 →
      c * (log G.averageDegree / G.averageDegree) * n ≤ G.indepNum :=
  Erdos802Variants.r_eq_three_of_main erdos_802

open scoped Classical in
/-- The exact repository variant, deduced from the complete main bound. -/
theorem erdos_802.variants.alon : ∀ r : ℕ, ∃ c > (0 : ℝ), ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    (∀ v, (G.induce (G.neighborSet v)).Colorable (r - 2)) →
      c * (log G.averageDegree / G.averageDegree) * n ≤ G.indepNum :=
  Erdos802Variants.alon_of_main erdos_802

end Erdos802Bridge
