/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ErdosProblems.Erdos799
import ListColoring799
import Proportion799

open Filter
open scoped Topology

namespace Erdos799Bridge

/-- The shared list-colouring predicate has exactly the source semantics. -/
theorem choosable_iff {V : Type*} (G : SimpleGraph V) (k : ℕ) :
    G.IsKChoosable k ↔ Erdos753.IsKChoosable G k := Iff.rfl

/-- The shared and source definitions of the minimum are definitionally equal. -/
theorem listChromaticNumber_eq {V : Type*} (G : SimpleGraph V) :
    G.listChromaticNumber = Erdos753.listChromaticNumber G := rfl

/-- Uniform proportions count exactly the same labelled graphs as the source density. -/
theorem graphDensity_eq_proportion
    (P : (n : ℕ) → SimpleGraph (Fin n) → Prop) (n : ℕ) :
    Erdos799.graphDensity P n = SimpleGraph.proportion (P n) := by
  classical
  unfold Erdos799.graphDensity SimpleGraph.proportion
  simp only [← Fintype.card_subtype, Fintype.card_eq_nat_card]

/-- Finite graphs attain their minimum list-colouring bound; no empty-infimum convention is used. -/
theorem listChromaticNumber_attained {V : Type*} [Finite V] (G : SimpleGraph V) :
    G.IsKChoosable G.listChromaticNumber := by
  classical
  change Erdos753.IsKChoosable G (Erdos753.listChromaticNumber G)
  exact Nat.sInf_mem (Erdos753.choosable_set_nonempty G)

/-- The full affirmative answer with the shared list-colouring and proportion interfaces. -/
theorem erdos_799 :
    ∃ b : ℕ → ℕ,
      (fun n : ℕ ↦ (b n : ℝ)) =o[atTop] (fun n : ℕ ↦ (n : ℝ)) ∧
      Tendsto (fun n : ℕ ↦ SimpleGraph.proportion
        (fun G : SimpleGraph (Fin n) ↦ G.listChromaticNumber ≤ b n))
        atTop (nhds 1) := by
  obtain ⟨b, hb, hprob⟩ := Erdos799.erdos_799
  refine ⟨b, hb, ?_⟩
  change Tendsto (fun n : ℕ ↦ Erdos799.graphDensity
    (fun n G ↦ Erdos753.listChromaticNumber G ≤ b n) n) atTop (nhds 1) at hprob
  simpa only [graphDensity_eq_proportion, listChromaticNumber_eq] using hprob

end Erdos799Bridge
