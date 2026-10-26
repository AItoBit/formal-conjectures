/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OAI.Combinatorics.CliqueFree.Main
import FCDefinitions802

open scoped BigOperators
open Finset
open OAI.CliqueFreeIndependence.WeightedGraph

namespace Erdos802Bridge

open scoped Classical in
/-- The repository's rational average degree equals the release's real average degree. -/
theorem averageDegree_cast {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    (G.averageDegree : ℝ) = OAI.CliqueFreeLog.averageDegree G := by
  classical
  simp only [SimpleGraph.averageDegree, OAI.CliqueFreeLog.averageDegree,
    Rat.cast_div, Rat.cast_sum, Rat.cast_natCast]
  have hsum := OAI.CliqueFreeLog.sum_degrees_real G
  exact congrArg (fun x : ℝ => x / (Fintype.card V : ℝ)) hsum

/-- Extend the released theorem to every clique size and every average degree. -/
theorem all_degrees_bound (r : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
      G.CliqueFree r →
      c * (Fintype.card V : ℝ) * Real.log (OAI.CliqueFreeLog.averageDegree G) /
        OAI.CliqueFreeLog.averageDegree G ≤ (G.indepNum : ℝ) := by
  classical
  let s := max r 4
  have hs : 4 ≤ s := Nat.le_max_right r 4
  have hsk : s - 2 + 2 = s := Nat.sub_add_cancel (by omega)
  obtain ⟨c₁, hc₁, hmain⟩ := OAI.CliqueFreeLog.logarithmic_independence_bound s hs
  obtain ⟨B, hB, htri⟩ := exists_optimizer_triangle_bound.{0} (s - 2)
  let D : ℝ := 3 + 3 * B / 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  let c₂ : ℝ := Real.log 4 / (32 * D)
  have hc₂ : 0 < c₂ := by dsimp [c₂]; positivity
  let c := min c₁ c₂
  have hc : 0 < c := lt_min hc₁ hc₂
  refine ⟨c, hc, ?_⟩
  intro V _ G hf
  have hfs : G.CliqueFree s := SimpleGraph.CliqueFree.mono (Nat.le_max_left r 4) hf
  let d := OAI.CliqueFreeLog.averageDegree G
  have hd0 : 0 ≤ d := by dsimp [d, OAI.CliqueFreeLog.averageDegree]; positivity
  change c * (Fintype.card V : ℝ) * Real.log d / d ≤ (G.indepNum : ℝ)
  by_cases hz : d = 0
  · simp [hz]
  have hdpos : 0 < d := lt_of_le_of_ne hd0 (Ne.symm hz)
  by_cases hd : 2 ≤ d
  · have hb := hmain G hfs hd
    have hfactor : 0 ≤ (Fintype.card V : ℝ) * Real.log d / d := by
      exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))) hd0
    calc
      c * (Fintype.card V : ℝ) * Real.log d / d =
          c * ((Fintype.card V : ℝ) * Real.log d / d) := by ring
      _ ≤ c₁ * ((Fintype.card V : ℝ) * Real.log d / d) :=
        mul_le_mul_of_nonneg_right (min_le_left c₁ c₂) hfactor
      _ = c₁ * (Fintype.card V : ℝ) * Real.log d / d := by ring
      _ ≤ (G.indepNum : ℝ) := hb
  have hdlt : d < 2 := lt_of_not_ge hd
  have hn : (Fintype.card V : ℝ) ≠ 0 := by
    intro he
    have : d = 0 := by simp [d, OAI.CliqueFreeLog.averageDegree, he]
    exact hz this
  have hsum : (∑ v, (G.degree v : ℝ)) = (Fintype.card V : ℝ) * d := by
    rw [OAI.CliqueFreeLog.sum_degrees_real]
    dsimp [d, OAI.CliqueFreeLog.averageDegree]
    field_simp
  let A : Finset V := univ.filter fun v ↦ (G.degree v : ℝ) ≤ 2 * d
  have hAcard : (Fintype.card V : ℝ) / 2 ≤ (Fintype.card (A : Set V) : ℝ) := by
    have he : Fintype.card (A : Set V) = A.card := Fintype.card_coe A
    rw [he]
    exact degree_cutoff_card G hdpos hsum
  have hfree : (G.induce (A : Set V)).CliqueFree (s - 2 + 2) := by
    rw [hsk]
    exact (G.cliqueFree_induce_iff _ _).2 hfs.cliqueFreeOn
  have hdeg (v : (A : Set V)) : ((G.induce (A : Set V)).degree v : ℝ) ≤ 4 := by
    have hv : (G.degree v : ℝ) ≤ 2 * d := (mem_filter.mp v.property).2
    have hi := Nat.cast_le (α := ℝ).mpr (degree_induce_le G A v)
    linarith
  have hmax := maximum_degree_independence (s - 2) hB.le (by norm_num : (3 : ℝ) ≤ 4)
    htri (G.induce (A : Set V)) hfree hdeg
  have hi : ((G.induce (A : Set V)).indepNum : ℝ) ≤ (G.indepNum : ℝ) :=
    Nat.cast_le.mpr (indepNum_induce_le G A)
  have hden : 4 * (3 + 3 * B / 2) * 4 = 16 * D := by dsimp [D]; ring
  rw [hden] at hmax
  have hnum : (Fintype.card V : ℝ) * Real.log 4 / 2 ≤
      (Fintype.card (A : Set V) : ℝ) * Real.log 4 := by
    have hh := mul_le_mul_of_nonneg_right hAcard hlog4.le
    nlinarith
  have hquot := div_le_div_of_nonneg_right hnum (by positivity : (0 : ℝ) ≤ 16 * D)
  have hstrong : c₂ * (Fintype.card V : ℝ) ≤ (G.indepNum : ℝ) := by
    calc
      c₂ * (Fintype.card V : ℝ) =
          ((Fintype.card V : ℝ) * Real.log 4 / 2) / (16 * D) := by
        dsimp [c₂]
        field_simp
        ring
      _ ≤ (Fintype.card (A : Set V) : ℝ) * Real.log 4 / (16 * D) := hquot
      _ ≤ (G.indepNum : ℝ) := hmax.trans hi
  have hratio : Real.log d / d ≤ 1 := by
    apply (div_le_one hdpos).mpr
    have hh := Real.log_le_sub_one_of_pos hdpos
    linarith
  calc
    c * (Fintype.card V : ℝ) * Real.log d / d =
        (c * (Fintype.card V : ℝ)) * (Real.log d / d) := by ring
    _ ≤ c * (Fintype.card V : ℝ) :=
      mul_le_of_le_one_right (mul_nonneg hc.le (Nat.cast_nonneg _)) hratio
    _ ≤ c₂ * (Fintype.card V : ℝ) :=
      mul_le_mul_of_nonneg_right (min_le_right c₁ c₂) (Nat.cast_nonneg _)
    _ ≤ (G.indepNum : ℝ) := hstrong

open scoped Classical in
/-- The exact original repository statement, without restrictions on clique size or degree. -/
theorem erdos_802 : ∀ r : ℕ, ∃ c > (0 : ℝ), ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    G.CliqueFree r →
      c * (Real.log G.averageDegree / G.averageDegree) * n ≤ G.indepNum := by
  classical
  intro r
  obtain ⟨c, hc, hb⟩ := all_degrees_bound r
  refine ⟨c, hc, ?_⟩
  intro n G hf
  have hh := hb G hf
  rw [← averageDegree_cast] at hh
  simpa only [Fintype.card_fin, mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using hh

end Erdos802Bridge
