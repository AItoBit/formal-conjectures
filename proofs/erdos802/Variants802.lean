/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import FCDefinitions802

namespace Erdos802Variants

open Real

open scoped Classical in
def MainStatement : Prop :=
  ∀ r : ℕ, ∃ c > (0 : ℝ), ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
    G.CliqueFree r →
      c * (log G.averageDegree / G.averageDegree) * n ≤ G.indepNum

lemma averageDegree_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : 0 ≤ (G.averageDegree : ℝ) := by
  simp only [SimpleGraph.averageDegree]
  positivity

open scoped Classical in
theorem aeks_of_main (hmain : MainStatement) :
    ∀ r : ℕ, ∃ c > (0 : ℝ), ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      G.CliqueFree r →
        c * (log (log (G.averageDegree + 1)) / G.averageDegree) * n ≤ G.indepNum := by
  intro r
  obtain ⟨c, hc, h⟩ := hmain r
  refine ⟨c, hc, ?_⟩
  intro n G hG
  have hd := averageDegree_nonneg G
  by_cases hz : (G.averageDegree : ℝ) = 0
  · simp [hz]
  have hp : 0 < (G.averageDegree : ℝ) := lt_of_le_of_ne hd (Ne.symm hz)
  have hin : 0 < log ((G.averageDegree : ℝ) + 1) := log_pos (by linarith)
  have hinner : log ((G.averageDegree : ℝ) + 1) ≤ (G.averageDegree : ℝ) := by
    have ht := log_le_sub_one_of_pos (by linarith : 0 < (G.averageDegree : ℝ) + 1)
    linarith
  have hout := log_le_log hin hinner
  have hratio := div_le_div_of_nonneg_right hout hp.le
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hc.le)
    (Nat.cast_nonneg n)).trans (h n G hG)

open scoped Classical in
theorem r_eq_three_of_main (hmain : MainStatement) :
    ∃ c > (0 : ℝ), ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      G.CliqueFree 3 →
        c * (log G.averageDegree / G.averageDegree) * n ≤ G.indepNum :=
  hmain 3

open scoped Classical in
theorem shearer_of_main (hmain : MainStatement) :
    ∀ r : ℕ, ∃ c > (0 : ℝ), ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      G.CliqueFree r → 2 ≤ G.averageDegree →
        c * (log G.averageDegree / (log (log (G.averageDegree + 1)) * G.averageDegree)) * n ≤
          G.indepNum := by
  intro r
  obtain ⟨c, hc, h⟩ := hmain r
  have hlog3 : 1 < log (3 : ℝ) := by
    calc
      (1 : ℝ) = log (exp 1) := (log_exp 1).symm
      _ < log 3 := log_lt_log (exp_pos 1) (lt_trans Real.exp_one_lt_d9 (by norm_num))
  have hL : 0 < log (log (3 : ℝ)) := log_pos hlog3
  refine ⟨c * log (log (3 : ℝ)), mul_pos hc hL, ?_⟩
  intro n G hG hd
  have hd' : (2 : ℝ) ≤ (G.averageDegree : ℝ) := by exact_mod_cast hd
  have hp : 0 < (G.averageDegree : ℝ) := by linarith
  have hlog : 0 ≤ log (G.averageDegree : ℝ) := log_nonneg (by linarith)
  have hin : log (3 : ℝ) ≤ log ((G.averageDegree : ℝ) + 1) :=
    log_le_log (by norm_num) (by linarith)
  have houter : log (log (3 : ℝ)) ≤ log (log ((G.averageDegree : ℝ) + 1)) :=
    log_le_log (lt_trans (by norm_num) hlog3) hin
  have hden : 0 < log (log ((G.averageDegree : ℝ) + 1)) := hL.trans_le houter
  have hratio : log (log (3 : ℝ)) *
      (log (G.averageDegree : ℝ) /
        (log (log ((G.averageDegree : ℝ) + 1)) * (G.averageDegree : ℝ))) ≤
      log (G.averageDegree : ℝ) / (G.averageDegree : ℝ) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (mul_pos hden hp) hp).mpr
    nlinarith [mul_nonneg (mul_nonneg hlog hp.le) (sub_nonneg.mpr houter)]
  calc
    _ = c * (log (log (3 : ℝ)) * (log (G.averageDegree : ℝ) /
        (log (log ((G.averageDegree : ℝ) + 1)) * (G.averageDegree : ℝ)))) * n := by ring
    _ ≤ c * (log (G.averageDegree : ℝ) / (G.averageDegree : ℝ)) * n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hc.le) (Nat.cast_nonneg n)
    _ ≤ _ := h n G hG

lemma cliqueFree_of_neighborhood_colorable {V : Type*} (G : SimpleGraph V) (r : ℕ)
    (h : ∀ v, (G.induce (G.neighborSet v)).Colorable (r - 2)) : G.CliqueFree (r + 2) := by
  classical
  intro s hs
  have hspos : 0 < s.card := by rw [hs.card_eq]; omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hspos
  let f : ↥(s.erase v) → G.neighborSet v := fun w =>
    ⟨w, hs.isClique hv (Finset.mem_of_mem_erase w.property)
      (Ne.symm (Finset.ne_of_mem_erase w.property))⟩
  have hf : Pairwise fun i j : ↥(s.erase v) => (G.induce (G.neighborSet v)).Adj (f i) (f j) := by
    intro i j hij
    exact hs.isClique (Finset.mem_of_mem_erase i.property) (Finset.mem_of_mem_erase j.property)
      (fun he => hij (Subtype.ext he))
  have hc := (h v).card_le_of_pairwise_adj f hf
  have hcard : Nat.card ↥(s.erase v) = r + 1 := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_erase_of_mem hv, hs.card_eq]
    omega
  rw [hcard] at hc
  omega

open scoped Classical in
theorem alon_of_main (hmain : MainStatement) :
    ∀ r : ℕ, ∃ c > (0 : ℝ), ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      (∀ v, (G.induce (G.neighborSet v)).Colorable (r - 2)) →
        c * (log G.averageDegree / G.averageDegree) * n ≤ G.indepNum := by
  intro r
  obtain ⟨c, hc, h⟩ := hmain (r + 2)
  exact ⟨c, hc, fun n G hG => h n G (cliqueFree_of_neighborhood_colorable G r hG)⟩

end Erdos802Variants
