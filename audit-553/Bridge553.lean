import ErdosProblems.Erdos553
import Proposed553

/-! Explicit equivalence bridge for the exact proposed problem 553 statement. -/

open Filter SimpleGraph

namespace Bridge553

lemma classicalRamsey_eq (n : ℕ) :
    classicalRamsey 3 n = Erdos553.twoColorRamseyNumber n := by
  unfold classicalRamsey graphRamsey Erdos553.twoColorRamseyNumber
  congr 1
  ext N
  simp only [Set.mem_ofPred_eq, Ramsey.RamseyProperty]
  refine forall_congr' fun C => ?_
  rw [← not_cliqueFree_iff_top_isContained, ← not_cliqueFree_iff_top_isContained,
    cliqueFree_compl, not_and_or]

lemma fin3_eq_two (k : Fin 3) (h0 : k ≠ 0) (h1 : k ≠ 1) : k = 2 := by
  revert k; decide

lemma prop_iff (m n : ℕ) :
    (∀ C : TopEdgeLabeling (Fin m) (Fin 3), ¬ (C.labelGraph 0).CliqueFree 3 ∨
        ¬ (C.labelGraph 1).CliqueFree 3 ∨ ¬ (C.labelGraph 2).CliqueFree n) ↔
      Erdos553.ThreeColorRamseyProperty n m := by
  unfold Erdos553.ThreeColorRamseyProperty
  constructor
  · rintro h red blue ⟨hr, hb, hi⟩
    classical
    let C : TopEdgeLabeling (Fin m) (Fin 3) :=
      EdgeLabeling.mk (fun x y _ => if red.Adj x y then 0 else if blue.Adj x y then 1 else 2)
        (by intro x y _; simp only [red.adj_comm, blue.adj_comm])
    have hget : ∀ x y (h : x ≠ y), C.get x y h =
        if red.Adj x y then 0 else if blue.Adj x y then 1 else 2 := fun x y h => rfl
    rcases h C with h0 | h1 | h2
    · refine h0 (hr.anti fun x y hxy => ?_)
      obtain ⟨hne, hk⟩ := (TopEdgeLabeling.labelGraph_adj x y).1 hxy
      rw [hget] at hk
      by_contra hn
      simp only [hn, if_false] at hk
      split_ifs at hk <;> simp at hk
    · refine h1 (hb.anti fun x y hxy => ?_)
      obtain ⟨hne, hk⟩ := (TopEdgeLabeling.labelGraph_adj x y).1 hxy
      rw [hget] at hk
      by_contra hn
      simp only [hn, if_false] at hk
      split_ifs at hk <;> simp at hk
    · rw [← cliqueFree_compl] at hi
      refine h2 (hi.anti fun x y hxy => ?_)
      obtain ⟨hne, hk⟩ := (TopEdgeLabeling.labelGraph_adj x y).1 hxy
      rw [hget] at hk
      simp only [compl_adj, sup_adj, not_or]
      refine ⟨hne, fun hn => ?_, fun hn => ?_⟩
      · simp only [hn, if_true] at hk
        exact absurd hk (by decide)
      · simp only [hn, if_true] at hk
        split_ifs at hk <;> simp at hk
  · intro h C
    by_contra hcon
    push Not at hcon
    obtain ⟨h0, h1, h2⟩ := hcon
    refine h (C.labelGraph 0) (C.labelGraph 1) ⟨h0, h1, ?_⟩
    rw [← cliqueFree_compl]
    refine h2.anti fun x y hxy => ?_
    simp only [compl_adj, sup_adj, not_or, TopEdgeLabeling.labelGraph_adj, not_exists] at hxy
    obtain ⟨hne, hk0, hk1⟩ := hxy
    exact (TopEdgeLabeling.labelGraph_adj x y).2 ⟨hne, fin3_eq_two _ (hk0 hne) (hk1 hne)⟩

lemma ramsey33_eq (n : ℕ) : Erdos553Proposed.ramsey33 n = Erdos553.threeColorRamseyNumber n := by
  unfold Erdos553Proposed.ramsey33 Erdos553.threeColorRamseyNumber
  congr 1
  ext m
  simp only [Set.mem_ofPred_eq]
  exact prop_iff m n

theorem erdos_553 :
    Tendsto (fun n : ℕ ↦ (Erdos553Proposed.ramsey33 n : ℝ) / classicalRamsey 3 n) atTop atTop := by
  simp only [ramsey33_eq, classicalRamsey_eq]
  exact Erdos553.erdos_553

end Bridge553

theorem proof_553_exact_statement : type_of% Erdos553Proposed.erdos_553 := Bridge553.erdos_553

#print axioms Erdos553.erdos_553
#print axioms proof_553_exact_statement
