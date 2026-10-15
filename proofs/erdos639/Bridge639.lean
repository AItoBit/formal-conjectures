/- Exact statement bridges for the attributed Erdős 639 proof. See README.md. -/
import Erdos639
import Mathlib.Order.Filter.AtTopBot.Basic

open scoped Sym2

namespace Erdos639FC

/-- The exact unordered-pair set used by the repository statement. -/
def uncoveredEdges {n : ℕ} (C : Sym2 (Fin n) → Fin 2) : Set (Sym2 (Fin n)) :=
  {e | ¬e.IsDiag ∧ ∀ x y : Fin n, e = s(x, y) →
    ¬∃ z, z ≠ x ∧ z ≠ y ∧ C s(x, z) = C e ∧ C s(y, z) = C e}

theorem uncoveredEdges_eq_edgeSet {n : ℕ} (C : Sym2 (Fin n) → Fin 2) :
    uncoveredEdges C = (Erdos639.SimpleGraph.nimt C).edgeSet := by
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
    change (¬s(x, y).IsDiag ∧ ∀ a b : Fin n, s(x, y) = s(a, b) →
      ¬∃ z, z ≠ a ∧ z ≠ b ∧ C s(a, z) = C s(x, y) ∧ C s(b, z) = C s(x, y)) ↔
      Erdos639.NIMT C x y
    rw [Sym2.mk_isDiag_iff]
    constructor
    · rintro ⟨hne, hbad⟩
      refine ⟨hne, ?_⟩
      rintro ⟨z, hxz, hyz, h₁, h₂⟩
      exact hbad x y rfl ⟨z, hxz.symm, hyz.symm, h₁.symm, h₂.symm⟩
    · rintro ⟨hne, hbad⟩
      refine ⟨hne, ?_⟩
      intro a b hab
      rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rintro ⟨z, hzx, hzy, h₁, h₂⟩
        exact hbad ⟨z, hzx.symm, hzy.symm, h₁.symm, h₂.symm⟩
      · rintro ⟨z, hzy, hzx, h₁, h₂⟩
        exact hbad ⟨z, hzx.symm, hzy.symm, h₂.symm, h₁.symm⟩

theorem uncoveredEdges_ncard {n : ℕ} (C : Sym2 (Fin n) → Fin 2) :
    (uncoveredEdges C).ncard = (Erdos639.SimpleGraph.nimt C).edgeFinset.card := by
  classical
  rw [uncoveredEdges_eq_edgeSet]
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]

theorem bound_ten {n : ℕ} (hn : 10 ≤ n) (C : Sym2 (Fin n) → Fin 2) :
    (uncoveredEdges C).ncard ≤ n ^ 2 / 4 := by
  rw [uncoveredEdges_ncard]
  simpa [Erdos639.SimpleGraph.n] using
    (Erdos639.SimpleGraph.erdos639 (V := Fin n) (C := C)
      (by simpa [Erdos639.SimpleGraph.n] using hn))

theorem asymptotic_bound :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ C : Sym2 (Fin n) → Fin 2,
      (uncoveredEdges C).ncard ≤ n ^ 2 / 4 := by
  filter_upwards [Filter.eventually_ge_atTop 10] with n hn
  exact bound_ten hn

/-- The repository's current theorem clause, without an `answer` wrapper. -/
theorem frozen_repository_clause :
    ∀ᶠ (n : ℕ) in Filter.atTop, ∀ C : Sym2 (Fin n) → Fin 2,
      {e : Sym2 (Fin n) | ¬e.IsDiag ∧
        ∀ x y : Fin n, e = s(x, y) →
          ¬∃ z, z ≠ x ∧ z ≠ y ∧ C s(x, z) = C e ∧ C s(y, z) = C e}.ncard ≤ n ^ 2 / 4 := by
  exact asymptotic_bound

#check Erdos639.SimpleGraph.erdos639
#print axioms Erdos639.SimpleGraph.erdos639
#print axioms frozen_repository_clause
#print axioms bound_ten

end Erdos639FC
