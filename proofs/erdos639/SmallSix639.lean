/- Explicit exceptional-order witness, checked using kernel reduction. -/
import Mathlib.Data.Sym.Card
import Mathlib.Data.Set.Card

open scoped Sym2

namespace Erdos639Six

def uncoveredEdges {n : ℕ} (C : Sym2 (Fin n) → Fin 2) : Set (Sym2 (Fin n)) :=
  {e | ¬e.IsDiag ∧ ∀ x y : Fin n, e = s(x, y) →
    ¬∃ z, z ≠ x ∧ z ≠ y ∧ C s(x, z) = C e ∧ C s(y, z) = C e}

def sixColoring (e : Sym2 (Fin 6)) : Fin 2 :=
  if e ∈ ({s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 0),
      s(5, 1), s(5, 4), s(0, 5)} : Finset (Sym2 (Fin 6))) then 0 else 1

def sixUncovered : Finset (Sym2 (Fin 6)) :=
  {s(0, 2), s(0, 3), s(1, 2), s(1, 3), s(1, 4),
    s(2, 3), s(2, 4), s(2, 5), s(3, 4), s(3, 5)}

theorem sixColoring_uncovered_count : (uncoveredEdges sixColoring).ncard = 10 := by
  have h : uncoveredEdges sixColoring = (sixUncovered : Set (Sym2 (Fin 6))) := by
    unfold uncoveredEdges
    apply Set.ext
    simp only [Set.mem_ofPred_eq]
    decide
  rw [h, Set.ncard_coe_finset]
  decide

theorem six_counterexample :
    ∃ C : Sym2 (Fin 6) → Fin 2, (uncoveredEdges C).ncard = 10 ∧
      6 ^ 2 / 4 < (uncoveredEdges C).ncard := by
  refine ⟨sixColoring, sixColoring_uncovered_count, ?_⟩
  rw [sixColoring_uncovered_count]
  decide

#print axioms sixColoring_uncovered_count
#print axioms six_counterexample

end Erdos639Six
