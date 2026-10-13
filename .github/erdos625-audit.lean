import Erdos625SelfContained

/- The following two definitions are copied from Formal Conjectures at
817d8a74 (Apache-2.0), Combinatorics/SimpleGraph/Coloring/Vertex.lean,
using set-builder notation for compatibility with Mathlib 4.31.
The external proof is by Samuil Petkov, CC BY 4.0, unchanged at
9702b5e734627e3fdaef8da0d65ad7394016f0a7. The adapter below is new. -/
namespace SimpleGraph
def Cocolorable {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ coloring : V → Fin n,
    ∀ i, G.induce {v | coloring v = i} = ⊥ ∨ G.induce {v | coloring v = i} = ⊤

noncomputable def cochromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ∞ :=
  ⨅ n ∈ {k | G.Cocolorable k}, (n : ℕ∞)
end SimpleGraph

namespace Audit625

variable {V : Type*} (G : SimpleGraph V)

/-- An independent vertex set induces the empty graph, including empty sets. -/
theorem induce_eq_bot_iff (s : Set V) :
    G.induce s = ⊥ ↔ G.IsIndepSet s := by
  rw [SimpleGraph.eq_bot_iff_forall_not_adj]
  constructor
  · intro h x hx y hy _
    exact h ⟨x, hx⟩ ⟨y, hy⟩
  · intro h x y hxy
    exact h x.property y.property (fun hval => hxy.ne (Subtype.ext hval)) hxy

/-- The external cocolorings and the repository cocolorings have the same
finite palettes. Empty color classes are allowed on both sides. -/
theorem coColorable_iff_cocolorable (k : ℕ) :
    Erdos625.CoColorable G k ↔ G.Cocolorable k := by
  classical
  constructor
  · rintro ⟨C⟩
    refine ⟨C.color, fun i => ?_⟩
    cases hi : C.kind i with
    | independent =>
      exact Or.inl ((induce_eq_bot_iff G _).mpr (C.valid_independent hi))
    | clique =>
      exact Or.inr (SimpleGraph.induce_eq_top.mpr (C.valid_clique hi))
  · rintro ⟨coloring, h⟩
    refine ⟨{
      color := coloring
      kind := fun i => if G.induce {v | coloring v = i} = ⊥
        then .independent else .clique
      valid := ?_
    }⟩
    intro i
    by_cases hi : G.induce {v | coloring v = i} = ⊥
    · simpa only [if_pos hi] using (induce_eq_bot_iff G _).mp hi
    · simpa only [if_neg hi] using SimpleGraph.induce_eq_top.mp ((h i).resolve_left hi)

/-- Both minimizations give the same extended natural number. -/
theorem cochromaticNumber_cast_eq [Fintype V] :
    (Erdos625.cochromaticNumber G : ℕ∞) = G.cochromaticNumber := by
  unfold SimpleGraph.cochromaticNumber
  apply le_antisymm
  · refine le_iInf fun n => le_iInf fun hn => ?_
    exact_mod_cast Erdos625.cochromaticNumber_le_of_coColorable G
      ((coColorable_iff_cocolorable G n).mpr hn)
  · exact iInf_le_of_le (Erdos625.cochromaticNumber G)
      (iInf_le_of_le ((coColorable_iff_cocolorable G _).mp
        (Erdos625.coColorable_cochromaticNumber G)) le_rfl)

/-- The natural-valued cochromatic numbers agree for every finite graph,
including the graph on the empty type. -/
theorem cochromaticNumber_eq [Fintype V] :
    Erdos625.cochromaticNumber G = G.cochromaticNumber.toNat := by
  simpa using congrArg ENat.toNat (cochromaticNumber_cast_eq G)

#print axioms coColorable_iff_cocolorable
#print axioms cochromaticNumber_cast_eq
#print axioms cochromaticNumber_eq

end Audit625
namespace Audit625
open Filter SimpleGraph
open scoped Topology

theorem quantitative :
    Tendsto
      (fun n : ℕ ↦ binomialRandom (Fin n) ⟨1 / 2, by norm_num⟩
        {G | ((Real.log 2) ^ 2 / 4 * Real.log (200 / 153 : ℝ)) *
            n / (Real.log n) ^ 3 ≤
          (G.chromaticNumber.toNat : ℝ) - G.cochromaticNumber.toNat})
      atTop (𝓝 1) := by
  have h : Tendsto
      (fun n => Erdos625.randomGraphMeasure n
        {G | Erdos625.gapScale n ≤
          (Erdos625.chromaticNumberNat G : ℝ) - Erdos625.cochromaticNumber G})
      atTop (𝓝 1) := Erdos625.erdos625
  simpa only [Erdos625.gapScale, Erdos625.gapConstant,
    Erdos625.randomGraphMeasure, Erdos625.halfProbability,
    Erdos625.chromaticNumberNat, cochromaticNumber_eq] using h

theorem positive_answer : True ↔
    ∀ K : ℝ, Tendsto
      (fun n : ℕ ↦ binomialRandom (Fin n) ⟨1 / 2, by norm_num⟩
        {G | K ≤ (G.chromaticNumber.toNat : ℝ) - G.cochromaticNumber.toNat})
      atTop (𝓝 1) := by
  constructor
  · intro _ K
    have h := Erdos625.fixedThreshold_tail_of_movingThreshold
      Erdos625.randomGraphMeasure
      (fun n G ↦ (Erdos625.chromaticNumberNat G : ℝ) - Erdos625.cochromaticNumber G)
      Erdos625.gapScale Erdos625.tendsto_explicit_gap_scale_atTop Erdos625.erdos625 K
    simpa only [Erdos625.randomGraphMeasure, Erdos625.halfProbability,
      Erdos625.chromaticNumberNat, cochromaticNumber_eq] using h
  · intro _
    trivial

#print axioms Erdos625.erdos625
#print axioms quantitative
#print axioms positive_answer
end Audit625
