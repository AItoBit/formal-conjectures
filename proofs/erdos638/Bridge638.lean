/- Exact statement bridge for Erdős 638.
The original construction is by Brian Saturnino / InfiniteInsights; the completed
formal development is supplied by Star Fleet Math. See README.md for provenance.
-/
import Research.Hereditary
import Mathlib.Combinatorics.SimpleGraph.Copy

open scoped SimpleGraph

namespace Erdos638FC

universe u

/-- Membership in a finite graph family is independent of the vertex labelling. -/
def IsoClosed (S : (n : ℕ) → Set (SimpleGraph (Fin n))) : Prop :=
  ∀ m n (H : SimpleGraph (Fin m)) (K : SimpleGraph (Fin n)),
    Nonempty (H ≃g K) → H ∈ S m → K ∈ S n

/-- The family contains every ordinary finite subgraph of each member. -/
def SubgraphClosed (S : (n : ℕ) → Set (SimpleGraph (Fin n))) : Prop :=
  ∀ m n (H : SimpleGraph (Fin m)) (K : SimpleGraph (Fin n)),
    H.IsContained K → K ∈ S n → H ∈ S m

/-- Every ordinary finite subgraph of the host belongs to the family, up to relabelling. -/
def FiniteSubgraphsIn (S : (n : ℕ) → Set (SimpleGraph (Fin n)))
    {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ n (H : SimpleGraph (Fin n)), H.IsContained G → H ∈ S n

/-- Every edge colouring with colours in `C` contains a monochromatic triangle. -/
def ArrowsTriangle {V : Type*} (G : SimpleGraph V) (C : Type*) : Prop :=
  ∀ c : G.EdgeLabeling C,
    ∃ (x y z : V) (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz : G.Adj x z),
      c.get x y hxy = c.get y z hyz ∧ c.get y z hyz = c.get x z hxz

/-- The family has a triangle-Ramsey member for each positive finite number of colours. -/
def FiniteRamseyRich (S : (n : ℕ) → Set (SimpleGraph (Fin n))) : Prop :=
  ∀ r : ℕ, ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ S n ∧ ArrowsTriangle G (Fin (r + 1))

abbrev Family := (n : ℕ) → Set (SimpleGraph (Fin n))

def Claim : Prop :=
  ∀ S : Family, SubgraphClosed S → FiniteRamseyRich S →
    ∀ C : Type u, Infinite C → ∃ V : Type (u + 1), ∃ G : SimpleGraph V,
      FiniteSubgraphsIn S G ∧ ArrowsTriangle G C

def LiteralClaim : Prop :=
  ∀ S : Family, IsoClosed S → FiniteRamseyRich S →
    ∀ C : Type u, Infinite C → ∃ V : Type (u + 1), ∃ G : SimpleGraph V,
      FiniteSubgraphsIn S G ∧ ArrowsTriangle G C
/-- This is a direct identity after unfolding both monochromatic-triangle predicates. -/
theorem arrowsTriangle_iff_external {V C : Type*} (G : SimpleGraph V) :
    ArrowsTriangle G C ↔ Erdos638.RamseyForTriangle G C := Iff.rfl

/-- Mathlib ordinary containment and the external injective-homomorphism definition agree. -/
theorem ordinarySubgraph_iff_isContained {V : Type*}
    (H : Erdos638.FiniteGraph) (G : SimpleGraph V) :
    H.IsOrdinarySubgraphOf G ↔ H.graph ⊑ G := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f.toCopy hf⟩
  · rintro ⟨f⟩
    exact ⟨f.toHom, f.injective⟩

/-- Re-index the bundled external family by graph order. -/
def ofExternal (S : Erdos638.GraphFamily) : Family :=
  fun n G => (⟨n, G⟩ : Erdos638.FiniteGraph) ∈ S

theorem ofExternal_subgraphClosed (S : Erdos638.GraphFamily)
    (hS : S.OrdinaryHereditary) : SubgraphClosed (ofExternal S) := by
  intro m n H K hHK hK
  exact hS ((ordinarySubgraph_iff_isContained ⟨m, H⟩ K).mpr hHK) hK

theorem ofExternal_finiteRamseyRich (S : Erdos638.GraphFamily)
    (hS : S.FinitelyTriangleRamseyRich) : FiniteRamseyRich (ofExternal S) := by
  intro r
  obtain ⟨H, hH, hRamsey⟩ := hS r
  exact ⟨H.order, H.graph, hH, hRamsey⟩

theorem containsAllFiniteOrdinarySubgraphs_of_external {V : Type*}
    (S : Erdos638.GraphFamily) (G : SimpleGraph V)
    (h : FiniteSubgraphsIn (ofExternal S) G) :
    S.ContainsAllFiniteOrdinarySubgraphs G := by
  intro H hHG
  exact h H.order H.graph ((ordinarySubgraph_iff_isContained H G).mp hHG)

/-- Full ordinary-hereditary negative answer, transported without changing its quantifiers. -/
theorem erdos_638_ordinaryHereditary : ¬ Claim.{u} := by
  intro hclaim
  apply Erdos638.erdos638_ordinaryHereditary_answer_is_no.{u}
  intro S hclosed hrich C hC
  obtain ⟨V, G, hAge, hRamsey⟩ := hclaim (ofExternal S)
    (ofExternal_subgraphClosed S hclosed) (ofExternal_finiteRamseyRich S hrich) C hC
  exact ⟨V, G, containsAllFiniteOrdinarySubgraphs_of_external S G hAge, hRamsey⟩

/-- Ordinary-subgraph closure includes isomorphism closure via the inverse isomorphism. -/
theorem subgraphClosed_isoClosed (S : Family) (hS : SubgraphClosed S) : IsoClosed S := by
  intro m n H K hIso hH
  obtain ⟨e⟩ := hIso
  exact hS n m K H ⟨e.symm.toCopy⟩ hH
/-- The literal statement follows as a logical consequence of the stronger hereditary disproof. -/
theorem erdos_638_literal : ¬ LiteralClaim.{u} := by
  intro hclaim
  apply erdos_638_ordinaryHereditary.{u}
  intro S hclosed hrich
  exact hclaim S (subgraphClosed_isoClosed S hclosed) hrich

#print axioms Erdos638.erdos638_ordinaryHereditary_answer_is_no
#check Erdos638.erdos638_ordinaryHereditary_answer_is_no
#check erdos_638_ordinaryHereditary
#print axioms erdos_638_ordinaryHereditary
#print axioms erdos_638_literal


/-- Target copied mechanically from the repository theorem. -/
theorem frozen_literal :
    ¬ ∀ S : (n : ℕ) → Set (SimpleGraph (Fin n)), IsoClosed S → FiniteRamseyRich S →
      ∀ C : Type u, Infinite C → ∃ (V : Type (u + 1)) (G : SimpleGraph V),
        FiniteSubgraphsIn S G ∧ ArrowsTriangle G C := by
  exact erdos_638_literal.{u}

/-- Target copied mechanically from the repository variant. -/
theorem frozen_subgraph_closed :
    ¬ ∀ S : (n : ℕ) → Set (SimpleGraph (Fin n)), SubgraphClosed S → FiniteRamseyRich S →
      ∀ C : Type u, Infinite C → ∃ (V : Type (u + 1)) (G : SimpleGraph V),
        FiniteSubgraphsIn S G ∧ ArrowsTriangle G C := by
  exact erdos_638_ordinaryHereditary.{u}

#print axioms frozen_literal
#print axioms frozen_subgraph_closed

end Erdos638FC
