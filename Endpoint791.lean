import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Find
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Erdos791

/-- A finite additive 2-basis for the interval from zero through n.
The two summands may be equal. -/
def IsBasis (n : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 0 n ∧
    ∀ m ≤ n, ∃ a ∈ A, ∃ b ∈ A, a + b = m

theorem exists_basis_card (n : ℕ) :
    ∃ k : ℕ, ∃ A : Finset ℕ, IsBasis n A ∧ A.card = k := by
  refine ⟨(Finset.Icc 0 n).card, Finset.Icc 0 n, ⟨fun _ h => h, ?_⟩, rfl⟩
  intro m hm
  exact ⟨m, by simp [hm], 0, by simp, by omega⟩

/-- Minimum cardinality of a basis, counting the necessary zero element. -/
noncomputable def g (n : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_basis_card n)

theorem g_spec (n : ℕ) : ∃ A : Finset ℕ, IsBasis n A ∧ A.card = g n := by
  classical
  exact Nat.find_spec (exists_basis_card n)

theorem g_le_of_basis {n : ℕ} {A : Finset ℕ} (hA : IsBasis n A) :
    g n ≤ A.card := by
  classical
  exact Nat.find_min' (exists_basis_card n) ⟨A, hA, rfl⟩

theorem g_zero : g 0 = 1 := by
  have hBasis : IsBasis 0 {0} := by
    constructor
    · simp
    · intro m hm
      have hm0 : m = 0 := by omega
      subst m
      exact ⟨0, by simp, 0, by simp, rfl⟩
  have hu : g 0 ≤ 1 := by simpa using g_le_of_basis hBasis
  obtain ⟨A, hA, hc⟩ := g_spec 0
  obtain ⟨a, ha, b, hb, _⟩ := hA.2 0 (by omega)
  have := Finset.card_pos.mpr ⟨a, ha⟩
  omega

/-- An elementary analytic consequence of the explicit seven-segment bound.
The construction hypothesis is discharged in the final development. -/
theorem not_tendsto_two_of_family
    (H : ∀ t : ℕ, 2 ≤ t → g (14 * t ^ 2 - 1) ≤ 7 * (t + 1)) :
    ¬ Filter.Tendsto (fun n : ℕ => (g n : ℝ) / Real.sqrt (n : ℝ))
      Filter.atTop (nhds 2) := by
  intro h
  have he : ∀ᶠ n : ℕ in Filter.atTop,
      (39 / 20 : ℝ) < (g n : ℝ) / Real.sqrt (n : ℝ) :=
    h.eventually (eventually_gt_nhds (by norm_num : (39 / 20 : ℝ) < 2))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp he
  let t := N + 100
  let n := 14 * t ^ 2 - 1
  have ht : 100 ≤ t := by omega
  have hb : 1 ≤ 14 * t ^ 2 := by nlinarith only [ht]
  have hcast : (n : ℝ) = 14 * (t : ℝ) ^ 2 - 1 := by
    dsimp [n]
    rw [Nat.cast_sub hb]
    push_cast
    ring
  have hn : N ≤ n := by
    have heq : n + 1 = 14 * t ^ 2 := Nat.sub_add_cancel hb
    have htN : N ≤ t := by dsimp [t]; omega
    have : t ≤ n := by nlinarith only [heq, ht]
    omega
  have htr : (100 : ℝ) ≤ t := by exact_mod_cast ht
  have hs : (37 / 10 : ℝ) * t ≤ Real.sqrt (n : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hcast, htr, sq_nonneg ((t : ℝ) - 100)]
  have hpos : 0 < Real.sqrt (n : ℝ) := by nlinarith only [hs, htr]
  have hl := (lt_div_iff₀ hpos).mp (hN n hn)
  have hu : (g n : ℝ) ≤ 7 * ((t : ℝ) + 1) := by
    exact_mod_cast H t (by omega)
  have hm := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 39 / 20)
  nlinarith only [hm, hl, hu, htr]

end Erdos791

#print axioms Erdos791.g_le_of_basis
#print axioms Erdos791.g_zero
#print axioms Erdos791.not_tendsto_two_of_family
