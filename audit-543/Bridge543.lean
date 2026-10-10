import ErdosProblems.Erdos543
import Proposed543

open Filter Finset Real

namespace Bridge543

open Erdos543 in
lemma halfComplete_iff (G : Type) [AddCommGroup G] [Fintype G] {k : ℕ} (hk : k ≤ Fintype.card G) :
    1 / 2 ≤ Erdos543Proposed.completeProbability G k ↔ Model.HalfComplete G k := by
  classical
  have hfilter : ((univ : Finset G).powersetCard k).filter Erdos543Proposed.IsComplete =
      Model.goodSets (univ : Finset G) Model.SubsetSumComplete k := by
    unfold Model.goodSets
    exact Finset.filter_congr fun _ _ => Iff.rfl
  have hpos : (0 : ℝ) < ((univ : Finset G).powersetCard k).card := by
    rw [Finset.card_powersetCard, Finset.card_univ]
    exact_mod_cast Nat.choose_pos hk
  unfold Erdos543Proposed.completeProbability Model.HalfComplete Model.totalCount Model.completeCount
  rw [hfilter, le_div_iff₀ hpos]
  constructor
  · intro h
    have : (((univ : Finset G).powersetCard k).card : ℝ) ≤
        2 * (Model.goodSets (univ : Finset G) Model.SubsetSumComplete k).card := by
      linarith
    exact_mod_cast this
  · intro h
    have : (((univ : Finset G).powersetCard k).card : ℝ) ≤
        2 * (Model.goodSets (univ : Finset G) Model.SubsetSumComplete k).card := by
      exact_mod_cast h
    linarith

open Erdos543 in
lemma mem_iff {N k : ℕ} (hk : k ≤ N) :
    k ∈ {k | ∀ (G : Type) [AddCommGroup G] [Fintype G], Fintype.card G = N →
      1 / 2 ≤ Erdos543Proposed.completeProbability G k} ↔ Model.UniversallyHalfComplete N k := by
  simp only [Set.mem_ofPred_eq, Model.UniversallyHalfComplete]
  refine forall_congr' fun G => ?_
  refine forall_congr' fun _ => ?_
  refine forall_congr' fun _ => ?_
  refine forall_congr' fun hG => ?_
  exact halfComplete_iff G (hG ▸ hk)

open Erdos543 in
lemma f_eq (N : ℕ) : Erdos543Proposed.f N = Model.universalF N := by
  set S := {k | ∀ (G : Type) [AddCommGroup G] [Fintype G], Fintype.card G = N →
      1 / 2 ≤ Erdos543Proposed.completeProbability G k} with hS
  have hN : N ∈ S := (mem_iff le_rfl).2 (Model.universallyHalfComplete_card N)
  have h1 : sInf S ≤ N := Nat.sInf_le hN
  have h2 : Model.universalF N ≤ N := Model.universalF_le_card N
  have hmem1 : sInf S ∈ S := Nat.sInf_mem ⟨N, hN⟩
  have hmem2 : Model.UniversallyHalfComplete N (Model.universalF N) := Model.universalF_spec N
  apply le_antisymm
  · exact Nat.sInf_le ((mem_iff h2).2 hmem2)
  · exact Model.universalF_min ((mem_iff h1).1 hmem1)

theorem erdos_543_bridge : type_of% Erdos543Proposed.erdos_543 := by
  show False ↔ _
  simp only [false_iff]
  rintro ⟨o, ho, hf⟩
  apply Erdos543.not_erdos_543
  refine ⟨o, ho.tendsto_div_nhds_zero, ?_⟩
  filter_upwards [hf] with N hN
  rw [← f_eq]
  exact hN

#print axioms Erdos543.not_erdos_543
#print axioms erdos_543_bridge

end Bridge543
