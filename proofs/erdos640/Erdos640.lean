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
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Erdős Problem 640: the case k = 3

Source: [erdosproblems.com/640](https://www.erdosproblems.com/640).

The main question remains open. This file proves the stated k = 3 case. The graph induced
by the cycle vertices retains all ambient chords.

The proof uses Mathlib's `two_colorable_iff_forall_loop_even` and
`Walk.three_le_chromaticNumber_of_odd_loop`. The odd-cycle extraction is proved below.
-/

@[expose] public section

open SimpleGraph
namespace Erdos640

def HasHighChromaticOddCycle {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ v, ∃ p : G.Walk v v, p.IsCycle ∧ Odd p.length ∧
    (k : ℕ∞) ≤ (G.induce {x | x ∈ p.support}).chromaticNumber

theorem exists_odd_cycle_of_odd_loop {V : Type*} {G : SimpleGraph V}
    {v : V} (p : G.Walk v v) (hp : Odd p.length) :
    ∃ w, ∃ q : G.Walk w w, q.IsCycle ∧ Odd q.length := by
  classical
  induction hn : p.length using Nat.strongRecOn generalizing v with
  | ind n ih =>
    cases p with
    | nil => simp at hp
    | @cons v u v h q =>
      by_cases hq : q.IsPath
      · refine ⟨v, q.cons h, ?_, hp⟩
        apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
        refine ⟨by simpa using hq, ?_⟩
        have hne : (q.cons h).length ≠ 1 := by
          intro he
          have hzero : q.length = 0 := by simpa using he
          have huv := Walk.eq_of_length_eq_zero hzero
          exact h.ne huv.symm
        have hodd := hp
        rw [Nat.odd_iff] at hodd
        omega
      · rw [Walk.isPath_iff_isSubwalk_imp_nil] at hq
        push Not at hq
        obtain ⟨w, r, hr, hrnil⟩ := hq
        obtain ⟨a, b, heq⟩ := hr
        have hlen := congrArg Walk.length heq
        simp only [Walk.length_append] at hlen
        have hrpos : 0 < r.length := by
          exact Nat.pos_of_ne_zero (fun hz => hrnil (Walk.length_eq_zero_iff.mp hz))
        by_cases hro : Odd r.length
        · exact ih r.length (by simp only [Walk.length_cons] at hn; omega) r hro rfl
        · let s := (a.append b).cons h
          have hslen : s.length = a.length + b.length + 1 := by simp [s]
          have hso : Odd s.length := by
            rw [Nat.odd_iff] at hp ⊢
            rw [Nat.odd_iff] at hro
            simp only [Walk.length_cons] at hp
            omega
          exact ih s.length (by simp only [Walk.length_cons] at hn; omega) s hso rfl

theorem length_induce {V : Type*} {G : SimpleGraph V} {s : Set V}
    {u v : V} (p : G.Walk u v) (hp : ∀ x ∈ p.support, x ∈ s) :
    (p.induce s hp).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [Walk.induce_cons, Walk.length_cons, ih]

theorem three_le_chromaticNumber_induce_support {V : Type*} {G : SimpleGraph V}
    {v : V} (p : G.Walk v v) (hp : Odd p.length) :
    (3 : ℕ∞) ≤ (G.induce {x | x ∈ p.support}).chromaticNumber := by
  let q := p.induce {x | x ∈ p.support} (fun _ hx => hx)
  have hlen : q.length = p.length := length_induce p _
  exact q.three_le_chromaticNumber_of_odd_loop (hlen ▸ hp)

theorem hasHighChromaticOddCycle_three {V : Type*} (G : SimpleGraph V)
    (hG : (3 : ℕ∞) ≤ G.chromaticNumber) : HasHighChromaticOddCycle G 3 := by
  have hn : ¬G.Colorable 2 := by
    intro hc
    have hbad := hG.trans hc.chromaticNumber_le
    norm_cast at hbad
  obtain ⟨v, p, hp⟩ : ∃ v, ∃ p : G.Walk v v, Odd p.length := by
    by_contra h
    apply hn
    rw [two_colorable_iff_forall_loop_even]
    intro v p
    apply Nat.not_odd_iff_even.mp
    intro hp
    exact h ⟨v, p, hp⟩
  obtain ⟨v, p, hc, ho⟩ := exists_odd_cycle_of_odd_loop p hp
  exact ⟨v, p, hc, ho, three_le_chromaticNumber_induce_support p ho⟩

/-- The finite k = 3 case of Erdős Problem 640, with threshold three. -/
theorem erdos_640.variants.three (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : (3 : ℕ∞) ≤ G.chromaticNumber) : HasHighChromaticOddCycle G 3 := by
  exact hasHighChromaticOddCycle_three G hG

#print axioms erdos_640.variants.three
#print axioms exists_odd_cycle_of_odd_loop
#print axioms three_le_chromaticNumber_induce_support
#print axioms hasHighChromaticOddCycle_three
end Erdos640

