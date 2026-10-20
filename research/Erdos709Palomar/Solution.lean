/-
Copyright 2026 The Formal Conjectures Authors.
Released under the Apache-2.0 license, as described in the file LICENSE.
-/
module

public import Mathlib

/-!
# Proof of the singleton case of Erdős Problem 709
-/

public section

namespace Erdos709

/-- The block of `length` consecutive positive integers immediately after `start`. -/
def window (start length : ℕ) : Finset ℕ := Finset.Icc (start + 1) (start + length)

/-- A block contains distinct multiples of every element of `A`. -/
def HasDistinctMultiples (A : Finset ℕ) (start length : ℕ) : Prop :=
  ∃ choice : ℕ → ℕ,
    Set.InjOn choice (A : Set ℕ) ∧
    ∀ a ∈ A, choice a ∈ window start length ∧ a ∣ choice a

/-- The multiplier works for every input of size `n` and every starting point. -/
def Works (n k : ℕ) : Prop :=
  ∀ (A : Finset ℕ) (M : ℕ),
    A.card = n → M ∈ A → (∀ a ∈ A, a ≤ M) → (∀ a ∈ A, 2 ≤ a) →
    ∀ start : ℕ, HasDistinctMultiples A start (k * M)

/-- For a singleton input, the multiplier `1` suffices. -/
theorem singleton_case : Works 1 1 := by
  intro A M hcard hM hbound htwo start
  have hA : A = {M} := by
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
    have hMz : M = z := Finset.mem_singleton.mp (hz ▸ hM)
    simpa [hMz] using hz
  obtain ⟨b, hb, hd⟩ := by
    let r := start % M
    let b := start + (M - r)
    have hr : r < M := Nat.mod_lt start (by have := htwo M hM; omega)
    have heq : start % M + M * (start / M) = start := by
      simpa [Nat.mul_comm] using Nat.mod_add_div start M
    have hbdiv : b = M * (start / M + 1) := by
      have haux : b = M * (start / M) + M := by
        dsimp [b, r]
        omega
      calc
        b = M * (start / M) + M := haux
        _ = M * (start / M + 1) := by ring
    refine ⟨b, ?_, ?_⟩
    · simp only [window, Finset.mem_Icc]
      constructor <;> dsimp [b] <;> omega
    · exact ⟨start / M + 1, hbdiv⟩
  refine ⟨fun _ => b, ?_, ?_⟩
  · intro u hu v hv _
    rw [hA] at hu hv
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hu hv
    exact hu.trans hv.symm
  · intro a ha
    rw [hA] at ha
    have hEq : a = M := Finset.mem_singleton.mp ha
    subst a
    simpa using And.intro hb hd

end Erdos709
