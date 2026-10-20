/-
Copyright 2026 The Formal Conjectures Authors.
Released under the Apache-2.0 license, as described in the file LICENSE.
-/
module

public import Mathlib

/-!
# Singleton case of Erdős Problem 709

This is a proved boundary case of the open problem at
https://www.erdosproblems.com/709. It does not assert an asymptotic bound.
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
  sorry

end Erdos709
