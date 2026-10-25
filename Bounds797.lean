/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Erdos797
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter Real
open scoped Topology

namespace Erdos797Bounds

private lemma third_power (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (1/3 : ℝ)) ^ 3 = x := by
  rw [← Real.rpow_mul_natCast hx]
  norm_num

private lemma four_thirds_power (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (4/3 : ℝ)) ^ 3 = x ^ 4 := by
  rw [← Real.rpow_mul_natCast hx]
  norm_num

noncomputable def lowerConstant : ℝ :=
  (Real.log 2 / (2 : ℝ)^67) ^ (1/3 : ℝ)

lemma lowerConstant_pos : 0 < lowerConstant := by
  apply Real.rpow_pos_of_pos
  exact div_pos (Real.log_pos (by norm_num)) (by positivity)

lemma lowerConstant_cube : lowerConstant^3 = Real.log 2 / (2 : ℝ)^67 := by
  exact third_power _ (by positivity)

/-- Real-power form of the verified cubic upper estimate. -/
theorem upper_bound {d : ℕ} (hd : 1 ≤ d) :
    (Erdos797.extremalAcyclicNumber d : ℝ) ≤ 1024*(d : ℝ)^(4/3 : ℝ) := by
  have hc : (Erdos797.extremalAcyclicNumber d : ℝ)^3 ≤
      (1024 : ℝ)^3*(d : ℝ)^4 := by
    exact_mod_cast Erdos797.UpperBound.extremalAcyclicNumber_cube_le hd
  apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by positivity)
  calc
    (Erdos797.extremalAcyclicNumber d : ℝ)^3 ≤
        (1024 : ℝ)^3*(d : ℝ)^4 := hc
    _ = (1024*(d : ℝ)^(4/3 : ℝ))^3 := by
      rw [mul_pow, four_thirds_power _ (by positivity)]

/-- Real-logarithm form of the verified discrete logarithmic lower estimate. -/
theorem lower_bound {d : ℕ}
    (hd : max (Erdos797.LowerBound.lowerD 1) 2 ≤ d) :
    lowerConstant*(d : ℝ)^(4/3 : ℝ)/(Real.log d)^(1/3 : ℝ) ≤
      (Erdos797.extremalAcyclicNumber d : ℝ) := by
  have hdlarge : Erdos797.LowerBound.lowerD 1 ≤ d := (le_max_left _ _).trans hd
  have hdtwo : 2 ≤ d := (le_max_right _ _).trans hd
  have hlog : 0 < Real.log (d : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1<d))
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : (0 : ℝ) < (2 : ℝ)^67 := by positivity
  have hc : (d : ℝ)^4 ≤ (2 : ℝ)^67*(Nat.log 2 d : ℝ)*
      (Erdos797.extremalAcyclicNumber d : ℝ)^3 := by
    exact_mod_cast Erdos797.LowerBound.fourth_le_log_mul_extremal_cube hdlarge
  have hnlog : (Nat.log 2 d : ℝ) ≤ Real.log d / Real.log 2 := by
    simpa [Real.logb] using Real.natLog_le_logb d 2
  have hc' : (d : ℝ)^4 ≤
      ((2 : ℝ)^67*Real.log d*(Erdos797.extremalAcyclicNumber d : ℝ)^3)/Real.log 2 := by
    calc
      (d : ℝ)^4 ≤ (2 : ℝ)^67*(Nat.log 2 d : ℝ)*
          (Erdos797.extremalAcyclicNumber d : ℝ)^3 := hc
      _ ≤ (2 : ℝ)^67*(Real.log d/Real.log 2)*
          (Erdos797.extremalAcyclicNumber d : ℝ)^3 := by gcongr
      _ = _ := by ring
  have hm : (d : ℝ)^4*Real.log 2 ≤
      (2 : ℝ)^67*Real.log d*(Erdos797.extremalAcyclicNumber d : ℝ)^3 :=
    (le_div_iff₀ hlogTwo).mp hc'
  apply le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (by positivity)
  rw [div_pow, mul_pow, lowerConstant_cube,
    four_thirds_power _ (by positivity), third_power _ hlog.le]
  apply (div_le_iff₀ hlog).mpr
  calc
    (Real.log 2/(2 : ℝ)^67)*(d : ℝ)^4 = ((d : ℝ)^4*Real.log 2)/(2 : ℝ)^67 := by ring
    _ ≤ ((2 : ℝ)^67*Real.log d*(Erdos797.extremalAcyclicNumber d : ℝ)^3)/(2 : ℝ)^67 :=
      div_le_div_of_nonneg_right hm hK.le
    _ = (Erdos797.extremalAcyclicNumber d : ℝ)^3*Real.log d := by
      field_simp

/-- The real-power, real-logarithm pair of bounds appearing in problem 797. -/
theorem bounds :
    ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∀ᶠ d : ℕ in atTop,
      c*(d : ℝ)^(4/3 : ℝ)/(Real.log d)^(1/3 : ℝ) ≤
          (Erdos797.extremalAcyclicNumber d : ℝ) ∧
      (Erdos797.extremalAcyclicNumber d : ℝ) ≤ C*(d : ℝ)^(4/3 : ℝ) := by
  refine ⟨lowerConstant,1024,lowerConstant_pos,by norm_num,?_⟩
  filter_upwards [eventually_ge_atTop (max (Erdos797.LowerBound.lowerD 1) 2)] with d hd
  exact ⟨lower_bound hd,upper_bound (by have := (le_max_right _ _).trans hd; omega)⟩

#print axioms upper_bound
#print axioms lower_bound
#print axioms bounds
end Erdos797Bounds

