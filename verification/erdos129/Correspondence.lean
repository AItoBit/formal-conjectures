import FormalConjectures.ErdosProblems.«129»
import External129

namespace Erdos129Receipt

theorem two_pow_lt_R (n : ℕ) (hn : 100 ≤ n) : 2 ^ (n / 100) < Erdos129.R n 3 2 := by
  exact ExternalErdos129.two_pow_lt_R n hn

theorem not_eventually_R_lt (C : ℝ) (hC : 0 ≤ C) :
    ¬ ∀ᶠ n : ℕ in Filter.atTop, (Erdos129.R n 3 2 : ℝ) < C ^ Real.sqrt n := by
  exact ExternalErdos129.not_eventually_R_lt C hC

theorem erdos_129 : answer(False) ↔
    ∀ r : ℕ, 2 ≤ r → ∃ C : ℝ, 1 < C ∧ ∀ n : ℕ,
      (Erdos129.R n 3 r : ℝ) < C ^ Real.sqrt n := by
  exact ExternalErdos129.erdos_129

#print axioms two_pow_lt_R
#print axioms not_eventually_R_lt
#print axioms erdos_129

end Erdos129Receipt
