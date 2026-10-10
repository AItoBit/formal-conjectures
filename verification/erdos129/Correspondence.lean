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

import FormalConjectures.ErdosProblems.«129»
import External129
import Lean.Util.CollectAxioms

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

run_cmd Lean.Elab.Command.liftTermElabM do
  for (fc, checked) in #[(`Erdos129.two_pow_lt_R, `Erdos129Receipt.two_pow_lt_R),
      (`Erdos129.not_eventually_R_lt, `Erdos129Receipt.not_eventually_R_lt),
      (`Erdos129.erdos_129, `Erdos129Receipt.erdos_129)] do
    unless ← Lean.Meta.isDefEq (← Lean.getConstInfo fc).type (← Lean.getConstInfo checked).type do
      throwError "FC TYPE MISMATCH: {fc}"
    let axioms ← Lean.collectAxioms checked
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "AXIOM REJECTED: {checked}: {axiomName}"
    Lean.logInfo m!"FC TYPE AND AXIOM MATCH: {fc}"

end Erdos129Receipt
