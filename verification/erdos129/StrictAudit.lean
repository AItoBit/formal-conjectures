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

import Erdos129
import Lean.Util.CollectAxioms

open Lean Elab Command

run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[`Erdos129.two_pow_lt_R, `Erdos129.not_eventually_R_lt, `Erdos129.erdos_129] do
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "AXIOM REJECTED: {name}: {axiomName}"
    logInfo m!"ALLOWLIST PASS: {name}: {axioms}"

#print axioms Erdos129.two_pow_lt_R
#print axioms Erdos129.not_eventually_R_lt
#print axioms Erdos129.erdos_129
