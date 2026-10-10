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
    logInfo "ALLOWLIST PASS: {name}: {axioms}"

#print axioms Erdos129.two_pow_lt_R
#print axioms Erdos129.not_eventually_R_lt
#print axioms Erdos129.erdos_129
