module

public import Erdos696External
public import proofs.erdos696.Bridge
public meta import Lean.Util.CollectAxioms

@[expose] public section

/-!
# Exact repository consequence of the external Erdős 696 theorem

The external mathematical proof is attributed to David Turturean, Jayyhk, plby,
and the BoundedGaps development. Its source is fetched at a pinned revision by
`prepare.py`; only import and visibility directives are changed.
-/

/-- The exact repository divergence claim is false, using the proved ratio limit. -/
theorem Erdos696Bridge.complete_repository_target : Erdos696Bridge.RepositoryTarget := by
  apply Erdos696Bridge.repositoryTarget_of_external
  intro ε hε
  exact (Erdos696.erdos_696 ε hε).2.2

#print Erdos696Bridge.complete_repository_target
#print axioms Erdos696.erdos_696
#print axioms Erdos696Bridge.complete_repository_target

run_cmd do
  for target in #[`Erdos696.erdos_696, `Erdos696Bridge.complete_repository_target] do
    let axioms ← Lean.collectAxioms target
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Unproved axiom {axiomName} in {target}"
    logInfo m!"AXIOM AUDIT PASSED: {target}: {axioms}"
