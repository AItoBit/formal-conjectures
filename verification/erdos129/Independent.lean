import Lean4Lean.Replay

unsafe def main : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  for name in #[`Erdos129.two_pow_lt_R, `Erdos129.not_eventually_R_lt, `Erdos129.erdos_129] do
    IO.println s!"Independent kernel replay: {name}"
    let count ← Lean4Lean.Replay.replayFromFresh `Erdos129 (decl := some name)
    if count == 0 then
      throw <| IO.userError s!"Target was not replayed: {name}"
    IO.println s!"PASS: {name}; {count} declarations checked from a fresh environment"
  return 0
