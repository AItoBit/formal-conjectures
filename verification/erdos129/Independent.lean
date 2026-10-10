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
