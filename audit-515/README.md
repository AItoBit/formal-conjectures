# Isolated verification of Erdos problem 515

Verification passed on 2026-10-11:
https://github.com/AItoBit/formal-conjectures/actions/runs/38119462031.
The tested harness commit is `8c9f7ad378bcc3b0fee2ef392cb843ad9ab62fe7`.
`receipt/` preserves the generated proof, axiom log, source hashes, and provenance.
The complete logs are also available in the run's artifact:
https://github.com/AItoBit/formal-conjectures/actions/runs/38119462031/artifacts/11694831929.

The external theorem, integral equality, and proved FC declaration each report
exactly `[propext, Classical.choice, Quot.sound]`. The FC source SHA-256 is
`d5b0e890209a307703bc021e701984ad10278d49363c19ad1b2dd159a8ced789`.

Run `python3 audit-515/isolated.py` from a fresh checkout on Linux with elan installed.
The workflow runs this command and uploads its sources and logs as an artifact.

Inputs are fixed at these commits:

- FC PR #7072: `66f3fb70a35318c275d633dac2aea67c02c7c288`.
- External proof: `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`.
- Lean and Mathlib: the FC commit's `lean-toolchain` and `lake-manifest.json`.

The script rebuilds the unchanged 231-module external dependency closure in the
FC environment. It does not reuse the previous external theorem's build products.
Two compiler processes run concurrently, with each module waiting for its imports.

Both projects declare names in `Erdos515`. The isolated copy relocates the FC
namespace to `FC515`; all definitions and the theorem proposition are retained.
It removes the FC module-mode directives because Lean forbids a module from
importing the legacy external file. The original public declarations remain public.
The script checks that the theorem proposition text is unchanged. It replaces
the FC placeholder with `external_implies_fc`, without using the placeholder theorem.
The contribution file in PR #7072 remains unchanged.

`Bridge.lean` defines `toFC` by copying the external path's `vertex` and
`tendsToInfinity` fields. `lineIntegral_toFC` proves integral equality with `rfl`.
The bridge invokes the external theorem, converts its witness once, and uses
that witness for every positive exponent.

Guarded `#print axioms` commands require both the external theorem and the
proved FC declaration to depend on exactly `propext`, `Classical.choice`, and
`Quot.sound`. A further output check restricts the integral equality's axioms
to this same permitted set. Any `sorryAx`, custom mathematical axiom, or native
evaluation axiom fails the verification.

The artifact contains the original FC file, generated `VerifiedFC515.lean`,
source hashes, build logs, bridge axiom output, and provenance. A successful
run ends with `ISOLATED FC DECLARATION VERIFIED; ALL PERMITTED-AXIOM CHECKS PASSED`.
