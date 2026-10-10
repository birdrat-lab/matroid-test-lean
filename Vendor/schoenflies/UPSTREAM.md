# Pinned Schoenflies source

Repository: https://github.com/alonamaloh/schoenflies-lean

Revision: `05a43d29cde026618777db3d4e4316204ccca237`

License: Apache-2.0; see `LICENSE`. Original copyright and author notices
are retained in each source file.

This directory contains the 128-module transitive import closure of
`Schoenflies.JordanSchoenflies`, rather than the upstream umbrella import.
`UPSTREAM_SHA256SUMS` records the hashes of the original source files at that
revision. `COMPATIBILITY.patch` records every change to those Lean sources.
The local Lake configuration uses the parent project's Lean/mathlib
4.35.0-rc3; upstream pins 4.32.2.

Compatibility changes:

- Make interval unfolding explicit in `Subarc.lean`.
- Replace the deprecated set restriction API in `InitialPair.lean` and
  `Endgame.lean`.
- Rename the external predicate `Graph.IsBridge` to
  `Graph.IsSchoenfliesBridge`, keeping its definition and proofs, because
  the project's newer mathlib already declares `Graph.IsBridge`.
- Import `Mathlib.Topology.MetricSpace.PiNat` in `QuantitativeRecursion.lean`
  so its generated `TopologicalSpace.denseSeq.congr_simp` declaration is
  shared with the project's mathlib imports.

The imported result is `Schoenflies.jordan_schoenflies_of_homeomorph`.
The local graph bridge also uses `Schoenflies.IsJordanCurve`,
`Schoenflies.IsJordanCurve.homeomorph_modelCurve`, and
`Schoenflies.isJordanCurve_modelCurve`.

All copied modules were compiled with the project's pinned Lean/mathlib.
The combined graph bridge's axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.
