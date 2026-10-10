# N268 / N176: blocker resolved

N268 and N176 are complete. The original remaining forest-complement hypothesis is now a proved theorem, and both unconditional endpoints are exported by `Matroid.Matroid`.

## Final checked endpoints

```lean
Graph.PlaneEmbedding.hasCycleBondFaceDual
  (P : G.PlaneEmbedding)
  (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite) :
  P.HasCycleBondFaceDual

Graph.IsPlanar.matroid_correspondence
  (hP : G.IsPlanar)
  (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite) :
  ∃ (γ : Type) (H : Graph γ β) (hH : H.edgeSet.Finite),
    Matroid.graphic G hE = Matroid.cographic H hH ∧
    Matroid.cographic G hE = Matroid.graphic H hH
```

These declarations are proved in `Internal/ForestComplement.lean`. N268 constructs the incidence dual on the actual complementary faces of `P`, retaining each original edge label. Both minimal-cycle/bond correspondences are part of `HasCycleBondFaceDual`. N176 is the short application of the existing graphic/cographic correspondence API.

## How the last geometric hypothesis was discharged

The retained reduction `hasCycleBondFaceDual_of_forest_edge_complement` needed:

```lean
∀ D : Set β, D ⊆ G.edgeSet → G.IsForestIn D →
  IsPreconnected (P.edgeSupport D)ᶜ
```

`forest_edge_complement_preconnected` now proves this (even without the redundant subset hypothesis, since `edgeSupport` already restricts to actual edges).

1. `forest_exists_vertex_potential` integrates edge increments using the checked isolating-cut characterization of forest independence.
2. Imported covering-space path lifts exist on every selected edge interval. `forest_exists_compatible_lifts` corrects their integer endpoint discrepancies with the vertex potentials.
3. `forest_circle_lift` descends the compatible lifts to the actual support. Its finite edge-interval quotient keeps labels distinct in interiors and identifies only common drawn endpoints. Branches, disconnected components, and empty supports are allowed.
4. `forest_sphere_extension` uses imported Tietze extension on the real-valued lift, then maps back to the geometric circle.
5. A bounded complementary component has frontier in the forest support. Extending radial projection from the support and pasting it with radial projection outside that component would retract an enclosing disk onto its boundary. The pinned, proved `JordanCurve.Brouwer.no_retraction` rules this out.
6. The imported connected disk exterior identifies all unbounded complementary components. Thus the forest complement is preconnected.
7. The existing retained-boundary separation theorem excludes nonempty forest boundaries. Existing finite graph circuit extraction and matroid duality then close N268, and N176 follows immediately.

The original cycle-to-Jordan trace, whole-boundary separation, relative Schoenflies standardization, complete edge incidence, and cycle-to-bond lemmas are retained. No generic Jordan separation, endpoint-collar, crosscut, face-counting, or arc-density theory was added in this completion pass.

## External-source compatibility and provenance

The dependency pins are unchanged: `jordan_pick` at `b3c9b7cf7358bf81a077d78ad67e6e8247869ddd`, the adapted Schoenflies closure at `05a43d29cde026618777db3d4e4316204ccca237`, and Lean/mathlib 4.35.0-rc3. Exact licenses, source links, imported declarations, and local bridge names are recorded in [SOURCES.md](SOURCES.md).

The formerly audited `general_crosscut_three_regions` requires polygonality and collars; `face_cycles'` requires a finite two-connected polygonal loopless drawing. The polygonal redrawing and PL approximation theorems do not transport the original complement. Those mismatches remain accurate descriptions of those APIs, but they no longer block this proof: the forest-lift/no-retraction bridge uses the original continuous drawing throughout.

The manuscript invokes planar graphic/cographic correspondence in `prop:r10-proper-minors`. The nearby Oxley citation is attached to the R10 minor identities, not the planar-duality sentence. N268/N176 remain `EXTERNAL_UNCITED_STANDARD`; the imported topology and local bridges are not described as manuscript proofs. The specific downstream R10 certificate fallback was unnecessary and was not substituted for the general theorem.

## Validation and stopping point

Full `lake build` passes after the forest lift (9124 jobs), N268 (9125 jobs), and N176 (9125 jobs). The 12-declaration axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`, including both unconditional endpoints.

N268 and N176 are `COMPLETE`. The unchanged dependency DAG has 197 active nodes, 55 complete. All active nodes at depths 0–4 are complete. The next unresolved depth is 5, listed in [FRONTIER.md](FRONTIER.md); no depth-5 proof was begun.

The active Matroid formalization is complete through topological depth 4.
