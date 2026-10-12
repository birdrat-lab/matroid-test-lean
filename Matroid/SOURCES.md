# External formal sources

N268 and N176 are complete. The final local forest bridge and its additional uses of the existing pinned dependency are recorded below; the source audits at the end explain why polygonal replacement was not used.

## Jordan curve and arc topology

- Repository: <https://github.com/rkirov/jordan_pick>
- Pinned Git revision: `b3c9b7cf7358bf81a077d78ad67e6e8247869ddd`
- License: Apache-2.0 (`LICENSE` at the pinned revision)
- Project import: `JordanPick.JordanCurve`, through `Matroid/Internal/JordanPath.lean` and `Matroid/PlanarDuality.lean`.
- Imported proved declarations currently used: `JordanCurve.jordan_curve`, `JordanCurve.component_boundary_eq`, `JordanCurve.arc_not_separates`, `JordanCurve.Brouwer.brouwerFPT`, `JordanCurve.Arcs.circleHomeoSphere`, `JordanCurve.Arcs.exists_proper_arc`, `JordanCurve.jordanCurveHomeo`, `JordanCurve.Brouwer.cover`, `JordanCurve.Brouwer.acToSphere`, `JordanCurve.Brouwer.no_retraction`, and `JordanCurve.isConnected_compl_closedBall`.
- Compatibility: the upstream project pins Lean 4.33.0, while this project pins Lean 4.35.0-rc3. The imported module and this project's full `lake build` were checked at the latter version, with the exact Git revision above. No upstream source was copied into `Matroid/`.
- Trust check: `#print axioms` for the imported theorems and `jordanCurveHomeo` reports only `propext`, `Classical.choice`, and `Quot.sound`.

The local bridge `JordanPath.exists_jordanTrace` converts an injective closed `Path` to the sphere parameterization used by the imported theorems. `Graph.jordanCurve_complement_card`, `Graph.jordanCurve_component_boundary`, and the edge lemmas in `PlanarDuality.lean` transport those theorems to the product plane used by `Graph.PlaneEmbedding`. None of these imported declarations states planar graph duality.

`Matroid/Internal/CycleWalkTrace.lean` proves that every labeled `Graph.IsGraphCycle` has a continuous closed path with exactly its drawn edge support and completes the loop case. `Matroid/Internal/SimpleCycleTrace.lean` extracts a vertex-simple walk while retaining actual edge labels, proves its drawn path injective, and closes it with the omitted edge. Thus `PlaneEmbedding.graphCycle_hasJordanTrace` now supplies an exact-support Jordan trace for every graph cycle. The subsequent full-drawing incidence and forest bridges now close N268; the graph-cycle trace is reused unchanged.

## Mathematical baseline for N268 / N176

- Oxley, *Matroid Theory* (2nd ed.), Proposition 5.2.1 and Lemma 2.3.7: <https://www.math.ens.psl.eu/~benoist/refs/Oxley.pdf>. The proposition derives graphic/cographic correspondence from an already constructed geometric dual; the connected-case lemma invokes Jordan separation. This is mathematical provenance, not a Lean import.
- The frozen manuscript uses planar graphic/cographic correspondence in the proof of `prop:r10-proper-minors` (lines 4401–4406 of `Manuscript/main.tex`). Its nearby Oxley citation is attached to the two `R₁₀` single-element minor identities; the planar-duality sentence has no explicit citation of its own.

## Relative Schoenflies infrastructure actually imported

- Repository: <https://github.com/alonamaloh/schoenflies-lean>
- Exact upstream revision: `05a43d29cde026618777db3d4e4316204ccca237`
- License: Apache-2.0; the upstream `LICENSE` and per-file author notices are retained.
- Dependency: local Lake package `Vendor/schoenflies`, containing the 128-module transitive import closure of `Schoenflies.JordanSchoenflies` at that revision. The original hashes, compatibility patch, and package configuration are recorded in [UPSTREAM.md](../Vendor/schoenflies/UPSTREAM.md), [UPSTREAM_SHA256SUMS](../Vendor/schoenflies/UPSTREAM_SHA256SUMS), and [COMPATIBILITY.patch](../Vendor/schoenflies/COMPATIBILITY.patch).
- Compatibility: upstream pins Lean 4.32.2. The vendored closure compiles with this project's Lean/mathlib 4.35.0-rc3 after the five documented source-file adaptations. Reversing the patch reproduces all 128 recorded original hashes. This is a pinned, locally adapted source dependency, not an assertion that the unmodified upstream package builds here.
- Imported declarations actually used by the graph bridge: `Schoenflies.IsJordanCurve`, `Schoenflies.IsJordanCurve.homeomorph_modelCurve`, `Schoenflies.isJordanCurve_modelCurve`, `Schoenflies.modelCurve`, and the proved `Schoenflies.jordan_schoenflies_of_homeomorph`. The local square calculations also use `Schoenflies.Plane.mk`, `sub_apply`, `smul_add_apply`, `abs_zero_le_supNorm`, `abs_one_le_supNorm`, `supNorm_le_norm`, `convex_coord_lt`, and `convex_coord_gt`.
- Trust check: `#print axioms` for the imported relative Schoenflies theorem, the general Jordan-trace bridge, ambient-standardization bridges, incidence transport, dual-certificate transport, local support isolation, and the new complete cycle-edge incidence and face-boundary bridges reports only `propext`, `Classical.choice`, and `Quot.sound`.

`Matroid/Internal/SchoenfliesCycle.lean` proves `PlaneEmbedding.graphCycle_isJordanCurve`, `graphCycle_hasAmbientModelCurve`, and `graphCycle_hasAmbientModelEmbedding`. The last moves the entire original labeled drawing while standardizing the selected cycle. `graphCycle_hasAmbientModelCurve_at` additionally sends any specified cycle point to the midpoint of the model square's top edge: it rotates the circle parameterization with mathlib's `Homeomorph.addLeft` and applies the imported relative extension theorem. `Matroid/Internal/AmbientEmbedding.lean` identifies the original and transported full face types, transports face regions and edge incidence, and proves `reembed_hasCycleBondFaceDual_iff`. These are local graph bridges to the imported standard theorem.

`PlaneEmbedding.edgeInterior_has_support_neighborhood` proves, from finite support and edge-interior disjointness, that the full drawing locally equals the selected cycle at each of its edge-interior points. `Matroid/Internal/CycleLocalSides.lean` now uses that equality and pointed Schoenflies to obtain two convex half-balls in the cycle complement. They pull back to connected subsets of actual full-drawing faces. `graphCycle_local_faces` proves that these two faces exhaust all face closures near the chosen interior point and occupy opposite Jordan sides. `graphCycle_edge_incidence_all_interior` propagates incidence along the connected open parameter interval. `graphCycle_edge_has_complete_incidentFaces` therefore supplies exactly two incident faces for every cycle edge, including loops and parallel-edge cycles, without assuming `Finite P.Face`.

`graphCycles_are_faceBoundaries_of_complete_incidence_no_faceFinite` removes the finite-face hypothesis from the cycle-boundary direction. `hasCycleBondFaceDual_of_complete_incidence_and_forestBoundary` reuses the existing graph/matroid reductions: complete incidence for all edges plus exclusion of nonempty forest boundaries suffices for N268. Complete incidence is discharged by the accessibility bridge below, and forest-boundary exclusion by `ForestComplement.lean`. These conditional reductions remain available unchanged; the final unconditional theorem is `PlaneEmbedding.hasCycleBondFaceDual`. `Graph.IsPlanar` is unchanged.

### Accessibility bridge now used for every edge

`Matroid/Internal/EdgeLocalSides.lean` discharges complete incidence for all edges of a finite drawing. It additionally uses these proved declarations from the same pinned Schoenflies closure:

- `Schoenflies.exists_countable_dense_stronglyAccessible`;
- `Schoenflies.StronglyAccessible.polyAccessible`;
- `Schoenflies.arc_complement`;
- `Schoenflies.image_isRelOpen`;
- `Schoenflies.isArcBetween_subarc_of_injOn_I`;
- `Schoenflies.exists_simple_arc_of_polyAccessible`;
- `Schoenflies.IsJordanCurve.of_two_arcs`;
- the `IsArc` compactness/closedness/nonemptiness API and `IsArcBetween.reverse`.

For a nonloop edge, the existing dense-complement theorem and the imported accessibility theorem give accessible points before and after any chosen interior parameter. The imported joining theorem closes the intervening subarc by an arc outside the original edge. This auxiliary Jordan curve need not be a graph cycle: compactness excludes its added arc from the final neighborhood. Relative Schoenflies then standardizes the actual local drawing. Loop edges reuse the checked cycle bridge. `edge_has_complete_incidentFaces` and `exists_complete_incidence` now hold without a cycle hypothesis or `Finite P.Face`, allowing repeated faces. `exists_incidence_with_cycle_boundaries` also supplies every primal cycle boundary from that assignment.

`Matroid/Internal/ForestBoundary.lean` proves `faceBoundary_complement_not_isPreconnected`: any nonempty face-partition boundary separates the complement of its own retained edge support plus the original vertices. This extends the face-partition color across every nonboundary edge using the local face pairs. The sufficient input to `hasCycleBondFaceDual_of_forest_complement` is connectivity of the complement of every retained embedded forest; `ForestComplement.lean` now discharges it through the checked finite-vertex reduction. The new declarations and the newly used imported theorems were audited with `#print axioms`, which lists only `propext`, `Classical.choice`, and `Quot.sound`.

### Arc-supported boundaries and cycle minimality

`Matroid/Internal/ArcBoundary.lean` now uses `JordanCurve.Arcs.exists_proper_arc` from the same pinned Jordan dependency. A proper subset of a graph cycle's edge labels removes a genuine interior point from its trace. Its compact support pulls back to a proper closed subset of the parameter circle. The imported theorem contains that subset in a proper arc, and compactness transports its interval homeomorphism to the drawn plane. The already used `JordanCurve.arc_not_separates` then supplies nonseparation.

The finite-vertex bridge uses these proved mathlib declarations at revision `c55e6e786f49471c72fbddbec5415808896aec1e`, under Apache-2.0:

- `OpenPartialHomeomorph.univBall`, `univBall_source`, `univBall_target`, `univBall_apply_zero`, and `continuous_univBall` from [Ball/Homeomorph.lean](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Analysis/Normed/Module/Ball/Homeomorph.lean);
- `isConnected_compl_singleton_of_one_lt_rank` from [Connected.lean](https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/Mathlib/Analysis/Normed/Module/Connected.lean).

The local punctured ball is the image of the imported connected punctured plane under the imported ball homeomorphism. Extending a hypothetical open partition across one removed point, then finite induction, proves `plane_open_preconnected_sdiff_finite`. No punctured-disk paths or separation theory are constructed. The existing interval obstruction in `PlaneArcDensity.lean` is exported as `plane_dense_compl_of_arc` and reused without a new proof.

`faceBoundary_eq_empty_of_subset_arc` excludes a boundary contained in one drawn arc, retaining all original vertices. Thus `graphCycle_isMinimalFaceBoundary` and `graphCycle_isBond_faceIncidenceGraph` establish the unconditional **primal cycle → dual bond** direction; `exists_incidence_with_cycle_bonds` constructs its complete actual incidence assignment. `retained_complement_preconnected_iff_edge_complement` also removes original vertex points from the sufficient forest-connectivity input. `hasCycleBondFaceDual_of_forest_edge_complement` keeps connectivity outside every forest edge support as an explicit argument; `ForestComplement.lean` supplies its proof and closes the converse and N268/N176 unconditionally for finite drawings. The new source uses standard external topology, not a manuscript proof, and all audited declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Final forest bridge: imported obstruction and local graph gluing

No dependency revision or toolchain changed in the completion pass. The full `lake build` passed with the existing pins at entry, after the forest-lift bridge (9124 jobs), after N268 (9125 jobs), and after N176 (9125 jobs).

Additional proved declarations actually used from `rkirov/jordan_pick` at `b3c9b7cf7358bf81a077d78ad67e6e8247869ddd` (Apache-2.0):

- `JordanCurve.Brouwer.cover` and `JordanCurve.Brouwer.acToSphere`: the real-line covering of `AddCircle 1` and its identification with the geometric unit circle.
- [`JordanCurve.Brouwer.no_retraction`](https://github.com/rkirov/jordan_pick/blob/b3c9b7cf7358bf81a077d78ad67e6e8247869ddd/JordanPick/JordanCurve/Brouwer.lean): no continuous retraction of the closed disk onto its boundary. This is the separation obstruction in the final bridge, applied directly as a proved import.
- [`JordanCurve.isConnected_compl_closedBall`](https://github.com/rkirov/jordan_pick/blob/b3c9b7cf7358bf81a077d78ad67e6e8247869ddd/JordanPick/JordanCurve.lean): the connected exterior used to identify all unbounded complementary components.

Additional mathlib declarations actually used at `c55e6e786f49471c72fbddbec5415808896aec1e` (Apache-2.0):

- `IsCoveringMap.liftPath`, `liftPath_lifts`, and `liftPath_zero` from `Mathlib.Topology.Homotopy.Lifting`.
- `AddCircle.equivIco`, `coe_equivIco`, and `coe_eq_zero_iff` from `Mathlib.Topology.Instances.AddCircle.Defs`.
- `Topology.IsQuotientMap.of_surjective_continuous` and `IsQuotientMap.continuous_iff`: descent from the compact finite family of edge intervals to the actual support.
- `ContinuousMap.exists_restrict_eq` from `Mathlib.Topology.TietzeExtension`, applied only to a real-valued map after the graph-specific lift.
- `continuous_piecewise`: pasting the extended circle map inside a complementary component with radial projection outside it.

Local bridges in `Internal/ForestLift.lean`: `forest_exists_vertex_potential` integrates arbitrary edge increments using the existing isolating-cut criterion for a finite forest. `forest_exists_compatible_lifts` corrects the integer endpoint discrepancies of imported path lifts. `PlaneEmbedding.forest_circle_lift` descends them through the finite edge-interval quotient: joint interior injectivity leaves only common vertices to check. `forest_sphere_extension` then applies Tietze extension to the real lift and maps it back to the circle. Branches and disconnected forest components require no endpoint collars or polygonality.

Local bridges in `Internal/ForestComplement.lean`: if a forest complement had a bounded component containing `o`, its frontier lies in the forest support. `forest_sphere_extension` extends radial projection from that support; pasting with radial projection outside the component would retract a large enclosing disk onto its boundary, contradicting the imported `no_retraction`. `forest_component_not_bounded` records this contradiction. The imported connected disk exterior then gives `forest_edge_complement_preconnected`. This is a graph-specific bridge to existing topology, not a new Jordan separation, crosscut, or Schoenflies theory.

`PlaneEmbedding.hasCycleBondFaceDual` feeds that result into the retained N268 reduction. `PlaneEmbedding.matroid_correspondence` and `IsPlanar.matroid_correspondence` give N176 immediately, with both equalities on the original edge labels. The original faces, continuous paths, loops, and parallel edges are retained. No downstream special-case replacement is used.

Trust audit: all 12 imported/local declarations checked in the completion pass, including both unconditional endpoints, report exactly `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`. Mathematical provenance remains standard external planar duality, as distinguished from the manuscript use above. The forest gluing proofs are local Lean bridges, not manuscript proofs.

## Crosscut and face-cycle declarations audited before completion

- [`Schoenflies.general_crosscut_three_regions`](https://github.com/alonamaloh/schoenflies-lean/blob/05a43d29cde026618777db3d4e4316204ccca237/Schoenflies/GeneralCrosscut.lean) requires `IsCrosscut.polygonal : IsPolygonal P` and `HasArcCollars (inside C) P`. The module is present as a transitive import, but this declaration is not used by the local graph bridge. `PlaneEmbedding.edgePath` permits arbitrary continuous embedded arcs and supplies neither hypothesis. Standardizing one cycle does not make the other edges polygonal.
- [`Graph.face_cycles'`](https://github.com/alonamaloh/schoenflies-lean/blob/05a43d29cde026618777db3d4e4316204ccca237/Schoenflies/FaceCyclesLand.lean) discharges its crosscut premise internally, but requires a finite, two-connected, polygonal `IsDrawing`. `IsDrawing.edge_param` requires full interval injectivity and excludes loops. The module is transitively available, but the theorem is not applied to this project's arbitrary continuous labeled multigraph drawing.
- [`Graph.polygonal_redrawing`](https://github.com/alonamaloh/schoenflies-lean/blob/05a43d29cde026618777db3d4e4316204ccca237/Schoenflies/Graph/Redrawing.lean) preserves the abstract graph and produces a polygonal drawing, but its conclusion supplies no ambient homeomorphism or original-face correspondence. The new transport API applies when an ambient homeomorphism is supplied; this redrawing theorem does not supply one. It also starts from the loop-excluding `IsDrawing` model.

The resolution of the former forest-boundary obligation is recorded in [N268_BLOCKER.md](N268_BLOCKER.md). The final proof uses the original drawing throughout, so these replacement/crosscut declarations were not needed as additional graph imports.

### Additional polygonalization source inspected, not imported

- Repository: <https://github.com/lowrank/gromov-filling-lower-bound>, inspected checkout `880e76637f728ed0b44ba2daf8777ffd9a579ded`.
- Inspected declaration: `LeanEval.Topology.ClassificationOfSurfaces.Moise.PlaneComplex.exists_graph_PL_approximation` in [`ClassificationOfSurfaces/Moise/GraphPolygonalization.lean`](https://github.com/lowrank/gromov-filling-lower-bound/blob/880e76637f728ed0b44ba2daf8777ffd9a579ded/ClassificationOfSurfaces/Moise/GraphPolygonalization.lean). The vendored source retains Apache-2.0 headers; its recorded upstream classification revision is `e3c7230fe78d7b056a415d9ecae6f77887046b32`. The containing project's own license is MIT.
- Exact mismatch: the theorem gives a PL embedding of a finite plane complex, with the same original vertex values and arbitrary uniform closeness to the supplied embedding. Its conclusion gives no ambient plane homeomorphism, no original-complement connectivity, and no correspondence of original and replacement faces. Its forest-complement application would still need those missing bridges. The inspected adapted closure uses Lean/mathlib 4.29.0; no compatibility or axiom-audit claim for this package is made here.
- No declarations from this checkout are imported into the project. The local accessibility bridge instead uses the already pinned and compiled Schoenflies dependency.

### Completion-pass source recheck (not imported)

The original `mccorvie/classification-of-surfaces` repository was inspected directly at `e3c7230fe78d7b056a415d9ecae6f77887046b32` (Apache-2.0; upstream Lean 4.32.0). Its `Moise.PlaneComplex.exists_graph_PL_approximation` and `exists_graph_PL_approximation_facewise` provide close PL replacement maps and preserve vertex values, but give no ambient-homeomorphism or original-complement transport conclusion. No new declaration from that repository was imported or claimed to build here. The upstream `alonamaloh/schoenflies-lean` checkout still resolves to the already pinned `05a43d29cde026618777db3d4e4316204ccca237`. The successful completion instead uses the existing Jordan no-retraction theorem as documented above.

## Depth-5 source check — 2026-10-11

The ten proved depth-5 requirements use the pinned mathlib and local Lean declarations only. For minor algebra and duality, the exact checked declarations are `Matroid.contract_contract`, `contract_delete_comm`, `dual_delete`, and `dual_contract` in `Mathlib/Combinatorics/Matroid/Minor/Contract.lean`. For represented contraction, `Matroid.IsBasis.contract_indep_iff_of_disjoint` in that file and `linearIndepOn_union_iff_quotient` in `Mathlib/LinearAlgebra/Dimension/Constructions.lean` are the mathematical quotient bridge. N264 uses the project's already proved graph-cut/reachability separation lemma and mathlib `Matroid.map_closure_eq`; the statement stays on actual edge labels, including loops and parallel edges. These are kernel proofs, so no literature admission was needed.

For N125, the manuscript cites Young-Bin Choe, James G. Oxley, Alan D. Sokal, and David G. Wagner, *Homogeneous multivariate polynomials with the half-plane property* (2004), [authors' PDF](https://www.math.lsu.edu/~oxley/ycjoasdw.pdf), §8.1, Theorem 8.1(b) and Corollary 8.2(b), with the rectangular Cauchy–Binet formula explicitly stated in footnote 12. The inspected source assumes an `r × n` complex matrix, weights on `n` columns, and full-row-rank minors of size `r`. It gives `det(A diag(x) A*)` as the sum of squared maximal minors times column-weight products; Corollary 8.2 filters unit-modulus nonzero minors to the basis-generating polynomial. Over real TU matrices, `A*` is transpose and the nonzero minor squares are 1. This supports the proposed narrow external premise, **not** a stronger all-rings identity. No theorem was admitted because the bounded proof route was not exhausted and the exact Lean signature remains open. The pre-existing `Matrix.IsTotallyUnimodular.det_submatrix_sq_of_ne_zero` supplies the local TU filter.

For N053, the manuscript's remark after `def:regular-matroid` explains the square-minor field-transfer argument, and the pinned mathlib `Matrix.IsTotallyUnimodular` API plus the project's `intCast_minor_ne_zero_iff` establishes the characteristic-independent nonvanishing part. The remaining indexed rectangular rank/minor equivalence is not supplied by the searched pinned matrix API. N262 is an uncited linear row-space step in the manuscript's `thm:regular-matroid-energy` proof; no precise external theorem with the required reconstruction-equation conclusion was verified, so it was left unresolved. No cited admission was added under `Matroid/External/`.

## Depth-5 continuation source resolution — 2026-10-11

N125 is now proved locally. The exact cited identity is in Choe–Oxley–Sokal–Wagner, [*Homogeneous multivariate polynomials with the half-plane property*](https://www.math.lsu.edu/~oxley/ycjoasdw.pdf), §8.1 Theorem 8.1(b), with the rectangular Cauchy–Binet statement in footnote 12 on p. 50. It assumes an arbitrary complex `r × n` matrix and uses Hermitian transpose; the locally proved `Matrix.weightedCauchyBinet` is its real/field transpose specialization, with explicit increasing enumeration of each `r`-element column subset. `Matrix.weightedCauchyBinet_real` is now a proved specialization, and `Matroid.weightedGram_det_eq_weightedBasesTotal_of_tu` proves the TU minor filtering and indexed-basis identification. No literature theorem is admitted.

For N053, the field-transfer conclusion described in the manuscript's remark after `def:regular-matroid` is also stated in Oxley, [*Matroid Theory* (2nd ed.)](https://www.math.ens.psl.eu/~benoist/refs/Oxley.pdf), regular-matroid discussion in Chapter 6. The local proof establishes the exact rectangular independence/nonzero-minor equivalence, transfers integer TU minors to every field including characteristic two, and constructs an integer TU lift of any real TU coordinate matrix. The project-facing theorem retains the column labels. No external premise is admitted.

N262 is proved directly by row-span factorization on the **already column-restricted** matrix. Its manuscript-specific reconstruction equivalence is formalized for every target, available-column subset, weight factor, and coefficient vector, in both directions. No external source is asserted for that composite statement and no admission was made. N137 follows the manuscript's basis-union argument; the target-free factor is shown strictly positive before cancellation in `ℝ≥0∞`.

## Corrected depth-6 source check — 2026-10-11

For N052, James Oxley, [*Briefly, What Is a Matroid?*](https://www.math.lsu.edu/~oxley/matroid_intro_summ.pdf), Definition 4.3 and Lemma 4.4 (p. 10 of the printed document), defines a real totally unimodular matrix by its square subdeterminants and states that a finite matroid is regular exactly when it is the vector matroid of such a matrix. This is the external mathematical theorem corresponding to the manuscript's Tutte characterization. Oxley's statement uses finite matrix column labels and does not itself give a Lean function carrying the project's `Regular` universe polymorphism and exact ground-set labels into a basis-coordinate matrix. Pinned mathlib supplies no located regular⇒TU converse. N053 already supplies the other direction locally. N052 remains unresolved; no external premise was admitted. The source attributes the result to Tutte [15], while the manuscript cites `Tutte1958,Oxley2011`.

Oxley's same author PDF, Theorem 5.1 (p. 12 printed), states existence of the 2-sum under a common element that is neither a loop nor a coloop and gives its **circuits** as the old circuits avoiding the common element and the joined cross-circuits. This is relevant to N065, but the manuscript specifies **cycles** by symmetric difference, requires each side to have at least three elements, and preserves labeled ground sets. No exact pinned Lean result or complete bridge from that external circuit theorem to the manuscript cycle construction was found; no admission was made. The size condition can be retained as an extra hypothesis once the underlying 2-sum is constructed.

The same source displays the manuscript's exact 5×10 integer matrix for R10 immediately after Theorem 5.1 and describes it as totally unimodular. This corroborates the mathematical N070 goal but is not a kernel-checked finite certificate. `r10Matrix_rank` and `r10_eRank` now prove the rank-five part; the TU proof and regularity application of N053 remain open. The source's mathematical claim was not admitted because N070 is a manuscript definition requiring a checked local realization.

For the proved basic and linear nodes, source-level matches are recorded individually in `DEPTH6_AUDIT.md`. Their imported premises are the pinned mathlib matroid closure, basis, contraction, and linear-span APIs already cited in earlier sections, plus the locally proved N045, N049, N053, N122, N158, and N264 as indicated there. No new external package or unverified mathematical premise was imported. For N174/N175 no exact labeled multigraph minor theorem was identified in the pinned graph API; their `EXTERNAL_UNCITED_STANDARD` ledger tag is not treated as a citation. N207 is a manuscript graph computation and remains local proof work.
