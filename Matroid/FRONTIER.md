# Current Matroid structural-depth frontier

Computed mechanically from `Matroid/LEDGER.md` and `Matroid/DEPENDENCY_EDGES.csv`. Active scopes are `CORE_MATROID` and `MATROID_INTERFACE`; depth is the longest direct-prerequisite chain. `Matroid/DEPTHS.csv` contains the row-level calculation.

## Prior depth-1 baseline

N061 is `COMPLETE`. `Matroid.graphic` has ground set exactly `G.edgeSet`, and `Matroid.graphic_indep_iff` characterizes its independent sets as subsets with no edge closing a finite walk through the other selected edges. The formal graph-cycle criterion includes loops and parallel-edge cycles. The proof derives the graph cut criterion from reachability and constructs the matroid through closure exchange. Provenance: `def:graphic-cographic`.

Depth 0 and depth 1 were clear at the start of the depth-2 pass. The following table is the pre-pass state left by the earlier N061-only task.

## Pre-pass minimum unresolved depth: 2

| ID | Name | Direct active prerequisites | Status | Manuscript provenance |
| --- | --- | --- | --- | --- |
| N024 | Deletion | N023 | `IDENTIFIED` | `def:matroid-minors` |
| N036 | Single-element extension | N023 | `IDENTIFIED` | `def:single-element-extension` |
| N046 | Represented circuits | N015, N043 | `IDENTIFIED` | — |
| N047 | Projective equivalence | N042 | `IDENTIFIED` | `def:projective-equivalence` |
| N051 | Regularity | N042 | `IDENTIFIED` | `def:regular-matroid` |
| N056 | TU pivot and standard form | N042 | `IDENTIFIED` | — |
| N057 | TU identity augmentation | N042 | `STATEMENT_DESIGN` | — |
| N062 | Cographic matroid | N001, N061 | `IDENTIFIED` | `def:graphic-cographic` |
| N111 | Nonzero column rescaling | N043 | `IDENTIFIED` | — |
| N112 | Ambient linear isomorphism | N043 | `IDENTIFIED` | — |
| N130 | Corank-one uniform target circuit | N015, N129 | `IDENTIFIED` | — |
| N258 | Incidence representation of a graphic matroid | N043, N061 | `IDENTIFIED` | — |

## Pre-pass active-node counts by structural depth

| Depth | Active | Complete | Unresolved |
| ---: | ---: | ---: | ---: |
| 0 | 1 | 1 | 0 |
| 1 | 9 | 9 | 0 |
| 2 | 19 | 7 | 12 |
| 3 | 12 | 1 | 11 |
| 4 | 19 | 2 | 17 |
| 5 | 32 | 10 | 22 |
| 6 | 25 | 1 | 24 |
| 7 | 21 | 0 | 21 |
| 8 | 21 | 0 | 21 |
| 9 | 24 | 0 | 24 |
| 10 | 9 | 0 | 9 |
| 11 | 3 | 0 | 3 |
| 12 | 1 | 0 | 1 |

No dependency edge changed in the N061 proof pass.

## Active depth-2 target snapshot

Verified mechanically from the canonical ledger and direct-edge CSV before depth-2 proof work. Depths 0 and 1 have no unresolved active requirement. This set is frozen for this pass; newly exposed depth-3 nodes are excluded.

| ID | Name | Direct prerequisites | Manuscript provenance | Initial status |
| --- | --- | --- | --- | --- |
| N024 | Deletion | N023 | `def:matroid-minors` | `IDENTIFIED` |
| N036 | Single-element extension | N023 | `def:single-element-extension` | `IDENTIFIED` |
| N046 | Represented circuits | N015, N043 | S: `prop:represented-minors`, `prop:span-program-matroid-shadow`, `prop:matroid-program-to-linear-span-program`, `prop:support-linear-characterization`, `thm:quotient-normal-form-correct` | `IDENTIFIED` |
| N047 | Projective equivalence | N042 | `def:projective-equivalence` | `IDENTIFIED` |
| N051 | Regularity | N042 | `def:regular-matroid` | `IDENTIFIED` |
| N056 | TU pivot and standard form | N042 | S: `thm:regular-quotient-form`, `thm:regular-support-bound`, `thm:regular-matroid-energy` | `IDENTIFIED` |
| N057 | TU identity augmentation | N042 | S: `thm:regular-quotient-form` | `STATEMENT_DESIGN` |
| N062 | Cographic matroid | N001, N061 | `def:graphic-cographic` | `IDENTIFIED` |
| N111 | Nonzero column rescaling | N043 | S: `prop:representation-scaling`, `prop:representation-coordinate-invariance`, `prop:regular-representations-are-weights` | `IDENTIFIED` |
| N112 | Ambient linear isomorphism | N043 | S: `prop:representation-scaling`, `prop:representation-coordinate-invariance`, `prop:regular-representations-are-weights` | `IDENTIFIED` |
| N130 | Corank-one uniform target circuit | N015, N129 | S: `prop:grover-source-value`, `prop:grover-program-value`, `lem:r10-targeted-query-matroid` | `IDENTIFIED` |
| N258 | Incidence representation of a graphic matroid | N043, N061 | S: `sec:introduction`, `sec:discussion`, `prop:r10-regular-route-b` | `IDENTIFIED` |

## Initial depth-2 pass audit

Recomputed mechanically from the final `LEDGER.md` and unchanged direct-edge DAG into `DEPTHS.csv`. No new mathematical prerequisite or direct dependency edge was discovered. The frozen 12-target snapshot remains above.

- **Depth-2 targets completed (10):** N024, N036, N046, N047, N051, N057, N062, N111, N112, N130.
- **Depth-2 targets unresolved (2):** N056 (`BLOCKED_PROOF`: TU basis-pivot minor identity and standard-form normalization); N258 (`BLOCKED_PROOF`: signed incidence linear independence iff the N061 forest criterion).
- **New prerequisites discovered:** none.
- **Minimum unresolved structural depth:** 2.

| Depth | Active | Complete | Unresolved |
| ---: | ---: | ---: | ---: |
| 0 | 1 | 1 | 0 |
| 1 | 9 | 9 | 0 |
| 2 | 19 | 17 | 2 |
| 3 | 12 | 1 | 11 |
| 4 | 19 | 2 | 17 |
| 5 | 32 | 10 | 22 |
| 6 | 25 | 1 | 24 |
| 7 | 21 | 0 | 21 |
| 8 | 21 | 0 | 21 |
| 9 | 24 | 0 | 24 |
| 10 | 9 | 0 | 9 |
| 11 | 3 | 0 | 3 |
| 12 | 1 | 0 | 1 |

**Total:** 196 active, 41 complete, 155 unresolved. Depth 0 and depth 1 remain clear; depth 2 is incomplete. The unresolved depth-3 layer was not formalized.

## Dedicated N056/N258 attack audit

Recomputed from the final ledger and unchanged direct-edge DAG. N258 is now `COMPLETE`: `Graph.incidence_vectorMatroid_eq_graphic` proves the incidence representation, and companion theorems prove `Represents` and orientation independence. N056 remains `BLOCKED_PROOF`: the normalized matrix is `[I D]` and the row operation preserves the indexed column matroid, but TU preservation reduces to proving TU of `D` by the generalized pivot-minor determinant identity. No new direct prerequisite was found.

- **Depth-2 targets completed:** 11 of the frozen 12, including N258.
- **Depth-2 targets unresolved:** N056 only.
- **Minimum unresolved structural depth:** 2.

| Depth | Active | Complete | Unresolved |
| ---: | ---: | ---: | ---: |
| 0 | 1 | 1 | 0 |
| 1 | 9 | 9 | 0 |
| 2 | 19 | 18 | 1 |
| 3 | 12 | 1 | 11 |
| 4 | 19 | 2 | 17 |
| 5 | 32 | 10 | 22 |
| 6 | 25 | 1 | 24 |
| 7 | 21 | 0 | 21 |
| 8 | 21 | 0 | 21 |
| 9 | 24 | 0 | 24 |
| 10 | 9 | 0 | 9 |
| 11 | 3 | 0 | 3 |
| 12 | 1 | 0 | 1 |

**Total:** 196 active, 42 complete, 154 unresolved. Depth 0 and depth 1 remain clear; depth 2 remains incomplete solely because of N056. No depth-3 formalization was performed.

## N056 continuation audit

N056 is now `COMPLETE`. `Matrix.IsTotallyUnimodular.basisStandardForm` packages the identity basis block, total unimodularity of the nonbasis block, and preservation of the indexed column matroid. Its TU proof uses a block determinant and the unit-row TU theorem. No direct edge changed. The depth table was recomputed from the ledger and direct-edge DAG; all recorded structural depths agree.

- **Depths 0 and 1:** clear.
- **Depth 2:** 19 active, 19 complete, 0 unresolved.
- **Minimum unresolved structural depth:** 3.
- **Total:** 196 active, 43 complete, 153 unresolved.

The N056/N258 audit above records the prior state. No depth-3 formalization was performed in this continuation.

## Active depth-3 target snapshot

After correcting N105 to require `A ⊆ M.E \ {τ}`, `lake build` passes. Structural depths recomputed from the direct-edge DAG agree with `DEPTHS.csv`: depths 0, 1, and 2 are entirely `COMPLETE`; depth 3 has 12 active nodes, of which N006 is already complete.

The frozen unresolved depth-3 set is N005, N027, N048, N052, N053, N064, N070, N125, N135, N181, and N256. No depth-4 target is included in this pass.

## End-of-pass depth-3 audit

The N105 interface now requires `A ⊆ M.E \ {τ}` and the full build passed after that repair. All active nodes at depths 0–2 remain `COMPLETE`. The initial depth-3 target snapshot above is retained as a historical record.

During the depth-3 attempt, manuscript and proof analysis exposed five missing direct edges: N044→N053, N044→N070, N053→N070, N044→N125, and N053→N052. The edge evidence and rationale are in `DEPENDENCY_EDGES.csv` and `FORMALIZATION_LOG.md`. N044 is the existing represented-rank requirement; no new ledger ID was needed. Recomputing the DAG moves N053 and N125 to depth 5 and N052 and N070 to depth 6. Their partial implementations and precise remaining obligations are recorded in the log. No depth-4 target was attacked.

The current active depth-3 layer is N005, N006, N027, N048, N064, N135, N181, and N256. The first seven are `COMPLETE`; N256 remains `BLOCKED_PROOF`. Its `F₂` representability step is checked, but the finite binary cycle-space theorem needed to identify disjoint circuit unions with zero column sums has not been proved. The requested symmetric-difference closure therefore remains open. The minimum unresolved structural depth is **3**.

| Depth | Active | Complete | Unresolved |
| ---: | ---: | ---: | ---: |
| 0 | 1 | 1 | 0 |
| 1 | 9 | 9 | 0 |
| 2 | 19 | 19 | 0 |
| 3 | 8 | 7 | 1 |
| 4 | 6 | 2 | 4 |
| 5 | 24 | 10 | 14 |
| 6 | 24 | 1 | 23 |
| 7 | 33 | 0 | 33 |
| 8 | 30 | 0 | 30 |
| 9 | 28 | 0 | 28 |
| 10 | 10 | 0 | 10 |
| 11 | 3 | 0 | 3 |
| 12 | 1 | 0 | 1 |

**Total:** 196 active, 49 complete, 147 unresolved. This audit is based on the recomputed `DEPTHS.csv`; depth 3 is not yet clear.

## N256 continuation audit

`Matroid.isCircuitUnion_iff_binary_sum_eq_zero` proves the finite binary cycle-space characterization, and `Matroid.Regular.isCircuitUnion_symmDiff` closes N256 for the manuscript's finite regular matroids. The full project builds. No direct dependency edge or ledger ID changed in this continuation. `DEPTHS.csv` was regenerated from the canonical ledger and direct-edge DAG.

**The active Matroid formalization is complete through topological depth 3.** All eight active depth-3 nodes (N005, N006, N027, N048, N064, N135, N181, N256) are `COMPLETE`. The minimum unresolved structural depth is **4**. The unresolved depth-4 frontier is N044 (represented rank), N067 (one-sum preserves regularity), N136 (direct-sum bases), and N176 (planar graphic-cographic correspondence). This continuation did not attack any depth-4 node.

| Depth | Active | Complete | Unresolved |
| ---: | ---: | ---: | ---: |
| 0 | 1 | 1 | 0 |
| 1 | 9 | 9 | 0 |
| 2 | 19 | 19 | 0 |
| 3 | 8 | 8 | 0 |
| 4 | 6 | 2 | 4 |
| 5 | 24 | 10 | 14 |
| 6 | 24 | 1 | 23 |
| 7 | 33 | 0 | 33 |
| 8 | 30 | 0 | 30 |
| 9 | 28 | 0 | 28 |
| 10 | 10 | 0 | 10 |
| 11 | 3 | 0 | 3 |
| 12 | 1 | 0 | 1 |

**Total:** 196 active, 50 complete, 146 unresolved.

## Depth-3 correspondence cleanup audit

N048 now has manuscript-facing `Matroid.Represents.restrict` and `Matroid.Represents.delete` bridges for an arbitrary representation of a finite matroid, via `Matroid.Represents.eq_vectorMatroid`. N005's stale `prop:r10-proper-minors` use location was removed from the canonical ledger after checking the manuscript proof. `lake build` passes.

The ledger, unchanged direct-edge DAG, and `DEPTHS.csv` agree: depths 0–3 remain entirely `COMPLETE` (1, 9, 19, and 8 active nodes respectively). The minimum unresolved structural depth remains **4**. No depth-4 target was attacked in this cleanup.

## Active depth-4 target snapshot

Preflight `lake build` passed. `DEPTHS.csv` records all active nodes at depths 0–3 as `COMPLETE` (1, 9, 19, and 8 respectively). The N048 arbitrary-`Represents` restriction/deletion bridge and corrected N005 provenance are present. The frozen unresolved depth-4 working set is N044, N067, N136, and N176; N007 and N025 are already complete. No depth-5 node belongs to this pass.

## Depth-4 attempt and prerequisite audit

The four frozen targets were attempted. N044, N067, and N136 are `COMPLETE`, each with a manuscript-facing Lean theorem and a successful `lake build`. N176 has a checked conditional bridge: a cycle-bond dual pair of finite labeled multigraphs gives both graphic-cographic matroid equalities. The plane-embedding-to-dual cycle-bond theorem itself remains open. It is now N268, split from N176/M120, with a direct N268→N176 proof edge evidenced by `prop:r10-proper-minors`. The pinned library lacks a compatible plane embedding and dual graph construction. `DEPTHS.csv` was regenerated from the ledger and direct edges; existing node depths did not change. N268 has depth 0 because the geometric graph theorem has no matroid prerequisite. No depth-5 work was performed.

| Depth | Active | Complete | Unresolved |
| ---: | ---: | ---: | ---: |
| 0 | 2 | 1 | 1 (N268) |
| 1 | 9 | 9 | 0 |
| 2 | 19 | 19 | 0 |
| 3 | 8 | 8 | 0 |
| 4 | 6 | 5 | 1 (N176) |
| 5 | 24 | 10 | 14 |
| 6 | 24 | 1 | 23 |
| 7 | 33 | 0 | 33 |
| 8 | 30 | 0 | 30 |
| 9 | 28 | 0 | 28 |
| 10 | 10 | 0 | 10 |
| 11 | 3 | 0 | 3 |
| 12 | 1 | 0 | 1 |

**Current active total:** 197 nodes, 53 complete, 144 unresolved. The minimum unresolved structural depth is **0** (N268); at the original depth-4 layer, N176 remains open. Depth 5 is outside this pass.

### N176 continuation

`Matroid/PlanarDuality.lean` now has an independent geometric `Graph.IsPlanar` predicate: actual edge labels have crossing-free continuous paths in `ℝ × ℝ`, including loops and parallel edges. Faces are connected components of the drawing complement. Edge deletion preserves this planarity; for finite graphs the drawn support is closed and the face region open. A graph on the complementary faces can be formed from proposed edge-face incidences with the same edge labels. The checked `CycleBondDuality.of_cycles_iff_bonds` reduces the needed geometric theorem to one cycle-to-bond equivalence; matroid duality supplies the reverse direction. The proposition `PlaneEmbedding.HasCycleBondFaceDual` states the still-unproved N268 step. Pinned mathlib has no Jordan-curve or compatible planar-dual theorem to establish the edge-side assignment and that equivalence. `lake build` passed; N268 remains blocked at depth 0 and N176 remains missing that prerequisite at depth 4. No depth-5 work was undertaken.

The next N176 continuation strengthened the geometric side of that interface: the chosen faces must now approach interior points of their edges. For finite drawings, checked lemmas identify faces with complement path components and prove each face region open. The missing N268 theorem is precisely existence of actual incident faces plus primal-cycle/dual-bond equivalence from plane separation. Its depth and blocked status, and N176's depth-4 status, remain unchanged; no depth-5 work was done.

The N268 continuation reduced the proposed face graph's cuts to boundaries of partitions of actual complementary faces. Checked Lean theorems identify its bonds with minimal nonempty face boundaries and prove that, for a finite drawing, `HasCycleBondFaceDual` is equivalent to the existence of incident face assignments for which primal minimal cycles are exactly those boundaries. This exposes the remaining local arc-side and embedded-cycle separation theorem without graph-cut bookkeeping. Pinned mathlib supplies neither a compatible Jordan curve theorem nor the needed local side theorem, so N268 remains `BLOCKED_MATHLIB_INFRASTRUCTURE` at depth 0 and N176 remains `MISSING_PREREQUISITE` at depth 4. No depth-5 work was undertaken.

The next N268 attack proved a local isolation theorem for finite vertex and edge sets. At every edge interior point, every open interval of path parameters containing that point has an open plane neighborhood in which all drawn points lie on the corresponding subarc. The proof also establishes unique edge/parameter preimages at interior points, including loops. This removes interference from other edges, vertices, and remote parts of the same edge before a local separation argument. The missing theorem must still produce incident complementary faces and prove that their minimal boundaries are exactly the primal cycles. N268 and N176 retain their blocked statuses; no depth-5 node was attempted.

The following N268 pass checked a conditional existence theorem for one incident face per edge. Face regions cover the complement; if individual edge paths have dense complement, the finite drawing has dense complement; if there are finitely many faces, every plane point lies in the closure of one face region. These hypotheses have not been proved from `PlaneEmbedding`. Establishing empty interior of arbitrary embedded edge paths, finiteness of faces, their two local sides, and cycle separation remains necessary for N268. N268 is still blocked at depth 0 and N176 still awaits it at depth 4; no depth-5 work was attempted.

The next N268 pass proved an exact finite combinatorial decomposition of the remaining cycle–boundary theorem. For a fixed assignment of incident faces, primal cycles are exactly minimal nonempty face boundaries if and only if every primal cycle is some face boundary and every nonempty face boundary contains a primal cycle. `hasCycleBondFaceDual_iff_geometric_conditions` combines this with the existing checked duality bridge. The open work is now the geometric incident-face assignment and those two separation claims. An attempted local proof that embedded arcs have empty interior needs punctured-disk connectivity and an arc cut-point argument; no direct theorem for arbitrary continuous embedded arcs was found in pinned mathlib. N268 remains blocked and N176 remains dependent on it; depth 5 was not attacked.

The next N268 continuation proved that every finite plane drawing has a unique unbounded complementary face. The drawing's support is compact; mathlib's path-connected sphere theorem and a checked radial path proof make the exterior of a sufficiently large disk path connected. The result supplies a face from the actual geometry without any finiteness assumption on the face set. The unresolved work is still local edge-side incidence and the two cycle/face-boundary separation claims. N268 remains `BLOCKED_MATHLIB_INFRASTRUCTURE` and N176 remains `MISSING_PREREQUISITE`; depth 5 was not attacked.

The latest N268 continuation constructed the map from complementary faces of a plane drawing to those after edge deletion. The deleted drawing has smaller support, so each old face lies in one new face; unbounded old faces remain unbounded, and incidence with a surviving edge is preserved. For finite drawings with dense original complement, this map is surjective because every new face region is open and meets the old complement. Density is still conditional on the unproved empty-interior theorem for embedded edge paths. The map does not establish how many faces merge when an edge is removed, nor the local two sides or cycle-separation theorem. N268 remains `BLOCKED_MATHLIB_INFRASTRUCTURE` at depth 0 and N176 remains `MISSING_PREREQUISITE` at depth 4. No depth-5 node was attempted.

Oxley, *Matroid Theory*, Proposition 5.2.1 supplies an exact published baseline for the matroid correspondence: a geometric dual has the dual cycle matroid. Its connected-case proof, Lemma 2.3.7, invokes Jordan-curve separation; the proposition then handles disconnected graphs by direct sums. This confirms N268 as standard mathematics while pinpointing the formal gap between the project's raw `PlaneEmbedding` and an edge-corresponding geometric dual. The manuscript's local Oxley citation in `prop:r10-proper-minors` covers the two displayed minor identities, so the ledger's `EXTERNAL_CITED` provenance for the later planar-duality sentence is flagged for review in `FORMALIZATION_LOG.md`. Statuses are unchanged; no depth-5 work was attempted.
