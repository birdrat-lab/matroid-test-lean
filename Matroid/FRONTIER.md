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
