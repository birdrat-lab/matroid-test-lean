# Current Matroid structural-depth frontier

Computed mechanically from `Matroid/LEDGER.md` and `Matroid/DEPENDENCY_EDGES.csv`. Active scopes are `CORE_MATROID` and `MATROID_INTERFACE`; depth is the longest direct-prerequisite chain. `Matroid/DEPTHS.csv` contains the row-level calculation.

## Completed depth-1 result

N061 is `COMPLETE`. `Matroid.graphic` has ground set exactly `G.edgeSet`, and `Matroid.graphic_indep_iff` characterizes its independent sets as subsets with no edge closing a finite walk through the other selected edges. The formal graph-cycle criterion includes loops and parallel-edge cycles. The proof derives the graph cut criterion from reachability and constructs the matroid through closure exchange. Provenance: `def:graphic-cographic`.

Depth 0 and depth 1 are now clear. The minimum unresolved active structural depth is **2**. The user requested work only on N061, so the following layer was recomputed for visibility and **no depth-2 target was attempted**.

## Minimum unresolved depth: 2

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

## Active-node counts by structural depth

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
