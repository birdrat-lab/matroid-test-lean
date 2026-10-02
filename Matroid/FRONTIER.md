# Current Matroid formalization frontier

Computed on 2026-10-02 from `Matroid/LEDGER.md` and `Matroid/DEPENDENCY_EDGES.csv` after the subject-module reorganization and primary blocker pass. Active scopes are `CORE_MATROID` and `MATROID_INTERFACE`. A frontier node is active, unresolved, and has every direct active prerequisite at `COMPLETE`.

Active requirements: **196**. Complete: **29**. Current unresolved frontier: **30**. The archived pass-2 frontier had **27** nodes; **7** are newly exposed here. N261 is preserved in the ledger as `OUT_OF_SCOPE_CONTEXT` and excluded.

## Completed blocker results

| ID | Result | Manuscript evidence | Effect |
| --- | --- | --- | --- |
| N025 | `COMPLETE`: `Matroid.contract_rank_toNat_eq_sub` | `def:matroid-minors` | Discharges one direct prerequisite for 14 children and reaches 25 descendants. |
| N043 | `COMPLETE`: `Matroid.vectorMatroid` and its independence/ground/representation API | `def:vector-matroid` | Discharges one direct prerequisite for 10 children and reaches 70 descendants. |
| N061 | `BLOCKED_MATHLIB_INFRASTRUCTURE` | `def:graphic-cographic` | Multigraph forest/cycle theory and augmentation remain to be supplied. |
| N062 | `BLOCKED_MATHLIB_INFRASTRUCTURE` | `def:graphic-cographic` | Requires N061 and a graph bond/graphic cocircuit correspondence. |

## Remaining blockers

The descendant counts below are transitive reachability counts in the active edge graph. The child lists are direct outgoing edges; a descendant may have other incomplete prerequisites as well.

| ID | Direct active children | Transitive descendants | Current constraint |
| --- | --- | ---: | --- |
| N061 | `N062`, `N071`, `N135`, `N172`, `N174`, `N176`, `N207`, `N224`, `N225`, `N258`, `N264`, `N267` | 22 | The pinned multigraph `Graph` API has no cycle/forest predicate or forest augmentation theorem for edge sets; simple-graph acyclicity would change the manuscript graph model. |
| N062 | `N071`, `N135`, `N173`, `N175`, `N176`, `N224`, `N225` | 13 | The new N061 → N062 definitional edge makes N061 a prerequisite; the bond/cocircuit bridge is also absent. |

N062 is **not** in the frontier because N061 remains incomplete. N080 is an independent unresolved frontier node with no recorded descendants; it was outside the optional work condition for this pass.

## Newly exposed frontier

This table lists **all** current unresolved active frontier nodes. “New” means absent from the archived pass-2 resulting frontier; “Retained” means present there. No node in this table was formalized as part of this frontier recomputation.

| ID | Name | Direct active prerequisites | Exposure |
| --- | --- | --- | --- |
| N005 | Extension to a full basis | `N004` | Retained |
| N013 | Flat rank test | `N006`, `N012` | Retained |
| N014 | Spanning basis forces full flat | `N002`, `N012` | Retained |
| N017 | Hyperplane | `N012` | Retained |
| N024 | Deletion | `N023` | Retained |
| N028 | Contraction composition | `N025` | New after N025/N043 |
| N030 | Spanned target contracts to loop | `N007`, `N021`, `N025` | New after N025/N043 |
| N033 | Modular pair of flats | `N006`, `N012` | Retained |
| N036 | Single-element extension | `N023` | Retained |
| N044 | Represented rank | `N006`, `N043` | New after N025/N043 |
| N046 | Represented circuits | `N015`, `N043` | New after N025/N043 |
| N047 | Projective equivalence | `N042` | Retained |
| N049 | Represented contraction | `N025`, `N043` | New after N025/N043 |
| N051 | Regularity | `N042` | Retained |
| N056 | TU pivot and standard form | `N042` | Retained |
| N057 | TU identity augmentation | `N042` | Retained |
| N061 | Graphic matroid | `N001` | Retained |
| N064 | Regular one-sum construction | `N063` | Retained |
| N080 | Finite closure-exchange representation | `N001` | Retained |
| N097 | Flat-lattice join | `N007`, `N012` | Retained |
| N106 | Positive support by target circuits | `N015`, `N081`, `N105` | Retained |
| N111 | Nonzero column rescaling | `N043` | New after N025/N043 |
| N112 | Ambient linear isomorphism | `N043` | New after N025/N043 |
| N125 | TU weighted basis determinant | `N042`, `N122` | Retained |
| N130 | Corank-one uniform target circuit | `N015`, `N129` | Retained |
| N131 | Rank-one uniform target closure | `N007`, `N129` | Retained |
| N143 | Negative restriction coloop | `N007`, `N022`, `N023` | Retained |
| N214 | R10 target loop or coloop ratio | `N021`, `N022`, `N122` | Retained |
| N243 | Free response generators form basis | `N002`, `N020` | Retained |
| N266 | Weighted triangle signature | `N001`, `N007`, `N158` | Retained |

The N061 → N062 dependency correction removes N062 from the former frontier; completing N025 and N043 removes those two nodes while exposing seven others. Re-scoping N261 removes it from active calculations.
