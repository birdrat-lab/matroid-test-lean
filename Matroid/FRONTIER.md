# Current Matroid structural-depth frontier

Computed mechanically from `Matroid/LEDGER.md` and `Matroid/DEPENDENCY_EDGES.csv` after the depth-1 pass. Only `CORE_MATROID` and `MATROID_INTERFACE` rows are active. Depth is the length of the longest directed prerequisite chain ending at each node; nodes with no active prerequisite have depth 0. `Matroid/DEPTHS.csv` records every active node and its direct prerequisites.

At the start of this pass, the minimum unresolved depth was **1**, containing N061 and N080. N080 is now complete. The final minimum unresolved depth remains **1**, containing **N061 Graphic matroid**. The depth-2 set was not started.

## Minimum unresolved depth

| ID | Name | Status | Direct prerequisites | Manuscript label |
| --- | --- | --- | --- | --- |
| N061 | Graphic matroid | `STATEMENT_DESIGN`; `BLOCKED_MATHLIB_INFRASTRUCTURE` | N001 (`COMPLETE`) | `def:graphic-cographic` |

## Focused depth-1 blocker

`Graph.edgeCutMatroid` now constructs a matroid on the subtype of actual labeled graph edges. Its independence theorem says each selected edge admits a graph cut containing that edge and no other selected edge. The cut family is closed under symmetric difference, which gives Steinitz exchange for the corresponding closure operator.

**Unfinished N061 statement:** `def:graphic-cographic` specifies independent sets by absence of graph cycles. The pinned mathlib multigraph `Graph` API has edge cuts and bonds but no walk/cycle predicate or cycle-free/bridge equivalence. A Lean proof that the cut-isolation criterion is equivalent to a cycle-free edge set is still required before N061 can be marked `COMPLETE`. This comparison is part of the construction proof, not a separate manuscript dependency; no new ledger node or edge was added.

`Matroid.ofFiniteClosure` and `Matroid.ofFiniteClosure_closure` complete N080. They construct a finite matroid from a Steinitz-exchange closure and prove that its closure equals the supplied operator on every set.

## Active-node counts by structural depth

| Depth | Active | Complete | Unresolved |
| ---: | ---: | ---: | ---: |
| 0 | 1 | 1 | 0 |
| 1 | 9 | 8 | 1 |
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

## Held depth-2 layer

Twelve active depth-2 requirements remain unresolved: `N024`, `N036`, `N046`, `N047`, `N051`, `N056`, `N057`, `N062`, `N111`, `N112`, `N130`, `N258`. This list is informational; no depth-2 target snapshot was frozen or attacked because depth 1 is unresolved.
