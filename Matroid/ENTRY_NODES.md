# Internal matroid dependency graph and entry nodes

## Final graph summary

The canonical [`LEDGER.md`](LEDGER.md) has 267 requirements. Its 173 `CORE_MATROID` and 24 `MATROID_INTERFACE` rows form the **197 active nodes** of the internal mathematical graph in [`DEPENDENCY_EDGES.csv`](DEPENDENCY_EDGES.csv). The graph has **439 direct edges**: 313 `DEFINITIONAL` and 126 `PROOF`. It is acyclic. Its indegrees give **2 strict entry nodes** and **2 first-frontier theorem-like nodes** under the direct-prerequisite rule below.

The other 70 ledger rows are retained for provenance and excluded from the formalization graph by scope: 69 `APPLICATION_CONTEXT` rows and N058 (`OUT_OF_SCOPE_CONTEXT`). The application IDs are N074–N079, N082–N096, N098–N104, N108, N113–N115, N117, N120–N121, N123–N124, N126–N128, N142, N145, N155, N168, N198–N199, N202–N203, N208–N211, N230–N231, N234–N237, N241–N242, N245, N249–N254, and N259–N260. In particular, corrected N098 is not a graph root. There are no `SCOPE_UNRESOLVED` rows.

An edge points from a direct prerequisite to the requirement it helps define, state, or prove. The table cites the target's exact TeX label, or the labeled manuscript result at which an unlabeled requirement is used. A direct definitional edge may remain even when an alternate graph path exists, if the target statement independently uses that source vocabulary. The older raw graph was used as audit evidence, not as this edge table. External finite-set, graph, linear-algebra, and arithmetic facts are not represented by invented matroid nodes.

## Strict entry nodes

| ID | Name and mathematical role | Manuscript provenance | Scope | Kind | External foundations |
| --- | --- | --- | --- | --- | --- |
| N001 | Finite matroid: ground set and independence axioms | `def:matroid` | `CORE_MATROID` | Definition | Finite sets, subset operations, elementary logic |
| N261 | TU row restriction: retain a row basis after restricting columns while keeping total unimodularity and full row rank | Proof of `thm:regular-matroid-energy`, at the positive-input row-compression step | `CORE_MATROID` | Theorem-like matrix fact | Matrices, row rank, row deletion, total unimodularity |

N261 is an internal root because the canonical ledger classifies it as active, yet it has no prerequisite among the other active matroid requirements. Its matrix-side scope and exact row-compression hypotheses remain a statement-design question. Root status does not claim that either entry is assumption-free.

## First theorem frontier

For this strict frontier, a theorem-like node qualifies when it has no incoming internal edge, or all its direct incoming edges are from **strict entry definitions/constructions**. Definitions and constructions are not counted as theorem-like merely because a later proof must show that they satisfy their advertised properties. This rule yields:

| ID | Theorem-like requirement | Direct internal prerequisites | Manuscript location |
| --- | --- | --- | --- |
| N080 | A finite extensive, monotone, idempotent closure with Steinitz exchange is the closure of a matroid | N001 (`DEFINITIONAL`) | `def:matroidal-query-system` |
| N261 | TU row restriction preserves a full-row-rank TU representation after retaining a row basis | None | Proof of `thm:regular-matroid-energy` |

This deliberately narrow frontier reflects the required **direct** edge rule. For example, N003 (equal basis cardinalities) waits on N002 (basis), which is a definition but not a strict root because it depends on N001. It becomes available as soon as that one intervening definition is fixed. The frontier is a dependency layer, not a ranking of mathematical value or difficulty.

## Ambiguities and blockers

- **N057 — TU identity augmentation.** The manuscript uses particular block matrices around `thm:regular-quotient-form`; the ledger's general augmentation wording still needs its precise matrix shape fixed. Its incoming N042 edge only records representation vocabulary.
- **N151 — connectedness at recursive glue.** The proof of `prop:recursive-r10-closure` says connectedness is preserved “here,” without stating a general theorem or complete glue hypotheses. The edges from N218 (recursive construction) and N255 (R10 connectedness) capture the direct local inputs; they do not settle that missing statement.
- **N154 — effective-weight monotonicity.** The weighted-ratio assertion used in the Seymour 2-sum discussion needs precise positivity and nondegeneracy hypotheses. Its N139 and N125 proof edges reflect the claimed weighted-basis route, not an independent proof of the monotonicity.
- **N204 and N206 — parallel target.** The prose before `prop:r10-regular-route-b` describes a parallel target copy, 2-sum glue, and union of acceptance conditions. Exact pointed-factor and availability hypotheses remain to be stated. N206 is retained as the closure-union fact; the raw graph's coarser construction was no contradiction.
- **N246 — quotient as contraction.** At `prop:quotient-normal-form-contraction`, relation vectors may be dependent. The represented-contraction edge N049 is direct, but the exact relation-set and quotient identification need statement design.
- **N261 — row restriction.** The proof of `thm:regular-matroid-energy` deletes dependent rows after a column restriction. This is a matrix fact placed in `CORE_MATROID` by the ledger; whether its eventual statement should remain a matroid requirement or only an external linear-algebra prerequisite requires scope review. It is counted as active here rather than silently removed.

Edges entering N057, N151, N154, N204, N206, and N246 carry `MEDIUM` confidence because these statement-design issues affect exact dependency shape. N261 has no internal edge to score. No cycles or unidentified endpoints were found. The manuscript does not determine a unique decomposition of every imported external theorem into its literature prerequisites; this graph records only the manuscript-level obligations.

## Suggested starting boundary

Start with the finite matroid independence system N001, then the immediately dependent basis and circuit notions N002 and N015. The first small proof chain is N003 (equal basis cardinalities), followed by rank N006, closure N007, and the circuit characterization of closure N016. This is the smallest coherent manuscript-facing basis/closure/circuit boundary exposed by the graph, without pulling in regularity, sums, or R10. N080 is the strict first-frontier theorem on an independent closure-axiom branch. N261 is an independent matrix-side root to resolve when the TU weighted-basis branch is specified.
