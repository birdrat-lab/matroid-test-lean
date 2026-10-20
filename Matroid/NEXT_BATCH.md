# Next proof batch — dependency-aware scheduler

_Generated proposal; not a mathematical certification or an authorization to admit a theorem._

## Snapshot

- Active nodes: **198**; active edges: **454**.
- Available: **140** (including **12** directly cited assumptions); unresolved: **58**.
- Eligible unresolved nodes: **40**; structural depths are **not** scheduling restrictions.
- Ordinarily selectable now: **35**; next attempted batch index: **36**.
- Proposed batch size: **2**; cost estimates are ordinal proxies, **not token/time forecasts**.
- Rules: exact manuscript correspondence, matroid-first proof search, cited external premise only after exact-source validation.

## Persistent cooldowns

| Node | Blocker | Last attempt | Retry after batch | Evidence |
|---|---|---:|---:|---|
| N059 | FREE_QUOTIENT_LABEL_BRIDGE | 33 | 44 | Matroid/FORMALIZATION_LOG.md current invocation batch 33 — Augmented matrix quotient action checked but disjoint free regular extension and identity-on-E contraction remain |
| N159 | THREE_SUM_CLASS_TRANSLATION | 31 | 37 | Matroid/FORMALIZATION_LOG.md current invocation batch 31 — Deleted-side basis matches all-triangle closure class but contraction and augmented singleton classes still lack bidirectional bridge |
| N185 | R10_AUTOMORPHISM_720_CERT | 29 | 45 | Matroid/FORMALIZATION_LOG.md following invocation batch 29 — Four-dependency count checked but direct five-set bridge timed out at one million heartbeats and 720 automorphism count remains absent |
| N226 | RECURSIVE_CIRCUIT_INDUCTION | 35 | 51 | Matroid/FORMALIZATION_LOG.md current invocation batch 35 — Root five-port count and 5l bound checked but arbitrary nine-stage support transport and attainment remain |
| N227 | RECURSIVE_COCIRCUIT_INDUCTION | 30 | 41 | Matroid/FORMALIZATION_LOG.md following invocation batch 30 — Five active root ports and their 5l union bound checked but nine-stage cocircuit support transport and attainment remain |

Expired cooldowns, now selectable when prerequisites permit: N161 (retry batch 36).

## Recommended batch

**Sequence:** N223 → N161

Score **3.340** (heuristic); sum of residual-cost scores **9.9**; **2** additional nodes become eligible after the batch.

| Task | Depth | Provenance | Est. residual cost | Evidence | Immediate descendants |
|---|---:|---|---:|---|---:|
| N223 — Recursive R10 minor | 9 | MANUSCRIPT_PROVED | 4.7 | Exact-labeled R10 minor predicate and base case checked; arbitrary nine-stage proof needs a proper-two-sum minor commutation theorem not present in current local interface | 1 |
| N161 — Triangle five-sum identity | 7 | MANUSCRIPT_PROVED | 5.2 | All-triangle class now identified with nontriangle bases; four weighted TU Cauchy-Binet class comparisons and determinant update still remain | 3 |

**Newly eligible after batch:** N164, N224.

## Alternative ranked batches

| Rank | Dependency-valid sequence | Score | Cost score | Newly eligible |
|---:|---|---:|---:|---:|
| 1 | N223 → N161 | 3.340 | 9.9 | 2 |
| 2 | N223 → N040 | 2.892 | 8.3 | 1 |
| 3 | N223 → N180 | 2.892 | 8.3 | 1 |
| 4 | N223 → N116 | 2.850 | 8.42 | 1 |
| 5 | N161 → N040 | 2.849 | 8.8 | 1 |
| 6 | N161 → N180 | 2.849 | 8.8 | 1 |
| 7 | N223 → N220 | 2.814 | 8.53 | 1 |
| 8 | N223 → N221 | 2.814 | 8.53 | 1 |

## Highest-leverage currently eligible tasks

| ID | Name | Depth | Unresolved descendants | Residual cost score | Provenance | Selection state |
|---|---|---:|---:|---:|---|---|
| N185 | R10 automorphism order | 7 | 6 | 5.2 | CERTIFICATE_DERIVED | cooling |
| N159 | Three-sum basis compatibility | 9 | 4 | 3.0 | MANUSCRIPT_PROVED | cooling |
| N161 | Triangle five-sum identity | 7 | 4 | 5.2 | MANUSCRIPT_PROVED | selectable |
| N267 | Weighted K4 triangle signature | 7 | 3 | 4.5 | MANUSCRIPT_PROVED | selectable |
| N059 | Regular free quotient form | 7 | 1 | 5.4 | MANUSCRIPT_PROVED | cooling |
| N072 | Seymour decomposition theorem | 10 | 1 | 2.4 | EXTERNAL_CITED | selectable |
| N151 | Connectedness at recursive glue | 9 | 1 | 4.5 | PROVENANCE_UNRESOLVED | selectable |
| N177 | Proper R10 minor class | 8 | 1 | 4.2 | MANUSCRIPT_PROVED | selectable |
| N206 | Parallel-target closure union | 9 | 1 | 4.5 | PROVENANCE_UNRESOLVED | selectable |
| N212 | Zero-weight R10 minor limit | 9 | 1 | 2.2 | EXTERNAL_UNCITED_STANDARD | selectable |
| N213 | Infinite-weight R10 minor limit | 9 | 1 | 2.2 | EXTERNAL_UNCITED_STANDARD | selectable |
| N223 | Recursive R10 minor | 9 | 1 | 4.7 | MANUSCRIPT_PROVED | selectable |
| N226 | Recursive target-circuit substitution | 9 | 1 | 4.2 | MANUSCRIPT_PROVED | cooling |
| N227 | Recursive target-cocircuit substitution | 11 | 1 | 4.8 | MANUSCRIPT_PROVED | cooling |
| N038 | Empty cut gives coloop | 9 | 0 | 2.2 | EXTERNAL_UNCITED_STANDARD | selectable |
| N039 | Full cut gives loop | 9 | 0 | 2.2 | EXTERNAL_UNCITED_STANDARD | selectable |
| N040 | Target-extension criterion | 9 | 0 | 3.6 | MANUSCRIPT_PROVED | selectable |
| N069 | Three-sum preserves regularity | 9 | 0 | 2.4 | EXTERNAL_CITED | selectable |
| N110 | Negative support in a representation | 10 | 0 | 3.97 | MANUSCRIPT_PROVED | selectable |
| N116 | Regular real representations parameterize by weights | 8 | 0 | 3.72 | MANUSCRIPT_PROVED | selectable |

## Operating constraints

1. Confirm selected tasks against the **exact** manuscript statements and ledger provenance; do not let a score override mathematical dependencies.
2. External-cited status means **verify the exact published theorem**, then use mathlib if exact or isolate an admitted, sourced Lean premise. **Do not auto-admit based on metadata alone.**
3. Manuscript results and finite certificate claims require substantive proofs; track transitive cited assumptions separately from kernel success.
4. After a short batch, update graph/status/cost estimates and rerun this scheduler; retain completed proof code and historical attempts.
5. A new necessary edge requires recomputing topological depths before selecting the next batch.
