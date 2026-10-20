# Next proof batch — dependency-aware scheduler

_Generated proposal; not a mathematical certification or an authorization to admit a theorem._

## Snapshot

- Active nodes: **197**; active edges: **452**.
- Available: **135** (including **10** directly cited assumptions); unresolved: **62**.
- Eligible unresolved nodes: **43**; structural depths are **not** scheduling restrictions.
- Ordinarily selectable now: **39**; next attempted batch index: **31**.
- Proposed batch size: **2**; cost estimates are ordinal proxies, **not token/time forecasts**.
- Rules: exact manuscript correspondence, matroid-first proof search, cited external premise only after exact-source validation.

## Persistent cooldowns

| Node | Blocker | Last attempt | Retry after batch | Evidence |
|---|---|---:|---:|---|
| N161 | TRIANGLE_TU_COEFFICIENT_BRIDGE | 25 | 36 | Matroid/FORMALIZATION_LOG.md persistent invocation batch 25 — All-triangle class matched to nontriangle bases but four TU determinant class coefficients remain |
| N185 | R10_AUTOMORPHISM_720_CERT | 29 | 45 | Matroid/FORMALIZATION_LOG.md following invocation batch 29 — Four-dependency count checked but direct five-set bridge timed out at one million heartbeats and 720 automorphism count remains absent |
| N226 | RECURSIVE_CIRCUIT_INDUCTION | 24 | 35 | Matroid/FORMALIZATION_LOG.md persistent invocation batch 24 — Depth one bound and sharp witness proved but arbitrary nine attachment induction and attainment remain |
| N227 | RECURSIVE_COCIRCUIT_INDUCTION | 30 | 41 | Matroid/FORMALIZATION_LOG.md following invocation batch 30 — Five active root ports and their 5l union bound checked but nine-stage cocircuit support transport and attainment remain |

Expired cooldowns, now selectable when prerequisites permit: N059 (retry batch 31).

## Recommended batch

**Sequence:** N159 → N059

Score **2.905** (heuristic); sum of residual-cost scores **9.1**; **2** additional nodes become eligible after the batch.

| Task | Depth | Provenance | Est. residual cost | Evidence | Immediate descendants |
|---|---:|---|---:|---|---:|
| N159 — Three-sum basis compatibility | 9 | EXTERNAL_CITED | 3.4 | Exact published deletion-contraction three-family formula isolated; remaining manuscript closure-class translation needs matroid minor and rank bridges absent from present infrastructure | 1 |
| N059 — Regular free quotient form | 7 | MANUSCRIPT_PROVED | 5.7 | Standard-form kernel-block map now proved injective and onto the exact kernel; disjoint-label extension free deletion contraction isomorphism and regular converse remain | 1 |

**Newly eligible after batch:** N060, N160.

## Alternative ranked batches

| Rank | Dependency-valid sequence | Score | Cost score | Newly eligible |
|---:|---|---:|---:|---:|
| 1 | N159 → N059 | 2.905 | 9.1 | 2 |
| 2 | N223 → N225 | 2.841 | 6.23 | 1 |
| 3 | N159 → N177 | 2.718 | 6.93 | 1 |
| 4 | N159 → N215 | 2.711 | 6.8 | 1 |
| 5 | N159 → N216 | 2.711 | 6.8 | 1 |
| 6 | N159 → N178 | 2.660 | 6.93 | 1 |
| 7 | N059 → N177 | 2.644 | 9.23 | 1 |
| 8 | N059 → N215 | 2.637 | 9.1 | 1 |

## Highest-leverage currently eligible tasks

| ID | Name | Depth | Unresolved descendants | Residual cost score | Provenance | Selection state |
|---|---|---:|---:|---:|---|---|
| N185 | R10 automorphism order | 7 | 6 | 5.2 | CERTIFICATE_DERIVED | cooling |
| N159 | Three-sum basis compatibility | 9 | 4 | 3.4 | EXTERNAL_CITED | selectable |
| N161 | Triangle five-sum identity | 7 | 4 | 5.2 | MANUSCRIPT_PROVED | cooling |
| N267 | Weighted K4 triangle signature | 7 | 3 | 4.5 | MANUSCRIPT_PROVED | selectable |
| N019 | Cocircuit basis hitting | 8 | 1 | 2.2 | EXTERNAL_UNCITED_STANDARD | selectable |
| N059 | Regular free quotient form | 7 | 1 | 5.7 | MANUSCRIPT_PROVED | selectable |
| N072 | Seymour decomposition theorem | 10 | 1 | 2.4 | EXTERNAL_CITED | selectable |
| N151 | Connectedness at recursive glue | 9 | 1 | 4.5 | PROVENANCE_UNRESOLVED | selectable |
| N177 | Proper R10 minor class | 8 | 1 | 3.53 | MANUSCRIPT_PROVED | selectable |
| N206 | Parallel-target closure union | 9 | 1 | 4.5 | PROVENANCE_UNRESOLVED | selectable |
| N212 | Zero-weight R10 minor limit | 9 | 1 | 2.2 | EXTERNAL_UNCITED_STANDARD | selectable |
| N213 | Infinite-weight R10 minor limit | 9 | 1 | 2.2 | EXTERNAL_UNCITED_STANDARD | selectable |
| N223 | Recursive R10 minor | 9 | 1 | 3.83 | MANUSCRIPT_PROVED | selectable |
| N225 | R10 nongraphic/noncographic status | 7 | 1 | 2.4 | EXTERNAL_CITED | selectable |
| N226 | Recursive target-circuit substitution | 9 | 1 | 4.4 | MANUSCRIPT_PROVED | cooling |
| N227 | Recursive target-cocircuit substitution | 11 | 1 | 4.8 | MANUSCRIPT_PROVED | cooling |
| N038 | Empty cut gives coloop | 9 | 0 | 2.2 | EXTERNAL_UNCITED_STANDARD | selectable |
| N039 | Full cut gives loop | 9 | 0 | 2.2 | EXTERNAL_UNCITED_STANDARD | selectable |
| N040 | Target-extension criterion | 9 | 0 | 3.6 | MANUSCRIPT_PROVED | selectable |
| N069 | Three-sum preserves regularity | 9 | 0 | 2.4 | EXTERNAL_CITED | selectable |

## Operating constraints

1. Confirm selected tasks against the **exact** manuscript statements and ledger provenance; do not let a score override mathematical dependencies.
2. External-cited status means **verify the exact published theorem**, then use mathlib if exact or isolate an admitted, sourced Lean premise. **Do not auto-admit based on metadata alone.**
3. Manuscript results and finite certificate claims require substantive proofs; track transitive cited assumptions separately from kernel success.
4. After a short batch, update graph/status/cost estimates and rerun this scheduler; retain completed proof code and historical attempts.
5. A new necessary edge requires recomputing topological depths before selecting the next batch.
