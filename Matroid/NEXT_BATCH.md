# Next proof batch — dependency-aware scheduler

_Generated proposal; not a mathematical certification or an authorization to admit a theorem._

## Snapshot

- Active nodes: **197**; active edges: **452**.
- Available: **124** (including **10** directly cited assumptions); unresolved: **73**.
- Eligible unresolved nodes: **42**; structural depths are **not** scheduling restrictions.
- Proposed batch size: **2**; cost estimates are ordinal proxies, **not token/time forecasts**.
- Rules: exact manuscript correspondence, matroid-first proof search, cited external premise only after exact-source validation.

## Recommended batch

**Sequence:** N066 → N159

Score **4.396** (heuristic); sum of residual-cost scores **6.7**; **4** additional nodes become eligible after the batch.

| Task | Depth | Provenance | Est. residual cost | Evidence | Immediate descendants |
|---|---:|---|---:|---|---:|
| N066 — Regular three-sum construction | 8 | MANUSCRIPT_DEFINITION | 4.3 | Checked finite common-trace normal form and characteristic-two trace-union equation in addition to quotient correction; remaining conversion between finite side sums and the quotient matroid cycle family | 4 |
| N159 — Three-sum basis compatibility | 9 | EXTERNAL_CITED | 2.4 | heuristic; low | 1 |

**Newly eligible after batch:** N069, N071, N160, N179.

## Alternative ranked batches

| Rank | Dependency-valid sequence | Score | Cost score | Newly eligible |
|---:|---|---:|---:|---:|
| 1 | N066 → N159 | 4.396 | 6.7 | 4 |
| 2 | N066 → N185 | 4.305 | 9.3 | 7 |
| 3 | N066 → N227 | 4.272 | 8.8 | 5 |
| 4 | N066 → N226 | 4.224 | 8.9 | 5 |
| 5 | N066 → N153 | 4.053 | 7.3 | 4 |
| 6 | N066 → N193 | 4.053 | 7.3 | 4 |
| 7 | N066 → N194 | 4.053 | 7.3 | 4 |
| 8 | N066 → N019 | 3.968 | 6.5 | 5 |

## Highest-leverage currently eligible tasks

| ID | Name | Depth | Unresolved descendants | Residual cost score | Provenance |
|---|---|---:|---:|---:|---|
| N066 | Regular three-sum construction | 8 | 10 | 4.3 | MANUSCRIPT_DEFINITION |
| N185 | R10 automorphism order | 7 | 6 | 5.0 | CERTIFICATE_DERIVED |
| N161 | Triangle five-sum identity | 7 | 4 | 5.4 | MANUSCRIPT_PROVED |
| N182 | R10 total basis count | 7 | 3 | 3.5 | CERTIFICATE_DERIVED |
| N267 | Weighted K4 triangle signature | 7 | 3 | 4.5 | MANUSCRIPT_PROVED |
| N152 | Recover parent across a two-element circuit | 7 | 2 | 4.5 | EXTERNAL_UNCITED_STANDARD |
| N154 | Regular effective-weight monotonicity | 9 | 2 | 3.2 | EXTERNAL_UNCITED_STANDARD |
| N019 | Cocircuit basis hitting | 8 | 1 | 2.2 | EXTERNAL_UNCITED_STANDARD |
| N059 | Regular free quotient form | 7 | 1 | 6.0 | MANUSCRIPT_PROVED |
| N151 | Connectedness at recursive glue | 9 | 1 | 4.5 | PROVENANCE_UNRESOLVED |
| N177 | Proper R10 minor class | 8 | 1 | 3.53 | MANUSCRIPT_PROVED |
| N206 | Parallel-target closure union | 9 | 1 | 4.5 | PROVENANCE_UNRESOLVED |
| N212 | Zero-weight R10 minor limit | 9 | 1 | 2.2 | EXTERNAL_UNCITED_STANDARD |
| N213 | Infinite-weight R10 minor limit | 9 | 1 | 2.2 | EXTERNAL_UNCITED_STANDARD |
| N225 | R10 nongraphic/noncographic status | 7 | 1 | 2.4 | EXTERNAL_CITED |
| N226 | Recursive target-circuit substitution | 9 | 1 | 4.6 | MANUSCRIPT_PROVED |
| N227 | Recursive target-cocircuit substitution | 11 | 1 | 4.5 | MANUSCRIPT_PROVED |
| N038 | Empty cut gives coloop | 9 | 0 | 2.2 | EXTERNAL_UNCITED_STANDARD |
| N039 | Full cut gives loop | 9 | 0 | 2.2 | EXTERNAL_UNCITED_STANDARD |
| N040 | Target-extension criterion | 9 | 0 | 3.6 | MANUSCRIPT_PROVED |

## Operating constraints

1. Confirm selected tasks against the **exact** manuscript statements and ledger provenance; do not let a score override mathematical dependencies.
2. External-cited status means **verify the exact published theorem**, then use mathlib if exact or isolate an admitted, sourced Lean premise. **Do not auto-admit based on metadata alone.**
3. Manuscript results and finite certificate claims require substantive proofs; track transitive cited assumptions separately from kernel success.
4. After a short batch, update graph/status/cost estimates and rerun this scheduler; retain completed proof code and historical attempts.
5. A new necessary edge requires recomputing topological depths before selecting the next batch.
