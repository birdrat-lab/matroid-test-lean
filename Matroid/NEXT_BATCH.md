# Next proof batch — dependency-aware scheduler

_Generated proposal; not a mathematical certification or an authorization to admit a theorem._

## Snapshot

- Active nodes: **197**; active edges: **449**.
- Available: **102** (including **2** directly cited assumptions); unresolved: **95**.
- Eligible unresolved nodes: **40**; structural depths are **not** scheduling restrictions.
- Proposed batch size: **2**; cost estimates are ordinal proxies, **not token/time forecasts**.
- Rules: exact manuscript correspondence, matroid-first proof search, cited external premise only after exact-source validation.

## Recommended batch

**Sequence:** N107 → N066

Score **5.682** (heuristic); sum of residual-cost scores **6.0**; **5** additional nodes become eligible after the batch.

| Task | Depth | Provenance | Est. residual cost | Evidence | Immediate descendants |
|---|---:|---|---:|---|---:|
| N107 — Negative target support | 8 | MANUSCRIPT_DEFINITION | 2.0 | heuristic; low | 1 |
| N066 — Regular three-sum construction | 8 | MANUSCRIPT_DEFINITION | 4.0 | Three-sum construction requires significant matroid existence/closure infrastructure | 4 |

**Newly eligible after batch:** N069, N071, N110, N159, N179.

## Alternative ranked batches

| Rank | Dependency-valid sequence | Score | Cost score | Newly eligible |
|---:|---|---:|---:|---:|
| 1 | N107 → N066 | 5.682 | 6.0 | 5 |
| 2 | N107 → N055 | 5.550 | 4.0 | 2 |
| 3 | N107 → N146 | 5.454 | 4.3 | 2 |
| 4 | N107 → N186 | 5.330 | 4.4 | 2 |
| 5 | N066 → N055 | 5.215 | 6.0 | 5 |
| 6 | N066 → N146 | 5.165 | 6.3 | 5 |
| 7 | N066 → N186 | 5.084 | 6.4 | 5 |
| 8 | N107 → N068 | 5.078 | 4.3 | 2 |

## Highest-leverage currently eligible tasks

| ID | Name | Depth | Unresolved descendants | Residual cost score | Provenance |
|---|---|---:|---:|---:|---|
| N068 | Two-sum preserves regularity | 7 | 14 | 2.3 | EXTERNAL_CITED |
| N066 | Regular three-sum construction | 8 | 10 | 4.0 | MANUSCRIPT_DEFINITION |
| N186 | R10 element transitivity | 7 | 8 | 2.4 | EXTERNAL_CITED |
| N146 | Two-sum target-circuit gluing | 7 | 6 | 2.3 | EXTERNAL_CITED |
| N185 | R10 automorphism order | 7 | 6 | 4.0 | CERTIFICATE_DERIVED |
| N161 | Triangle five-sum identity | 7 | 4 | 4.0 | MANUSCRIPT_PROVED |
| N204 | Parallel target construction | 7 | 4 | 3.2 | EXTERNAL_CITED |
| N255 | R10 connectedness | 7 | 4 | 3.5 | PROVENANCE_UNRESOLVED |
| N263 | Maximal nonspanning sets | 8 | 4 | 2.2 | EXTERNAL_UNCITED_STANDARD |
| N037 | Crapo extension classification | 8 | 3 | 3.0 | EXTERNAL_CITED |
| N133 | Dual circuits and cocircuits | 8 | 3 | 2.2 | EXTERNAL_UNCITED_STANDARD |
| N172 | R10 single deletion | 7 | 3 | 2.8 | EXTERNAL_CITED |
| N173 | R10 single contraction | 7 | 3 | 2.8 | EXTERNAL_CITED |
| N182 | R10 total basis count | 7 | 3 | 3.5 | CERTIFICATE_DERIVED |
| N195 | Pointed R10 target circuits | 7 | 3 | 3.0 | CERTIFICATE_DERIVED |
| N267 | Weighted K4 triangle signature | 7 | 3 | 3.0 | MANUSCRIPT_PROVED |
| N152 | Recover parent across a two-element circuit | 7 | 2 | 2.0 | EXTERNAL_UNCITED_STANDARD |
| N154 | Regular effective-weight monotonicity | 9 | 2 | 3.2 | EXTERNAL_UNCITED_STANDARD |
| N019 | Cocircuit basis hitting | 8 | 1 | 2.2 | EXTERNAL_UNCITED_STANDARD |
| N035 | Generated modular cut | 8 | 1 | 2.2 | EXTERNAL_UNCITED_STANDARD |

## Operating constraints

1. Confirm selected tasks against the **exact** manuscript statements and ledger provenance; do not let a score override mathematical dependencies.
2. External-cited status means **verify the exact published theorem**, then use mathlib if exact or isolate an admitted, sourced Lean premise. **Do not auto-admit based on metadata alone.**
3. Manuscript results and finite certificate claims require substantive proofs; track transitive cited assumptions separately from kernel success.
4. After a short batch, update graph/status/cost estimates and rerun this scheduler; retain completed proof code and historical attempts.
5. A new necessary edge requires recomputing topological depths before selecting the next batch.
