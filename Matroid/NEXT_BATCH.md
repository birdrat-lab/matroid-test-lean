# Next proof batch — dependency-aware scheduler

_Generated proposal; not a mathematical certification or an authorization to admit a theorem._

## Snapshot

- Active nodes: **197**; active edges: **450**.
- Available: **103** (including **3** directly cited assumptions); unresolved: **94**.
- Eligible unresolved nodes: **39**; structural depths are **not** scheduling restrictions.
- Proposed batch size: **2**; cost estimates are ordinal proxies, **not token/time forecasts**.
- Rules: exact manuscript correspondence, matroid-first proof search, cited external premise only after exact-source validation.

## Recommended batch

**Sequence:** N146 → N186

Score **4.660** (heuristic); sum of residual-cost scores **4.7**; **2** additional nodes become eligible after the batch.

| Task | Depth | Provenance | Est. residual cost | Evidence | Immediate descendants |
|---|---:|---|---:|---|---:|
| N146 — Two-sum target-circuit gluing | 7 | EXTERNAL_CITED | 2.3 | Externally cited circuit gluing; source correspondence remains unverified | 2 |
| N186 — R10 element transitivity | 7 | EXTERNAL_CITED | 2.4 | External R10 automorphism transitivity needs exact source and indexed action correspondence | 3 |

**Newly eligible after batch:** N147, N188.

## Alternative ranked batches

| Rank | Dependency-valid sequence | Score | Cost score | Newly eligible |
|---:|---|---:|---:|---:|
| 1 | N146 → N186 | 4.660 | 4.7 | 2 |
| 2 | N186 → N185 | 4.488 | 6.4 | 4 |
| 3 | N146 → N161 | 4.447 | 6.3 | 2 |
| 4 | N186 → N161 | 4.378 | 6.4 | 2 |
| 5 | N186 → N068 | 4.316 | 4.7 | 2 |
| 6 | N146 → N059 | 4.278 | 6.3 | 2 |
| 7 | N146 → N068 | 4.250 | 4.6 | 2 |
| 8 | N146 → N032 | 4.220 | 5.62 | 2 |

## Highest-leverage currently eligible tasks

| ID | Name | Depth | Unresolved descendants | Residual cost score | Provenance |
|---|---|---:|---:|---:|---|
| N068 | Two-sum preserves regularity | 7 | 14 | 2.3 | EXTERNAL_CITED |
| N066 | Regular three-sum construction | 8 | 10 | 6.0 | MANUSCRIPT_DEFINITION |
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
| N032 | Cocircuit separating closure | 8 | 2 | 3.32 | MANUSCRIPT_PROVED |
| N152 | Recover parent across a two-element circuit | 7 | 2 | 2.0 | EXTERNAL_UNCITED_STANDARD |
| N154 | Regular effective-weight monotonicity | 9 | 2 | 3.2 | EXTERNAL_UNCITED_STANDARD |
| N019 | Cocircuit basis hitting | 8 | 1 | 2.2 | EXTERNAL_UNCITED_STANDARD |

## Operating constraints

1. Confirm selected tasks against the **exact** manuscript statements and ledger provenance; do not let a score override mathematical dependencies.
2. External-cited status means **verify the exact published theorem**, then use mathlib if exact or isolate an admitted, sourced Lean premise. **Do not auto-admit based on metadata alone.**
3. Manuscript results and finite certificate claims require substantive proofs; track transitive cited assumptions separately from kernel success.
4. After a short batch, update graph/status/cost estimates and rerun this scheduler; retain completed proof code and historical attempts.
5. A new necessary edge requires recomputing topological depths before selecting the next batch.
