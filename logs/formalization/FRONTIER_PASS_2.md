# Frontier pass 2: frozen targets

Pass date: 2026-10-02.

Mechanically computed from `Matroid/LEDGER.md` and `Matroid/DEPENDENCY_EDGES.csv`: 197 active nodes, 7 complete nodes, 26 frontier targets. This matches the expected current frontier in `AGENTS.md`.

**This target set is frozen for the duration of this pass.**

| ID | Name | Direct internal prerequisites | Initial status | Scope | Manuscript TeX provenance |
| --- | --- | --- | --- | --- | --- |
| N004 | Extension within a subset | N002 | IDENTIFIED | CORE_MATROID | S: `prop:cocircuit-separates-closure`, `prop:support-linear-characterization`, `prop:r10-proper-minors` |
| N008 | Closure extensivity | N007 | IDENTIFIED | CORE_MATROID | S: `prop:target-extension-criterion`, `prop:query-separation-cover` |
| N009 | Closure monotonicity | N007 | IDENTIFIED | CORE_MATROID | S: `prop:target-extension-criterion`, `prop:query-separation-cover` |
| N010 | Closure idempotence | N007 | IDENTIFIED | CORE_MATROID | S: `prop:target-extension-criterion`, `prop:query-separation-cover` |
| N011 | Steinitz closure exchange | N007 | IDENTIFIED | CORE_MATROID | S: `prop:agreement-set-flat`, `lem:r10-minimal-positive` |
| N012 | Flat | N007 | IDENTIFIED | CORE_MATROID | `def:matroid-flat` |
| N020 | Free matroid | N001, N002, N007 | IDENTIFIED | CORE_MATROID | `def:free-matroid` |
| N021 | Loop | N007, N015 | IDENTIFIED | CORE_MATROID | `def:loop-coloop` |
| N022 | Coloop | N002 | IDENTIFIED | CORE_MATROID | `def:loop-coloop` |
| N023 | Restriction | N001 | IDENTIFIED | CORE_MATROID | `def:matroid-minors` |
| N025 | Contraction rank | N006 | IDENTIFIED | CORE_MATROID | `def:matroid-minors` |
| N031 | Fundamental circuit | N002, N015 | IDENTIFIED | CORE_MATROID | `def:fundamental-circuit` |
| N042 | Matroid representation | N001 | IDENTIFIED | CORE_MATROID | `def:matroid-representability` |
| N043 | Vector matroid | N001 | IDENTIFIED | CORE_MATROID | `def:vector-matroid` |
| N061 | Graphic matroid | N001 | IDENTIFIED | CORE_MATROID | `def:graphic-cographic` |
| N062 | Cographic matroid | N001 | IDENTIFIED | CORE_MATROID | `def:graphic-cographic` |
| N063 | Regular-matroid cycle | N015 | IDENTIFIED | CORE_MATROID | `def:matroid-cycle` |
| N073 | Colored matroid | N001 | IDENTIFIED | CORE_MATROID | `def:colored-matroid` |
| N080 | Finite closure-exchange representation | N001 | IDENTIFIED | CORE_MATROID | `def:matroidal-query-system` |
| N081 | Pointed matroid port | N007, N015, N016 | IDENTIFIED | MATROID_INTERFACE | S: `prop:minimal-query-circuits`, `prop:positive-support-circuits`, `lem:r10-minimal-positive` |
| N105 | Positive target support | N007 | IDENTIFIED | MATROID_INTERFACE | `def:positive-support` |
| N122 | Weighted target basis sums | N002 | IDENTIFIED | CORE_MATROID | S: `thm:regular-matroid-energy`, `prop:seymour-one-sum`, `thm:seymour-two-sum`, `thm:r10-fixed-weight-evaluation` |
| N129 | Uniform matroid | N001 | IDENTIFIED | CORE_MATROID | S: `prop:grover-source-value`, `prop:grover-program-value`, `lem:r10-targeted-query-matroid` |
| N132 | Dual matroid bases | N002 | IDENTIFIED | CORE_MATROID | S: `def:graphic-cographic`, `prop:r10-proper-minors`, `prop:recursive-r10-closure` |
| N158 | Five 3-sum boundary classes | N007, N015 | IDENTIFIED | CORE_MATROID | S: `lem:seymour-three-sum-five`, `prop:regular-triangle-identity` |
| N261 | TU row restriction | none | STATEMENT_DESIGN | CORE_MATROID | S: `thm:regular-matroid-energy` |

## Resulting frontier

Computed mechanically after the pass from the updated ledger and unchanged direct-edge CSV. The frontier has **27 unresolved active nodes**: 21 newly exposed nodes and the six blocked targets from the frozen pass. No newly exposed node was formalized.

| Newly available ID | Name | Direct prerequisites | Why exposed |
| --- | --- | --- | --- |
| N005 | Extension to a full basis | N004 | Completion of N004 in this pass |
| N013 | Flat rank test | N006, N012 | Completion of N012 in this pass |
| N014 | Spanning basis forces full flat | N002, N012 | Completion of N012 in this pass |
| N017 | Hyperplane | N012 | Completion of N012 in this pass |
| N024 | Deletion | N023 | Completion of N023 in this pass |
| N033 | Modular pair of flats | N006, N012 | Completion of N012 in this pass |
| N036 | Single-element extension | N023 | Completion of N023 in this pass |
| N047 | Projective equivalence | N042 | Completion of N042 in this pass |
| N051 | Regularity | N042 | Completion of N042 in this pass |
| N056 | TU pivot and standard form | N042 | Completion of N042 in this pass |
| N057 | TU identity augmentation | N042 | Completion of N042 in this pass |
| N064 | Regular one-sum construction | N063 | Completion of N063 in this pass |
| N097 | Flat-lattice join | N007, N012 | Completion of N012 in this pass |
| N106 | Positive support by target circuits | N015, N081, N105 | Completion of N081, N105 in this pass |
| N125 | TU weighted basis determinant | N042, N122 | Completion of N042, N122 in this pass |
| N130 | Corank-one uniform target circuit | N015, N129 | Completion of N129 in this pass |
| N131 | Rank-one uniform target closure | N007, N129 | Completion of N129 in this pass |
| N143 | Negative restriction coloop | N007, N022, N023 | Completion of N022, N023 in this pass |
| N214 | R10 target loop or coloop ratio | N021, N022, N122 | Completion of N021, N022, N122 in this pass |
| N243 | Free response generators form basis | N002, N020 | Completion of N020 in this pass |
| N266 | Weighted triangle signature | N001, N007, N158 | Completion of N158 in this pass |

### Branches still held by incomplete targets

| Blocked target still in frontier | Direct active descendants held |
| --- | --- |
| N025 — Contraction rank | N026, N028, N029, N030, N049, N134, N141, N144, N152, N157, N166, N173, N213, N246 |
| N043 — Vector matroid | N044, N045, N046, N048, N049, N070, N111, N112, N258, N262 |
| N061 — Graphic matroid | N071, N135, N172, N174, N176, N207, N224, N225, N258, N264, N267 |
| N062 — Cographic matroid | N071, N135, N173, N175, N176, N224, N225 |
| N080 — Finite closure-exchange representation | none recorded |
| N261 — TU row restriction | none recorded |

Targets attempted: **26**. Completed: **20**. Blocked: **6**. Frontier size before: **26**. Frontier size after: **27**. The six blocked targets remain unresolved and do not expose their descendants.
