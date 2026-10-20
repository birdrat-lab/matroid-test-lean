# Current Matroid structural-depth frontier

Computed mechanically from `Matroid/LEDGER.md` and `Matroid/DEPENDENCY_EDGES.csv`. Active scopes are `CORE_MATROID` and `MATROID_INTERFACE`; depth is the longest direct-prerequisite chain. `Matroid/DEPTHS.csv` contains the row-level calculation.

**Current status (2026-10-20): 121/197 active nodes are kernel-proved, ten are directly cited assumptions, and four have completed local conditional proofs.** The clean strict scheduler counts 135 available, 62 unresolved, 452 direct active edges, and 43 eligible unresolved nodes. Structural depths are audit metadata, not an execution order. The next recommendation, with persistent cooldowns and no run-local deferrals, is **N159 → N059**, score 2.905.

## Following five scheduler batches (indices 26–30)

| Batch | Scheduler selection and score | Outcome |
| --- | --- | --- |
| 26 | N188 → N152; 2.397 | Both `KERNEL_PROVED`: pointed R10 basis-polynomial equivariance and exact two-element-child relabeling. |
| 27 | N066 → N159; 4.396 | N066 `KERNEL_PROVED`: proper three-sum existence and cycle correspondence. N159 `UNRESOLVED`: exact cited basis-family helper isolated; manuscript closure-class bridge open. |
| 28 | N071 → N179; 4.012 | Both `KERNEL_PROVED`: exact decomposition object and R10 exclusion from proper three-sum child slots. |
| 29 | N185 → N187; 3.938 | N185 `UNRESOLVED`: finite four-dependency count checked, 720 automorphism count open. N187 skipped because N185 remained unavailable. |
| 30 | N227 → N154; 2.866 | N227 `UNRESOLVED`: five active ports and `5*l` local bound checked, recursive transport open. N154 `CONDITIONAL_PROOF` through the precisely sourced regular Rayleigh premise. |

`FOLLOWING_FIVE_BATCH_AUDIT.md` records full source/declaration correspondence and transitive axioms. Attempt events 46–54 are append-only in `SCHEDULER_ATTEMPTS.csv`; N159 was deferred only within this run, while repeated N185/N227 blockers triggered persistent cooldowns. No new direct edge or depth was needed. Full `lake build` passed (9214 jobs), the tracked axiom audit passed, 15 scheduler tests passed, and `git diff --check` passed. N161/N185/N226/N227 are cooling until batches 36/45/35/41 respectively; N059's cooldown has expired. N060/N160 are only predicted to become eligible after the next proposed batch closes.

## Earlier five-batch run

| Batch | Scheduler selection | Outcome |
| --- | --- | --- |
| 1 | N255 → N218 | Both `KERNEL_PROVED`: finite R10 common-circuit certificate and exact recursive-stage specification. |
| 2 | N195 → N147 | N195 `KERNEL_PROVED` by finite target-circuit certificate; N147 `CONDITIONAL_PROOF` via N146. |
| 3 | N152 → N150 | N152 partial cycle/relabeling lemmas checked, full isomorphism unresolved and rescheduled; N150 `CONDITIONAL_PROOF` via N138. |
| 4 | N204 → N066 | N204 source provenance corrected and its construction `KERNEL_PROVED`; N066 proper three-sum specification/span lemma checked, cycle correspondence unresolved and rescheduled. |
| 5 | N172 → N173 | Both exact Oxley Lemma 6.6.9 statements source-verified as isolated `CITED_ASSUMPTION` premises, with checked real-R10 and labeled K3,3 bridges. |

The full `lake build` passed (9183 jobs), the tracked `FiveBatchAxiomAudit` printed `sorryAx` only for expected citation-relative declarations, all eight scheduler tests passed, and `git diff --check` passed. N152 and N066 were deferred only for this invocation. The final clean scheduler restored them to eligibility and selected N066→N159. The attempt details and source comparisons are in `PROOF_BUDGET.md`, `FORMALIZATION_LOG.md`, and `SOURCES.md`.

## Earlier automated five-batch run

| Batch | Scheduler selection | Outcome |
| --- | --- | --- |
| 1 | N146 → N186 | Both exact Oxley results source-verified and isolated as `CITED_ASSUMPTION`; local labeled bridges checked. |
| 2 | N185 → N187 | N185 remains unresolved because the finite automorphism completeness certificate and referenced ancillary verifier are absent; dependent N187 was not attempted. |
| 3 | N161 → N068 | N161's final algebra checked, determinant coefficient bridge unresolved; N068 source-verified as `CITED_ASSUMPTION`. |
| 4 | N059 → N032 | N059 kernel-block equation checked, quotient extension unresolved; N032 `KERNEL_PROVED`. The provisional N218→N195 proposal was corrected by adding the genuine N255→N218 edge before this selection. |
| 5 | N107 → N263 | Both `KERNEL_PROVED`, including the manuscript's hyperplane-complement cocircuit interface. Added N032→N263 and recomputed all affected depths before proof work. |

The full `lake build`, tracked `MultiBatchAxiomAudit`, eight scheduler tests, and clean strict scheduler regeneration passed. N185, N161, and N059 have factual residual estimates and remain eligible at the next invocation. The source matches and attempt details are in `SOURCES.md`, `PROOF_BUDGET.md`, and `FORMALIZATION_LOG.md`. Sections below retain earlier historical frontiers.

## Scheduler-directed short batch: N066 → N055

| ID | Direct prerequisites | Result | Trust |
| --- | --- | --- | --- |
| N066 | N015, N018, N063, N256 | Checked `ThreeSumCycle` family, empty/ground/closure lemmas, and a binary quotient matroid candidate with the correct ground. The two-way cycle correspondence and proper 3-sum existence remain open. Residual cost 4.0→6.0. | `UNRESOLVED` |
| N055 | N047, N051, N052 | `External.binary_real_projective_uniqueness` matches Oxley Proposition 6.6.5; `Regular.real_representations_projectivelyEquivalent` specializes it, and `Regular.exists_tu_projectivelyEquivalent` adds the N052 TU representation. | `CITED_ASSUMPTION`; TU conclusion depends on N052 and N055 |

The initial N107→N066 proposal was invalid because N107's defining minimum needs the N032 separation theorem; the missing N032→N107 edge was added and all depths recomputed before proof work. Focused and full Lean builds passed. `CurrentBatchAxiomAudit.lean` exposes `sorryAx` on the N055 citation and its dependents, and none on N066's partial lemmas. N055 adds one conditionally available requirement; N116 becomes eligible. The scheduler now selects N146→N186 (score 4.660), with N147/N188 only predicted to become eligible after that future batch.

## Completed short batch: N138 → N139

| ID | Direct prerequisites | Result | Trust |
| --- | --- | --- | --- |
| N138 | N002, N065 | `External.regularTwoSum_isBase_iff` matches Oxley, *Matroid Theory* (2nd ed.), Proposition 7.1.13(ii), the 2-sum definition, and Proposition 7.1.20 on original labels. The earlier first-port independence proof remains kernel-checked. | `CITED_ASSUMPTION` |
| N139 | N122, N138 | `weightedBasesIn_twoSum`, `weightedBasesOut_twoSum`, `weightedBasisRatio_twoSum`: both basis-sum equations, finite positive `P₀/P₁`, extended ratio, nonzero-mass and loop/coloop conventions. | `CONDITIONAL_PROOF` via N138 only |

`TwoSumAxiomAudit.lean` records the precise transitive `sorryAx`. Target-level and full builds passed. The graph gained no edge and no depth changed. N140, N141, N150, N153, N154, N212, N213, and N215 became eligible only after the trust-status updates; the scheduler now reports 40 eligible unresolved nodes.

## Historical corrected depth-7 frontier (2026-10-13)

The completed rows are N018, N034, N106, N144, N149, N162, N163, N170, N175, and N244. Their exact declarations and source correspondence are in `DEPTH7_AUDIT.md`. The remaining requirements are:

| ID | Requirement | Direct prerequisites | Current blocker |
| --- | --- | --- | --- |
| N055 | Projective uniqueness of regular matroids | N047, N051, N052 | Projective uniqueness needs exact literature/signature match and proof routes. |
| N059 | Regular free quotient form | N020, N049, N051, N052, N056, N057 | Both directions of the regular free quotient theorem; N052 would make forward proof conditional. |
| N068 | Two-sum preserves regularity | N051, N065 | Regularity of N065 proper 2-sum over all fields. |
| N118 | Signed circuit dependency | N015, N052 | TU signed circuit dependency with target normalization. |
| N138 | Proper 2-sum basis correspondence | N002, N065 | Both directions of exactly-one-port basis correspondence. |
| N146 | Two-sum target-circuit gluing | N015, N065 | Classify target circuits from N065 cycle unions. |
| N152 | Recover parent across a two-element circuit | N015, N025, N065 | Explicit relabeling for two-circuit child. |
| N161 | Triangle five-sum identity | N051, N125, N266 | Five-class triangle identity including zero classes. |
| N169 | R10 circuit counts | N015, N070 | Certified counts of 4- and 6-circuits. |
| N172 | R10 single deletion | N024, N061, N070 | Labeled graphic K3,3 deletion isomorphism. |
| N173 | R10 single contraction | N025, N062, N070 | Labeled cographic K3,3 contraction isomorphism. |
| N182 | R10 total basis count | N002, N070 | Compact kernel-checked 162-base count and computable-index/base bridge; `#eval` alone is insufficient. |
| N185 | R10 automorphism order | N070 | Complete automorphism order 720 certificate. |
| N186 | R10 element transitivity | N070 | Certified automorphism transitivity. |
| N193 | R10 pointed determinant | N070, N122, N125 | Exact pointed determinant polynomial. |
| N194 | R10 pointed cofactor | N070, N122, N125 | Exact pointed cofactor polynomial. |
| N195 | Pointed R10 target circuits | N070, N081 | Six matching plus nine row-column minimal supports. |
| N204 | Parallel target construction | N021, N065 | Parallel target/glue labels and target-preservation statement design. |
| N225 | R10 nongraphic/noncographic status | N061, N062, N070 | Both nongraphic and noncographic proofs. |
| N238 | Pointed R10 closure balance | N007, N070 | Certified 256/256 target closure split. |
| N239 | Pointed R10 sensitivity witnesses | N007, N070 | Two labeled five-sensitive witnesses. |
| N255 | R10 connectedness | N015, N070 | Source provenance and R10 connectedness/common-circuit certificate. |
| N267 | Weighted K4 triangle signature | N061, N266 | Five weighted K4 closure-class sums. |

N182 was evaluated from N070's exact integer matrix and returned 162, but two `decide` routes exhausted kernel heartbeats; it remains unresolved. No new `sorry`, `admit`, or `axiom` was introduced. `PROOF_BUDGET.md` records observed cycles and unknown time/token data. N218 and the downstream nodes shifted by the new edge are outside this pass.

## Prior depth-1 baseline

N061 is `COMPLETE`. `Matroid.graphic` has ground set exactly `G.edgeSet`, and `Matroid.graphic_indep_iff` characterizes its independent sets as subsets with no edge closing a finite walk through the other selected edges. The formal graph-cycle criterion includes loops and parallel-edge cycles. The proof derives the graph cut criterion from reachability and constructs the matroid through closure exchange. Provenance: `def:graphic-cographic`.

Depth 0 and depth 1 were clear at the start of the depth-2 pass. The following table is the pre-pass state left by the earlier N061-only task.

## Pre-pass minimum unresolved depth: 2

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

## Pre-pass active-node counts by structural depth

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

## Active depth-2 target snapshot

Verified mechanically from the canonical ledger and direct-edge CSV before depth-2 proof work. Depths 0 and 1 have no unresolved active requirement. This set is frozen for this pass; newly exposed depth-3 nodes are excluded.

| ID | Name | Direct prerequisites | Manuscript provenance | Initial status |
| --- | --- | --- | --- | --- |
| N024 | Deletion | N023 | `def:matroid-minors` | `IDENTIFIED` |
| N036 | Single-element extension | N023 | `def:single-element-extension` | `IDENTIFIED` |
| N046 | Represented circuits | N015, N043 | S: `prop:represented-minors`, `prop:span-program-matroid-shadow`, `prop:matroid-program-to-linear-span-program`, `prop:support-linear-characterization`, `thm:quotient-normal-form-correct` | `IDENTIFIED` |
| N047 | Projective equivalence | N042 | `def:projective-equivalence` | `IDENTIFIED` |
| N051 | Regularity | N042 | `def:regular-matroid` | `IDENTIFIED` |
| N056 | TU pivot and standard form | N042 | S: `thm:regular-quotient-form`, `thm:regular-support-bound`, `thm:regular-matroid-energy` | `IDENTIFIED` |
| N057 | TU identity augmentation | N042 | S: `thm:regular-quotient-form` | `STATEMENT_DESIGN` |
| N062 | Cographic matroid | N001, N061 | `def:graphic-cographic` | `IDENTIFIED` |
| N111 | Nonzero column rescaling | N043 | S: `prop:representation-scaling`, `prop:representation-coordinate-invariance`, `prop:regular-representations-are-weights` | `IDENTIFIED` |
| N112 | Ambient linear isomorphism | N043 | S: `prop:representation-scaling`, `prop:representation-coordinate-invariance`, `prop:regular-representations-are-weights` | `IDENTIFIED` |
| N130 | Corank-one uniform target circuit | N015, N129 | S: `prop:grover-source-value`, `prop:grover-program-value`, `lem:r10-targeted-query-matroid` | `IDENTIFIED` |
| N258 | Incidence representation of a graphic matroid | N043, N061 | S: `sec:introduction`, `sec:discussion`, `prop:r10-regular-route-b` | `IDENTIFIED` |

## Initial depth-2 pass audit

Recomputed mechanically from the final `LEDGER.md` and unchanged direct-edge DAG into `DEPTHS.csv`. No new mathematical prerequisite or direct dependency edge was discovered. The frozen 12-target snapshot remains above.

- **Depth-2 targets completed (10):** N024, N036, N046, N047, N051, N057, N062, N111, N112, N130.
- **Depth-2 targets unresolved (2):** N056 (`BLOCKED_PROOF`: TU basis-pivot minor identity and standard-form normalization); N258 (`BLOCKED_PROOF`: signed incidence linear independence iff the N061 forest criterion).
- **New prerequisites discovered:** none.
- **Minimum unresolved structural depth:** 2.

| Depth | Active | Complete | Unresolved |
| ---: | ---: | ---: | ---: |
| 0 | 1 | 1 | 0 |
| 1 | 9 | 9 | 0 |
| 2 | 19 | 17 | 2 |
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

**Total:** 196 active, 41 complete, 155 unresolved. Depth 0 and depth 1 remain clear; depth 2 is incomplete. The unresolved depth-3 layer was not formalized.

## Dedicated N056/N258 attack audit

Recomputed from the final ledger and unchanged direct-edge DAG. N258 is now `COMPLETE`: `Graph.incidence_vectorMatroid_eq_graphic` proves the incidence representation, and companion theorems prove `Represents` and orientation independence. N056 remains `BLOCKED_PROOF`: the normalized matrix is `[I D]` and the row operation preserves the indexed column matroid, but TU preservation reduces to proving TU of `D` by the generalized pivot-minor determinant identity. No new direct prerequisite was found.

- **Depth-2 targets completed:** 11 of the frozen 12, including N258.
- **Depth-2 targets unresolved:** N056 only.
- **Minimum unresolved structural depth:** 2.

| Depth | Active | Complete | Unresolved |
| ---: | ---: | ---: | ---: |
| 0 | 1 | 1 | 0 |
| 1 | 9 | 9 | 0 |
| 2 | 19 | 18 | 1 |
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

**Total:** 196 active, 42 complete, 154 unresolved. Depth 0 and depth 1 remain clear; depth 2 remains incomplete solely because of N056. No depth-3 formalization was performed.

## N056 continuation audit

N056 is now `COMPLETE`. `Matrix.IsTotallyUnimodular.basisStandardForm` packages the identity basis block, total unimodularity of the nonbasis block, and preservation of the indexed column matroid. Its TU proof uses a block determinant and the unit-row TU theorem. No direct edge changed. The depth table was recomputed from the ledger and direct-edge DAG; all recorded structural depths agree.

- **Depths 0 and 1:** clear.
- **Depth 2:** 19 active, 19 complete, 0 unresolved.
- **Minimum unresolved structural depth:** 3.
- **Total:** 196 active, 43 complete, 153 unresolved.

The N056/N258 audit above records the prior state. No depth-3 formalization was performed in this continuation.

## Active depth-3 target snapshot

After correcting N105 to require `A ⊆ M.E \ {τ}`, `lake build` passes. Structural depths recomputed from the direct-edge DAG agree with `DEPTHS.csv`: depths 0, 1, and 2 are entirely `COMPLETE`; depth 3 has 12 active nodes, of which N006 is already complete.

The frozen unresolved depth-3 set is N005, N027, N048, N052, N053, N064, N070, N125, N135, N181, and N256. No depth-4 target is included in this pass.

## End-of-pass depth-3 audit

The N105 interface now requires `A ⊆ M.E \ {τ}` and the full build passed after that repair. All active nodes at depths 0–2 remain `COMPLETE`. The initial depth-3 target snapshot above is retained as a historical record.

During the depth-3 attempt, manuscript and proof analysis exposed five missing direct edges: N044→N053, N044→N070, N053→N070, N044→N125, and N053→N052. The edge evidence and rationale are in `DEPENDENCY_EDGES.csv` and `FORMALIZATION_LOG.md`. N044 is the existing represented-rank requirement; no new ledger ID was needed. Recomputing the DAG moves N053 and N125 to depth 5 and N052 and N070 to depth 6. Their partial implementations and precise remaining obligations are recorded in the log. No depth-4 target was attacked.

The current active depth-3 layer is N005, N006, N027, N048, N064, N135, N181, and N256. The first seven are `COMPLETE`; N256 remains `BLOCKED_PROOF`. Its `F₂` representability step is checked, but the finite binary cycle-space theorem needed to identify disjoint circuit unions with zero column sums has not been proved. The requested symmetric-difference closure therefore remains open. The minimum unresolved structural depth is **3**.

| Depth | Active | Complete | Unresolved |
| ---: | ---: | ---: | ---: |
| 0 | 1 | 1 | 0 |
| 1 | 9 | 9 | 0 |
| 2 | 19 | 19 | 0 |
| 3 | 8 | 7 | 1 |
| 4 | 6 | 2 | 4 |
| 5 | 24 | 10 | 14 |
| 6 | 24 | 1 | 23 |
| 7 | 33 | 0 | 33 |
| 8 | 30 | 0 | 30 |
| 9 | 28 | 0 | 28 |
| 10 | 10 | 0 | 10 |
| 11 | 3 | 0 | 3 |
| 12 | 1 | 0 | 1 |

**Total:** 196 active, 49 complete, 147 unresolved. This audit is based on the recomputed `DEPTHS.csv`; depth 3 is not yet clear.

## N256 continuation audit

`Matroid.isCircuitUnion_iff_binary_sum_eq_zero` proves the finite binary cycle-space characterization, and `Matroid.Regular.isCircuitUnion_symmDiff` closes N256 for the manuscript's finite regular matroids. The full project builds. No direct dependency edge or ledger ID changed in this continuation. `DEPTHS.csv` was regenerated from the canonical ledger and direct-edge DAG.

**The active Matroid formalization is complete through topological depth 3.** All eight active depth-3 nodes (N005, N006, N027, N048, N064, N135, N181, N256) are `COMPLETE`. The minimum unresolved structural depth is **4**. The unresolved depth-4 frontier is N044 (represented rank), N067 (one-sum preserves regularity), N136 (direct-sum bases), and N176 (planar graphic-cographic correspondence). This continuation did not attack any depth-4 node.

| Depth | Active | Complete | Unresolved |
| ---: | ---: | ---: | ---: |
| 0 | 1 | 1 | 0 |
| 1 | 9 | 9 | 0 |
| 2 | 19 | 19 | 0 |
| 3 | 8 | 8 | 0 |
| 4 | 6 | 2 | 4 |
| 5 | 24 | 10 | 14 |
| 6 | 24 | 1 | 23 |
| 7 | 33 | 0 | 33 |
| 8 | 30 | 0 | 30 |
| 9 | 28 | 0 | 28 |
| 10 | 10 | 0 | 10 |
| 11 | 3 | 0 | 3 |
| 12 | 1 | 0 | 1 |

**Total:** 196 active, 50 complete, 146 unresolved.

## Depth-3 correspondence cleanup audit

N048 now has manuscript-facing `Matroid.Represents.restrict` and `Matroid.Represents.delete` bridges for an arbitrary representation of a finite matroid, via `Matroid.Represents.eq_vectorMatroid`. N005's stale `prop:r10-proper-minors` use location was removed from the canonical ledger after checking the manuscript proof. `lake build` passes.

The ledger, unchanged direct-edge DAG, and `DEPTHS.csv` agree: depths 0–3 remain entirely `COMPLETE` (1, 9, 19, and 8 active nodes respectively). The minimum unresolved structural depth remains **4**. No depth-4 target was attacked in this cleanup.

## Active depth-4 target snapshot

Preflight `lake build` passed. `DEPTHS.csv` records all active nodes at depths 0–3 as `COMPLETE` (1, 9, 19, and 8 respectively). The N048 arbitrary-`Represents` restriction/deletion bridge and corrected N005 provenance are present. The frozen unresolved depth-4 working set is N044, N067, N136, and N176; N007 and N025 are already complete. No depth-5 node belongs to this pass.

## Depth-4 attempt and prerequisite audit

The four frozen targets were attempted. N044, N067, and N136 are `COMPLETE`, each with a manuscript-facing Lean theorem and a successful `lake build`. N176 has a checked conditional bridge: a cycle-bond dual pair of finite labeled multigraphs gives both graphic-cographic matroid equalities. The plane-embedding-to-dual cycle-bond theorem itself remains open. It is now N268, split from N176/M120, with a direct N268→N176 proof edge evidenced by `prop:r10-proper-minors`. The pinned library lacks a compatible plane embedding and dual graph construction. `DEPTHS.csv` was regenerated from the ledger and direct edges; existing node depths did not change. N268 has depth 0 because the geometric graph theorem has no matroid prerequisite. No depth-5 work was performed.

| Depth | Active | Complete | Unresolved |
| ---: | ---: | ---: | ---: |
| 0 | 2 | 1 | 1 (N268) |
| 1 | 9 | 9 | 0 |
| 2 | 19 | 19 | 0 |
| 3 | 8 | 8 | 0 |
| 4 | 6 | 5 | 1 (N176) |
| 5 | 24 | 10 | 14 |
| 6 | 24 | 1 | 23 |
| 7 | 33 | 0 | 33 |
| 8 | 30 | 0 | 30 |
| 9 | 28 | 0 | 28 |
| 10 | 10 | 0 | 10 |
| 11 | 3 | 0 | 3 |
| 12 | 1 | 0 | 1 |

**Current active total:** 197 nodes, 53 complete, 144 unresolved. The minimum unresolved structural depth is **0** (N268); at the original depth-4 layer, N176 remains open. Depth 5 is outside this pass.

### N176 continuation

`Matroid/PlanarDuality.lean` now has an independent geometric `Graph.IsPlanar` predicate: actual edge labels have crossing-free continuous paths in `ℝ × ℝ`, including loops and parallel edges. Faces are connected components of the drawing complement. Edge deletion preserves this planarity; for finite graphs the drawn support is closed and the face region open. A graph on the complementary faces can be formed from proposed edge-face incidences with the same edge labels. The checked `CycleBondDuality.of_cycles_iff_bonds` reduces the needed geometric theorem to one cycle-to-bond equivalence; matroid duality supplies the reverse direction. The proposition `PlaneEmbedding.HasCycleBondFaceDual` states the still-unproved N268 step. Pinned mathlib has no Jordan-curve or compatible planar-dual theorem to establish the edge-side assignment and that equivalence. `lake build` passed; N268 remains blocked at depth 0 and N176 remains missing that prerequisite at depth 4. No depth-5 work was undertaken.

The next N176 continuation strengthened the geometric side of that interface: the chosen faces must now approach interior points of their edges. For finite drawings, checked lemmas identify faces with complement path components and prove each face region open. The missing N268 theorem is precisely existence of actual incident faces plus primal-cycle/dual-bond equivalence from plane separation. Its depth and blocked status, and N176's depth-4 status, remain unchanged; no depth-5 work was done.

The N268 continuation reduced the proposed face graph's cuts to boundaries of partitions of actual complementary faces. Checked Lean theorems identify its bonds with minimal nonempty face boundaries and prove that, for a finite drawing, `HasCycleBondFaceDual` is equivalent to the existence of incident face assignments for which primal minimal cycles are exactly those boundaries. This exposes the remaining local arc-side and embedded-cycle separation theorem without graph-cut bookkeeping. Pinned mathlib supplies neither a compatible Jordan curve theorem nor the needed local side theorem, so N268 remains `BLOCKED_MATHLIB_INFRASTRUCTURE` at depth 0 and N176 remains `MISSING_PREREQUISITE` at depth 4. No depth-5 work was undertaken.

The next N268 attack proved a local isolation theorem for finite vertex and edge sets. At every edge interior point, every open interval of path parameters containing that point has an open plane neighborhood in which all drawn points lie on the corresponding subarc. The proof also establishes unique edge/parameter preimages at interior points, including loops. This removes interference from other edges, vertices, and remote parts of the same edge before a local separation argument. The missing theorem must still produce incident complementary faces and prove that their minimal boundaries are exactly the primal cycles. N268 and N176 retain their blocked statuses; no depth-5 node was attempted.

The following N268 pass checked a conditional existence theorem for one incident face per edge. Face regions cover the complement; if individual edge paths have dense complement, the finite drawing has dense complement; if there are finitely many faces, every plane point lies in the closure of one face region. These hypotheses have not been proved from `PlaneEmbedding`. Establishing empty interior of arbitrary embedded edge paths, finiteness of faces, their two local sides, and cycle separation remains necessary for N268. N268 is still blocked at depth 0 and N176 still awaits it at depth 4; no depth-5 work was attempted.

The next N268 pass proved an exact finite combinatorial decomposition of the remaining cycle–boundary theorem. For a fixed assignment of incident faces, primal cycles are exactly minimal nonempty face boundaries if and only if every primal cycle is some face boundary and every nonempty face boundary contains a primal cycle. `hasCycleBondFaceDual_iff_geometric_conditions` combines this with the existing checked duality bridge. The open work is now the geometric incident-face assignment and those two separation claims. An attempted local proof that embedded arcs have empty interior needs punctured-disk connectivity and an arc cut-point argument; no direct theorem for arbitrary continuous embedded arcs was found in pinned mathlib. N268 remains blocked and N176 remains dependent on it; depth 5 was not attacked.

The next N268 continuation proved that every finite plane drawing has a unique unbounded complementary face. The drawing's support is compact; mathlib's path-connected sphere theorem and a checked radial path proof make the exterior of a sufficiently large disk path connected. The result supplies a face from the actual geometry without any finiteness assumption on the face set. The unresolved work is still local edge-side incidence and the two cycle/face-boundary separation claims. N268 remains `BLOCKED_MATHLIB_INFRASTRUCTURE` and N176 remains `MISSING_PREREQUISITE`; depth 5 was not attacked.

The latest N268 continuation constructed the map from complementary faces of a plane drawing to those after edge deletion. The deleted drawing has smaller support, so each old face lies in one new face; unbounded old faces remain unbounded, and incidence with a surviving edge is preserved. For finite drawings with dense original complement, this map is surjective because every new face region is open and meets the old complement. Density is still conditional on the unproved empty-interior theorem for embedded edge paths. The map does not establish how many faces merge when an edge is removed, nor the local two sides or cycle-separation theorem. N268 remains `BLOCKED_MATHLIB_INFRASTRUCTURE` at depth 0 and N176 remains `MISSING_PREREQUISITE` at depth 4. No depth-5 node was attempted.

Oxley, *Matroid Theory*, Proposition 5.2.1 supplies an exact published baseline for the matroid correspondence: a geometric dual has the dual cycle matroid. Its connected-case proof, Lemma 2.3.7, invokes Jordan-curve separation; the proposition then handles disconnected graphs by direct sums. This confirms N268 as standard mathematics while pinpointing the formal gap between the project's raw `PlaneEmbedding` and an edge-corresponding geometric dual. The manuscript's local Oxley citation in `prop:r10-proper-minors` covers the two displayed minor identities, so the ledger's `EXTERNAL_CITED` provenance for the later planar-duality sentence is flagged for review in `FORMALIZATION_LOG.md`. Statuses are unchanged; no depth-5 work was attempted.

The latest N268 pass pins and builds `jordan_pick`, then checks the coordinate bridge to its Jordan separation and whole-component-boundary theorems. A simple closed path with only its endpoints identified now has a checked sphere trace. Every loop edge of `PlaneEmbedding` satisfies that condition and has a two-component complement; every nonloop edge is an arc with connected complement. These results use the existing labeled multigraph model. The general `IsGraphCycle` predicate is still a minimal edge set, with no checked extraction of an ordered simple cyclic path. Moreover, Jordan separation of a cycle support alone does not assign the incident faces of the full drawing or prove cycle/minimal-face-boundary equivalence. A separate formal crosscut source was inspected but is pinned to Lean 4.32.2 and not integrated. N268 remains unresolved at depth 0, N176 remains dependent at depth 4, and `DEPTHS.csv` statuses are unchanged. See `SOURCES.md` and the latest `FORMALIZATION_LOG.md` entry. No depth-5 node was attempted.

The next N268 pass established a continuous closed path with image exactly equal to the drawn support of **every** `IsGraphCycle`, using the actual edge labels and a minimality argument on the traversed reachable edges. It also proved those connecting edges are inclusion-minimal, and closed the Jordan-trace bridge for all one-edge loop cycles. The remaining nonloop bridge is a simple labeled walk extraction: the constructed path may backtrack, so it has not been proved injective modulo its endpoints. Face assignment and cycle/face-boundary correspondence remain open after that. The full `lake build` passes; N268 and N176 retain their unresolved statuses, and depth 5 was not attempted.

The latest N268 continuation completed the general graph-cycle-to-Jordan bridge. A minimal connecting edge set now yields a vertex-simple walk with the original edge labels, whose drawn path is injective; a fresh closing edge gives a simple closed path, including parallel-edge cycles. Every `IsGraphCycle` therefore has an exact-support Jordan trace, and its support has two complementary components with the imported whole-boundary theorem available. A map now sends each face of the full drawing to a side of any selected cycle. The still-open step is to show that full-drawing edge-incident faces occupy the required local sides and that minimal face boundaries coincide with primal cycles. N268 remains unresolved at depth 0, N176 remains dependent at depth 4, and `DEPTHS.csv` is unchanged. No depth-5 work was attempted.

The next N268 pass proves a conditional full-face incidence result. If the full drawing's complement is dense and its face type finite, every cycle edge has two distinct incident faces, one mapped to each Jordan side. This uses the checked whole-boundary theorem for the cycle and a finite-face closure argument. The unproved density and finite-face facts remain necessary, as do side assignments for bridge edges and the exact cycle/minimal-face-boundary correspondence. An inspected crosscut development assumes polygonal crosscuts and arc collars, so it does not directly cover the arbitrary continuous edge paths in `PlaneEmbedding`. N268 remains unresolved at depth 0 and N176 at depth 4; no depth-5 work was attempted.

The latest N268 pass proves that every finite plane drawing has dense complement. For nonloop edges, a hypothetical open disk in the drawn arc would embed a circle into an interval; a checked antipodal/connectedness argument rules that out. Loop-edge density follows from the imported Jordan whole-boundary theorem. Consequently, face maps after edge deletion and onto either side of a graph cycle are surjective without a density hypothesis. Every minimal-cycle edge has two incident full-drawing faces on opposite Jordan sides when the full face type is finite. Face finiteness, incident faces for bridge edges, and the two cycle/minimal-face-boundary implications remain open. An additional `schoenflies-lean` audit found a proved face-cycle theorem, but it assumes a finite two-connected polygonal loopless drawing and does not identify this project's original faces. N268 and N176 remain unresolved; no depth-5 work was attempted.

## N268 / N176 audit after relative Schoenflies integration

The pinned Jordan dependency and the pinned, adapted Schoenflies import closure both build with Lean/mathlib 4.35.0-rc3. Every labeled graph cycle has an exact-support Jordan trace. The relative Schoenflies bridge now moves the whole drawing to standardize a selected cycle, and checked ambient transport identifies all original full-drawing faces, their regions, edge incidence, and minimal face boundaries. At a selected edge's interior point, a checked open neighborhood excludes the other finite support. These bridges preserve loops, parallel edges, and edge labels.

The remaining obligation is to construct a complete incident-face assignment and prove the two geometric face-boundary clauses. The audited crosscut API requires polygonality and collars; the graph face-cycle API requires polygonality, two-connectedness, and loopless drawings. The polygonal redrawing theorem supplies no original-face correspondence or ambient homeomorphism. See [N268_BLOCKER.md](N268_BLOCKER.md) for the exact hypotheses, missing conclusions, and separate downstream-certificate fallback assessment.

The canonical ledger now records both claims as `EXTERNAL_UNCITED_STANDARD`. N268 is `BLOCKED_PROOF` at depth 0; N176 is `MISSING_PREREQUISITE` at depth 4. The unchanged direct-edge DAG and regenerated `DEPTHS.csv` give 197 active nodes, 53 complete, and 144 unresolved. At depths 1–3 all 9, 19, and 8 active nodes remain complete; at depth 4, 5 of 6 remain complete. N268/N176 are the only unresolved active requirements through depth 4. The active formalization is not complete through topological depth 4. No depth-5 or downstream application proof was begun. Full `lake build` passes (9119 jobs).

## N268 frontier after complete cycle-edge incidence

Relative Schoenflies now sends a chosen cycle point to the midpoint of a square side. In a small ball there, the full drawing equals the selected cycle and its complement is two convex half-balls. The checked `graphCycle_local_faces` identifies their actual full-drawing faces, excludes any third incident face locally, and proves the two faces occupy opposite Jordan sides. `graphCycle_edge_incidence_all_interior` makes that pair consistent along the whole edge. Thus `graphCycle_edge_has_complete_incidentFaces` holds for every cycle edge, including loops and parallel-edge cycles, without a finite-face assumption.

The checked `graphCycles_are_faceBoundaries_of_complete_incidence_no_faceFinite` now supplies the cycle-boundary direction from complete incidence. `hasCycleBondFaceDual_of_complete_incidence_and_forestBoundary` reduces N268 to two supplied geometric inputs: extend complete incidence to edges lying in no cycle, and prove that a face-partition boundary that is a primal forest is empty. The edgewise result when every edge belongs to a cycle discharges only the first input for that subcase. Neither input is silently assumed for the general drawing. See [N268_BLOCKER.md](N268_BLOCKER.md).

Full `lake build` passes (9120 jobs); the new declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. The ledger/DAG depth calculation was revalidated with unchanged statuses: N268 remains `BLOCKED_PROOF` at depth 0, and N176 remains `MISSING_PREREQUISITE` at depth 4. Active totals remain 197 nodes / 53 complete. The active formalization is not yet complete through topological depth 4. No depth-5 work was begun.

## N268 frontier after complete all-edge incidence

`Matroid/Internal/EdgeLocalSides.lean` now constructs complete incident-face pairs for every edge of a finite drawing, including bridge edges, with no containing-cycle or finite-face hypothesis. The imported accessibility and arc-joining theorems close a nonloop subarc into an auxiliary Jordan curve; compactness excludes the added arc locally, and relative Schoenflies models the actual drawing by a line. Loop edges reuse the existing cycle result. Incidence is constant along each entire edge interior, and `exists_incidence_with_cycle_boundaries` supplies both a complete assignment and every exact primal cycle boundary.

`Matroid/Internal/ForestBoundary.lean` proves that any nonempty face-partition boundary separates the complement of its own retained edge support plus the original vertices. Its `hasCycleBondFaceDual_of_forest_complement` leaves one explicit sufficient input: the complement of every retained finite embedded forest is preconnected. The audited isolated-arc theorem does not cover arbitrary finite branching or disjoint unions of trees. The additional inspected finite-complex PL approximation theorem supplies no ambient homeomorphism or original-face connectivity transport and was not imported. See [N268_BLOCKER.md](N268_BLOCKER.md) and [SOURCES.md](SOURCES.md) for the exact statement and source audit.

Full `lake build` passes (9122 jobs). Axiom audits of the new imports and local bridges report only `propext`, `Classical.choice`, and `Quot.sound`. N268 remains `BLOCKED_PROOF` at depth 0; N176 remains `MISSING_PREREQUISITE` at depth 4. The ledger/DAG calculation was revalidated with 197 active nodes / 53 complete and unchanged statuses and depths. The active formalization is not yet complete through topological depth 4. No depth-5 work was begun.

## Prior N268 frontier after the cycle-to-bond direction

`Matroid/Internal/ArcBoundary.lean` proves that a nonempty face boundary cannot fit inside a simple drawn arc, even with all original vertices retained. Every proper edge subset of a primal cycle fits inside a proper arc of its Jordan trace by imported `JordanCurve.Arcs.exists_proper_arc`. Consequently every primal cycle is a minimal actual face boundary and a bond of the constructed incidence graph. `exists_incidence_with_cycle_bonds` supplies a complete assignment with the unconditional cycle-to-bond direction, including loop and parallel-edge cycles.

The same module proves that finitely many original vertex points do not affect connectivity outside a selected edge support, using the imported ball homeomorphism and connected punctured plane. The remaining sufficient input is therefore connectivity of `(P.edgeSupport D)ᶜ` for every primal forest `D`; no isolated-vertex input remains. The converse dual-bond-to-primal-cycle direction still needs exclusion of arbitrary forest boundaries, which may branch or have multiple components. The leaf-endpoint bypass needed for an alternative induction is not supplied by the audited global arc-complement theorem. See [N268_BLOCKER.md](N268_BLOCKER.md).

Full `lake build` passes (9123 jobs). All 13 audited imported and local declarations use only `propext`, `Classical.choice`, and `Quot.sound`. N268 remains `BLOCKED_PROOF`; N176 remains `MISSING_PREREQUISITE`. Active totals remain 197 nodes / 53 complete, and all statuses, structural depths, and dependency edges are unchanged. The active formalization is not yet complete through topological depth 4. No depth-5 work was begun.

## N268 / N176 completion — 2026-10-10

`PlaneEmbedding.hasCycleBondFaceDual` now constructs the dual on the original drawing’s faces. The existing cycle/Jordan/Schoenflies/incidence reductions are retained. The final forest bridge uses graph-cut potentials to make covering-space lifts agree at vertices, then Tietze extension and the imported disk no-retraction theorem to rule out bounded complementary components. The imported connected disk exterior identifies all remaining components. No polygonal redrawing, matroidal definition of planarity, or special-case substitution is used.

`PlaneEmbedding.matroid_correspondence` and `IsPlanar.matroid_correspondence` discharge N176 in both directions on the original edge labels. Full `lake build` passes after N268 and again after N176 (9125 jobs). All 12 audited imported/local declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

The unchanged direct-edge DAG and regenerated `DEPTHS.csv` contain **197 active nodes, 55 complete, 142 unresolved**. All active nodes at depths 0–4 are complete: 2, 9, 19, 8, and 6 nodes respectively.

The active Matroid formalization is complete through topological depth 4.

## Next frontier: depth 5 (identified only)

There are 24 active depth-5 nodes: 10 already complete and the following 14 unresolved. No depth-5 proof was begun. Existing statuses are retained.

| ID | Name | Status |
| --- | --- | --- |
| N026 | Minor | `IDENTIFIED` |
| N028 | Contraction composition | `IDENTIFIED` |
| N029 | Deletion-contraction commutation | `IDENTIFIED` |
| N041 | Closure under extension restriction | `IDENTIFIED` |
| N045 | Represented closure | `IDENTIFIED` |
| N049 | Represented contraction | `IDENTIFIED` |
| N053 | TU representation over every field | `MISSING_PREREQUISITE` |
| N125 | TU weighted basis determinant | `MISSING_PREREQUISITE` |
| N131 | Rank-one uniform target closure | `IDENTIFIED` |
| N134 | Deletion-contraction duality | `IDENTIFIED` |
| N137 | One-sum target ratio | `IDENTIFIED` |
| N143 | Negative restriction coloop | `IDENTIFIED` |
| N262 | Row-restriction matroid equivalence | `IDENTIFIED` |
| N264 | Graphic target-edge closure | `IDENTIFIED` |

## Frozen depth-5 pass — 2026-10-11

The active direct-edge DAG was recomputed before any depth-5 proof: 197 active nodes, no unresolved node at depths 0–4, and exactly the following 14 unresolved nodes at depth 5. This table preserves their **initial** statuses. The proof classification is recorded separately in `PROOF_STATUS.csv`.

| ID | Direct active prerequisites | Mathematical source | Initial status | Depth | Final trust status |
| --- | --- | --- | --- | ---: | --- |
| N026 | N024, N025 | MANUSCRIPT_DEFINITION | IDENTIFIED | 5 | KERNEL_PROVED |
| N028 | N025 | EXTERNAL_UNCITED_STANDARD | IDENTIFIED | 5 | KERNEL_PROVED |
| N029 | N024, N025 | EXTERNAL_UNCITED_STANDARD | IDENTIFIED | 5 | KERNEL_PROVED |
| N041 | N006, N007, N036 | EXTERNAL_UNCITED_STANDARD | IDENTIFIED | 5 | KERNEL_PROVED |
| N045 | N007, N043, N044 | EXTERNAL_UNCITED_STANDARD | IDENTIFIED | 5 | KERNEL_PROVED |
| N049 | N025, N043 | MANUSCRIPT_PROVED | IDENTIFIED | 5 | KERNEL_PROVED |
| N053 | N042, N044, N051 | EXTERNAL_UNCITED_STANDARD | MISSING_PREREQUISITE | 5 | UNRESOLVED |
| N125 | N042, N044, N122 | EXTERNAL_CITED | MISSING_PREREQUISITE | 5 | UNRESOLVED |
| N131 | N007, N129 | EXTERNAL_UNCITED_STANDARD | IDENTIFIED | 5 | KERNEL_PROVED |
| N134 | N024, N025, N132 | EXTERNAL_UNCITED_STANDARD | IDENTIFIED | 5 | KERNEL_PROVED |
| N137 | N122, N136 | MANUSCRIPT_PROVED | IDENTIFIED | 5 | UNRESOLVED |
| N143 | N007, N022, N023 | MANUSCRIPT_PROVED | IDENTIFIED | 5 | KERNEL_PROVED |
| N262 | N043, N044 | EXTERNAL_UNCITED_STANDARD | IDENTIFIED | 5 | UNRESOLVED |
| N264 | N007, N061 | EXTERNAL_UNCITED_STANDARD | IDENTIFIED | 5 | KERNEL_PROVED |

The ledger has `COMPLETE` only for the ten kernel proofs. N053 and N125 retain `MISSING_PREREQUISITE`; N137 and N262 retain `IDENTIFIED`. There are no `CITED_ASSUMPTION` or `CONDITIONAL_PROOF` rows and no admitted external declarations. No DAG edge was changed. `DEPTHS.csv` was regenerated from the same direct-edge DAG and the updated ledger: 65 of 197 active nodes are complete.

**Unconditional kernel-certified depth: 4. Citation-relative completed depth: 4.** The two figures agree because this pass introduced no cited assumptions. The next mathematical frontier remains N053, N125, N137, and N262 at depth 5. Their precise proof obligations and resource records are in `FORMALIZATION_LOG.md` and `PROOF_BUDGET.md`. Depth 6 was not attempted.

Final full `lake build` passed (9125 jobs). `#print axioms` for each new depth-5 theorem and the unchanged N268/N176 declarations listed only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` appeared. The Lean-source scan found no admitted declarations, and the ledger/DAG/status consistency check passed.

## Depth-5 continuation audit — 2026-10-11

The four rows left open by the preceding historical snapshot are now kernel proved. Their final signatures and audit are in `Depth5AxiomAudit.lean`; `PROOF_BUDGET.md` records observed and unknown resource use.

| ID | Final Lean declaration | Trust status |
| --- | --- | --- |
| N137 | `Matroid.weightedBasisRatio_oneSum`, with separate `weightedBasesIn_oneSum` and `weightedBasesOut_oneSum` | `KERNEL_PROVED` |
| N262 | `Matroid.rowCompression_after_columnRestriction` | `KERNEL_PROVED` |
| N053 | `Matroid.vectorMatroid_realTU_represents_over_field` | `KERNEL_PROVED` |
| N125 | `Matroid.weightedGram_det_eq_weightedBasesTotal_of_tu` | `KERNEL_PROVED` |

The active direct-edge DAG is unchanged. `DEPTHS.csv` was recomputed from all 197 active ledger rows and `DEPENDENCY_EDGES.csv`; every stored depth and direct-prerequisite list agreed with the graph. There are now **69/197** active `COMPLETE` nodes, and depth 5 has **24/24 complete**. All layers 0–5 are complete. Depth 6 contains 24 active nodes, of which one was already complete; no depth-6 proof was attempted.

**Unconditional kernel-certified depth: 5. Citation-relative completed depth: 5.** There are no cited assumptions or conditional proofs in this continuation. The final `lake build` passed (9131 jobs), and the committed audit source printed only `propext`, `Classical.choice`, and `Quot.sound` for all four interfaces and their new premises. The Lean-source declaration scan found no `sorry` or `admit`; no direct dependency edge was changed.

## Corrected depth-6 pass — 2026-10-11

Before freezing the pass, the manuscript's converse of `thm:regular-quotient-form` was checked against the DAG. It chooses a TU representation of an arbitrary regular matroid, so N052 is a direct prerequisite of N059. The evidenced `N052 → N059` edge was added and longest-path depths recomputed: N059 moved 6→7 and N060 moved 7→8. All other active depths stayed fixed. N059 was excluded from this pass and no depth-7 proof was started.

The corrected layer consists of N081 (previously complete) and the 22 rows audited individually in `DEPTH6_AUDIT.md`. Sixteen formerly open rows now have complete axiom-clean Lean declarations: N013, N014, N017, N030, N033, N050, N054, N097, N109, N214, N243, N246, N247, N248, N257, and N266. N070 gained exact rank-five proofs but is not complete. There are no cited assumptions or conditional proofs.

| Remaining depth-6 ID | Exact blocker | Next proof step |
| --- | --- | --- |
| N052 | Regular⇒existence of a labeled real TU coordinate matrix is absent from pinned mathlib and local Lean. Oxley Lemma 4.4 confirms the finite theorem but not a project signature bridge. | State and attempt the narrow labeled converse; preserve arbitrary-field `Regular` and exact ground labels. |
| N065 | No complete labeled proper 2-sum construction with cycle symmetric differences. | Formalize the Oxley circuit construction, prove the cycle equivalence, and retain the manuscript's nonloop/noncoloop and size conditions. |
| N070 | The displayed 5×10 matrix is proved rank five; a kernel-checked TU certificate is missing. | Use canonical minor indexing or a compact auditable finite checker, then apply N053. |
| N174 | No labeled multigraph edge-contraction/graphic-matroid correspondence, including loops and parallel edges. | Build graph edge contraction and prove deletion/contraction matroid identities. |
| N175 | Cographic minor closure needs the labeled N174 bridge. | Dualize the completed N174 identities using existing local matroid duality. |
| N207 | The six-path graph and its target-reachability calculation have not been formalized. | Define its 18 response edges and target edge, apply N264, and prove the row/column and nine-minimal-support equivalences. |

Recomputed active counts by depth are 0: 2/2, 1: 9/9, 2: 19/19, 3: 8/8, 4: 6/6, 5: 24/24, 6: 17/23, where each pair is complete/total. Overall, 85/197 active nodes are kernel-complete. The minimum unresolved depth is 6. Both unconditional kernel-certified depth and citation-relative completed depth are 5. This pass stopped at the depth-6 frontier.

## Depth-6 continuation checkpoint — 2026-10-12

The entry `lake build` and `git diff --check` passed. The direct edge N174→N175 was added because the stated cographic-minor route dualizes N174's graphic-minor theorem. A longest-path DAG recomputation moves only N175 from depth 6 to 7; no depth-7 mathematical work was done.

| ID | Depth | Direct active prerequisites | Current trust | Exact result / remaining work |
| --- | ---: | --- | --- | --- |
| N207 | 6 | N061, N264 | `KERNEL_PROVED` | `DoubleStar.target_mem_graphic_closure_iff`, `minimal_accepting_iff`: exact 19 graph edges, nine shared query labels, nine minimal supports of size five. |
| N070 | 6 | N043, N044, N051, N053 | `KERNEL_PROVED` | 252 canonical minors of the nonbasis block; `r10IntegerMatrix_isTotallyUnimodular`, `r10_regular`. |
| N174 | 6 | N026, N061 | `KERNEL_PROVED` | Labeled graph deletion/contraction and `IsGraphic.minor`, including loops and parallel edges. |
| N065 | 6 | N021, N022, N063, N256 | `KERNEL_PROVED` | `regularTwoSum_ground` and `regularTwoSum_isCircuitUnion_iff` under all properness hypotheses. N068 regularity preservation remains a separate depth-7 requirement. |
| N052 | 6 | N051, N053 | `CITED_ASSUMPTION` | `External.regular_ground_exists_realTU` (Oxley Lemma 4.4) is the sole admission; `Regular.hasLabeledRealTU` proves ambient-label transport but is conditional. A local proof of the TU sign normalization would remove `sorryAx`. |
| N175 | 7 | N026, N062, N174 | `UNRESOLVED`, outside this pass | Cographic minor closure is now a depth-7 task by the evidenced direct edge. |

The active total is **89/197 kernel-complete**. At depth 6, **21/22** nodes are kernel-complete and **22/22** are complete relative to the cited Tutte premise. All earlier certified depths remain complete. The minimum kernel-unresolved depth is 6; the minimum citation-relative unresolved depth is 7. `PROOF_STATUS.csv` and `DEPTH6_AUDIT.md` give the per-target trust and signature audit.

## Current scheduler frontier — 2026-10-19 five-batch closeout

The current strict scheduler recomputes **197 active nodes**, **452 direct active edges**, **121 available** (including **9 directly cited assumptions**), **76 unresolved**, and **43 eligible unresolved**. Structural depths remain audit metadata; no edge or depth changed in these five batches. N200, N035, and N196 are newly kernel proved; N037 is source-verified and cited. N066, N185, N226, and N267 retain their unresolved statuses and documented partial Lean work. Full `lake build` passed (9192 jobs), eight scheduler tests passed, and the tracked axiom audit distinguishes ordinary axioms from the N037 and inherited N146 `sorryAx` premises. The clean, no-deferral recommendation in `NEXT_BATCH.md` is **N066→N159**, score **4.091**; N159 remains blocked until N066 is actually completed. The older depth snapshots above remain historical, not current execution orders.

## Automated scheduler five-batch closeout — 2026-10-19

Five consecutive strict-scheduler selections were attempted: N066→N159, N185→N187, N226→N161, N133→N148, and N227→N201. N133 and N201 are newly `KERNEL_PROVED`; N148 is available as a source-verified `CITED_ASSUMPTION`. N066, N185, N226, N161, and N227 remain unresolved with checked partial proofs and factual residual-cost revisions. N159/N187 were not attempted because their first-task prerequisites did not become available. No direct edge or structural depth changed; completion-state changes are synchronized between `LEDGER.md` and `DEPTHS.csv`.

The clean strict scheduler now reports **197 active nodes**, **452 active direct edges**, **124 available** (including **10 directly cited assumptions**), **73 unresolved**, and **42 eligible unresolved**. All run-local deferrals were cleared. Its reproducible next recommendation in `NEXT_BATCH.md` is **N066→N159**, score **4.396**. The source and full-hypothesis comparison for each attempted task is in `CURRENT_FIVE_BATCH_AUDIT.md`; transitive axioms are tracked in `NextFiveBatchAxiomAudit.lean`. The full `lake build` passed (9197 jobs), eight scheduler tests passed, and `git diff --check` passed. Per-node time/tokens were unavailable and remain `UNKNOWN`.

## Persistent-cooldown scheduler closeout — 2026-10-19

The strict scheduler selected five more consecutive batches, indexed 21–25: N227→N153, N182→N193, N183→N194, N184→N226, and N161→N059. N153, N182, N183, N184, and N193 are newly `KERNEL_PROVED`. N194, N226, N161, and N059 gained checked partial Lean results but remain unresolved; N227's checked one-stage route still needs the active-port invariant. The exact manuscript correspondence and remaining obligations for all ten selections are recorded in `PERSISTENT_FIVE_BATCH_AUDIT.md`. No new citation or direct DAG edge was added, and all structural depths remain valid.

The append-only `SCHEDULER_ATTEMPTS.csv` now derives persistent cooldowns across scheduler restarts. At the next attempted index 26, N059, N066, N161, N185, N226, and N227 are cooling; N194's run-local deferral has cleared. The clean strict snapshot reports **197 active nodes**, **452 direct active edges**, **129 available** (including **10 directly cited assumptions**), **68 unresolved**, **40 mathematically eligible unresolved**, and **34 ordinarily selectable**. The next automatically selected batch is **N188→N152**, score **2.397**. No incomplete node was counted as available. The full build, scheduler tests, and transitive axiom results are recorded in `FORMALIZATION_LOG.md`.
