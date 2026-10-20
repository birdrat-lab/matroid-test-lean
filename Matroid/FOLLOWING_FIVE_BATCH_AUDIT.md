# Scheduler batches 26–30: manuscript and trust audit

Checked against `Manuscript/main.tex` on 2026-10-20. The selected sequences and
their scores were N188→N152 (2.397), N066→N159 (4.396), N071→N179 (4.012),
N185→N187 (3.938), and N227→N154 (2.866). The second task of batch 29 was
skipped because its direct prerequisite N185 stayed unresolved. No task ID was
manually substituted. `SCHEDULER_ATTEMPTS.csv` events 46–54 contain one event
per substantive attempt; no WAKE event was justified. The active direct-edge
count stayed 452 and no depth changed.

| ID | Exact source correspondence and public Lean declaration | Trust and remaining obligation |
| --- | --- | --- |
| N188 | `prop:r10-symmetry`, equation `eq:r10-P01-equivariance`: `r10_pointed_basis_polynomials_equivariant` reindexes both pointed basis sums for every R10 automorphism, target, and pushed-forward weight, over any commutative semiring. It does not claim the separate order-720 clause. | `KERNEL_PROVED`; none. |
| N152 | The two-element-circuit reduction in the proof of `prop:recursive-r10-closure`: `twoSumWithPair_eq_mapEquiv_swap` gives equality of the labeled binary cycle-glued matroid with the parent under the port/leaf swap. The proper two-sum size condition is inapplicable to a two-element child, so the proof uses N065's unrestricted binary cycle construction. | `KERNEL_PROVED`; none. |
| N066 | `def:regular-matroid-sums`, proper 3-sum: `ThreeSumCycle.candidate_isCircuitUnion`, its converse, and `exists_properThreeSum` provide the finite regular-side, common three-element coindependent circuit, size-at-least-seven, ground symmetric-difference, and exact cycle-family witness. Regularity preservation of the new matroid remains separately tracked as N069. | `KERNEL_PROVED`; none for N066. |
| N159 | The proof of `lem:seymour-three-sum-five` requires compatibility of the five closure classes, then the weighted linearity theorem. `External.properThreeSum_isBase_iff` states the verified Bérczi–Mátravölgyi–Schwarcz Section 2 deletion/contraction and augmented-basis three-family formula with original labels. It does not identify those families with the manuscript's five `closure S ∩ T` classes. | `UNRESOLVED`; helper is `CITED_ASSUMPTION`. The closure-class translation and N160 weighted bilinear result remain open. |
| N071 | `def:seymour-decomposition`: `SeymourDecomposition` represents rooted binary 1/2/3-sum trees, finite regular node matroids, and graphic/cographic/embedded-R10 leaves. The existence theorem `thm:seymour-decomposition` is separately N072. | `KERNEL_PROVED`; none. |
| N179 | First assertion of `prop:r10-no-three-sum`: `IsR10Copy.circuit_card_ne_three` and both `not_properThreeSum_*` declarations exclude an intact, relabeled R10 leaf from either proper three-sum child slot using N170's no-triangle property. The target-component 2-sum consequence is separately N180. | `KERNEL_PROVED`; none. |
| N185 | `prop:r10-symmetry` order-720 clause: `r10FourDependencyCert_count` checks only that there are 15 four-column dependencies. The five-set basis bridge exhausted 1,000,000 Lean heartbeats after about 84 seconds and was removed from the compiling module. | `UNRESOLVED`; exact 720 automorphism certificate still needed. N187 stabilizer order 72 was not attempted. |
| N227 | `prop:recursive-r10-natural-cost` target-cocircuit part: `r10TargetSixCocircuit_nonTarget_card` gives five active root ports in each displayed cocircuit; `r10TargetSixCocircuit_activePort_bound` gives the `5*l` union bound when those five ports each carry a child support of size at most `l`. | `UNRESOLVED`; nine-stage support transport, arbitrary-depth induction, and attainment still needed. The earlier one-stage lemma has a cited N148 dependency; the new counting lemmas are unconditional. |
| N154 | Monotonicity prose after `eq:two-sum-homogeneity`: `regularEffectiveWeight_mono_of_positive` establishes nondecreasing `P₀/P₁` for an increasing positive non-target weight in a finite regular pointed matroid, with target and updated label on the ground, distinctness, nonloop target, and positive other weights. Four-class affine expansions and the ratio inequality are Lean proved. | `CONDITIONAL_PROOF`; `sorryAx` is transitive only through exact Choe–Wagner regular Rayleigh premise `External.regular_rayleigh_pair`. |

The exact external statement comparisons and locations are recorded in
`SOURCES.md`. The tracked `FollowingFiveBatchAxiomAudit.lean` prints ordinary
`propext`, `Classical.choice`, and `Quot.sound` for completed unconditional
declarations and the N185/N227 partials. It prints `sorryAx` for the N159
external helper, the N154 external premise, and N154's dependent public
declarations. No N159, N185, N187, or N227 manuscript claim was admitted.

Focused builds passed for each batch. The final `lake build` passed (9214
jobs), as did `lake env lean Matroid/FollowingFiveBatchAxiomAudit.lean`, 15
scheduler tests, strict scheduler validation, and `git diff --check`.
Per-node total time and tokens remain `UNKNOWN`; the N185 direct checker is
the only specific observed duration in this run. Remaining-cost revisions,
separate from cooldowns, are in `SCHEDULER_ESTIMATES.csv` and `PROOF_BUDGET.md`.

After clearing run-local deferrals, the canonical scheduler has 197 active
nodes, 452 direct edges, 135 available (10 directly cited), 62 unresolved,
and 43 eligible unresolved at attempted batch index 31. Persistent cooldowns
are N161 until batch 36, N185 until batch 45, N226 until batch 35, and N227
until batch 41; N059's prior cooldown has expired. The next automatically
selected sequence is **N159→N059** (score 2.905). Its predicted newly
eligible N060 and N160 remain unavailable until those prerequisites close.
