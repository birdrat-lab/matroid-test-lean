# Cumulative depth-5 external-theorem proof budget

Checkpoint: 2026-10-11. Verified elapsed time and per-theorem token counts were unavailable, so both are `UNKNOWN`; no elapsed or token total is inferred. Counts below are substantive edit–check cycles observed in this pass. Earlier N053/N125 reconnaissance is retained in `FORMALIZATION_LOG.md`; its time and cycle counts were not recorded, so cumulative counts cannot be reconstructed. No theorem has been admitted.

| ID | Source / first recorded attempt | Verified cumulative time | Observed tokens | Attempts / cycles observed this pass | Proved intermediates | Precise remaining goal | Disposition |
| --- | --- | --- | --- | --- | --- | --- | --- |
| N028 | Standard minor algebra; 2026-10-11 | UNKNOWN | UNKNOWN | 1 / 1 | `Matroid.contract_contract` bridge | None | KERNEL_PROVED |
| N029 | Standard minor algebra; 2026-10-11 | UNKNOWN | UNKNOWN | 1 / 1 | Disjoint `contract_delete_comm` bridge | None | KERNEL_PROVED |
| N041 | Standard restriction rank/closure; 2026-10-11 | UNKNOWN | UNKNOWN | 1 / 2 | Exact extension closure and rank theorem | None | KERNEL_PROVED |
| N045 | Standard vector-matroid closure; 2026-10-11 | UNKNOWN | UNKNOWN | 1 / 1 | Indexed span test for arbitrary represented finite matroid | None | KERNEL_PROVED |
| N053 | Manuscript regularity remark; first attempt date UNKNOWN (earlier depth-3 reconnaissance) | UNKNOWN | UNKNOWN | Prior attempt at least 1, this pass reconnaissance / 0 cycles | Integer TU minor nonvanishing bridge, including characteristic 2 | Prove indexed column independence iff some square minor is nonzero for an arbitrary rectangular matrix; transfer that criterion to every field, including the integer lift of a real TU matrix. | UNRESOLVED; no admission |
| N125 | Choe–Oxley–Sokal–Wagner, Theorem 8.1/Corollary 8.2; first attempt date UNKNOWN (earlier depth-3 reconnaissance) | UNKNOWN | UNKNOWN | Prior attempt at least 1, this pass reconnaissance / 0 cycles | TU nonzero minor square equals 1 | Formalize rectangular weighted Cauchy–Binet with finite subset indexing, then identify exactly the full-rank subsets with matroid bases and filter the TU squared minors. | UNRESOLVED; no admission |
| N131 | Standard rank-one uniform matroid; 2026-10-11 | UNKNOWN | UNKNOWN | 1 / 1 | Nonloop target and closure for every nonempty other set | None | KERNEL_PROVED |
| N134 | Standard matroid duality; 2026-10-11 | UNKNOWN | UNKNOWN | 1 / 1 | Both dual deletion/contraction identities | None | KERNEL_PROVED |
| N262 | Standard linear row-space compression; 2026-10-11 | UNKNOWN | UNKNOWN | Reconnaissance / 0 cycles | Existing represented-rank theorem N044 | State an exact restricted matrix compression that simultaneously preserves the indexed column matroid and both directions of every target reconstruction equation; a rank-only row-deletion lemma is insufficient. | UNRESOLVED; no admission |
| N264 | Standard graphic closure/path criterion; 2026-10-11 | UNKNOWN | UNKNOWN | 1 / 2 | Labeled cut/reachability characterization, including loops | None | KERNEL_PROVED |

The unresolved external results remain within the policy budget. Their missing proof routes were identified without introducing an admission. A future pass must continue these records rather than resetting them.

## Depth-5 continuation checkpoint — 2026-10-11

At entry, the workspace had uncommitted, compiling proof files for all four targets and one provisional `sorry` in `External/WeightedCauchyBinet.lean`. The ledger still reported 65/197 complete. The authorship, elapsed time, and edit/check counts of that pre-entry work are `UNKNOWN`; they are not charged as observed cycles below. The full entry `lake build` passed, but the admitted declaration prevented an axiom-clean entry checkpoint. The observed whole-turn clock interval was 21:40:51–21:49:41 UTC; per-node start/end times and token deltas were not exposed and remain `UNKNOWN`. The table counts material theorem/lemma additions followed by Lean feedback during this continuation; small syntax/debug corrections are not counted as separate substantive cycles.

| ID | Manuscript use and exact source | Route / observed cycles | Newly checked proof artifacts | Remaining goal; decision |
| --- | --- | --- | --- | --- |
| N137 | `prop:seymour-one-sum`, both factorization equations and extended ratio; manuscript-local, no admissible citation | Existing uncommitted factorization route at entry; 1 new substantive edit/check group (explicit loop zero lemma). Per-node time/tokens `UNKNOWN`. | `weightedBasesIn_oneSum`, `weightedBasesOut_oneSum`, `weightedBasesTotal_pos`, `weightedBasisSums_nonzero`, `weightedBasesIn_eq_zero_of_isLoop`, and `weightedBasisRatio_oneSum`; source `WeightedBases.lean`, `Sums.lean`, `OneSumWeights.lean`. | None. `KERNEL_PROVED`; no admission. |
| N262 | Restricted-column row deletion in `thm:regular-matroid-energy`; no external citation needed for the completed local proof | Existing uncommitted row-factorization route at entry; 0 new substantive edit/check groups, one axiom audit. Per-node time/tokens `UNKNOWN`. | `exists_rowCompression_factor`, `rowCompression_reconstruction_iff`, `rowCompression_weightedReconstruction_iff`, `rowCompression_vectorMatroid_eq`, `rowCompression_after_columnRestriction`. | None. `KERNEL_PROVED`; the exact target equation is preserved in both directions. |
| N053 | Remark after `def:regular-matroid`; Oxley, *Matroid Theory* (2nd ed.), §6.6 for TU field transfer; rectangular minor criterion proved locally | Existing uncommitted rectangular-minor route at entry; 2 new substantive edit/check groups (real integral lift, field-facing corollary). Per-node time/tokens `UNKNOWN`. | `linearIndependent_cols_iff_exists_minor_det_ne_zero`, `linearIndependent_intCast_iff`, `vectorMatroid_intCast_eq_of_totallyUnimodular`, `IsTotallyUnimodular.exists_intCast_eq`, `vectorMatroid_realTU_represents_over_field`. | None. `KERNEL_PROVED`, all characteristics, original labels. |
| N125 | Weighted basis determinant in `thm:regular-matroid-energy`; Choe–Oxley–Sokal–Wagner (2004), §8.1 Theorem 8.1(b), Corollary 8.2(b), footnote 12 | Finite ordered-column expansion and image/permutation grouping; 7 substantive lemma/theorem addition and Lean-check groups after entry. Per-node time/tokens `UNKNOWN`. This exceeds the requested six-group new-pass allowance by one; the seventh group closed the identity, so no further proof route was started. | `weightedGram_det_sum_injective`, `weightedGram_permutation_fiber`, `orderedColumnIndex_injective`, `orderedColumnIndex_image`, `exists_orderedColumnIndex_comp_perm`, `sum_injective_eq_sum_ordered_permutations`, `weightedCauchyBinet`, and `weightedGram_det_eq_weightedBasesTotal_of_tu`. | None. `KERNEL_PROVED`; the provisional `sorry` was replaced by a theorem application, with no cited assumption. |

The historical time/token entries and lower bounds above remain unchanged. The final proof has no admitted premise, so the external admission gate was not used. The full build and all four target-facing `#print axioms` checks report no `sorryAx`.

## Corrected depth-6 pass — 2026-10-11 (America/Detroit)

The whole-pass start was observed at 22:14:01 UTC on 2026-10-11. Per-node start/end times and token deltas were not exposed; all are `UNKNOWN`. A later whole-pass clock observation is recorded in the final log, but it is not assigned to individual theorems. A shared module edit/check group can advance several rows, so the table does not invent separate per-node cycles. `0` means source/API reconnaissance only. The N070 finite `decide` route was one substantive route with two configuration checks (heartbeat and recursion limits), not three mathematical cycles. The historical depth-5 external-theorem budgets above remain cumulative and untouched. No external theorem was admitted.

| ID | Manuscript use; source | Route and observed new-pass cycles | Checked artifact / exact remaining goal | Decision |
| --- | --- | --- | --- | --- |
| N013 | `def:matroid-flat` rank test; pinned matroid closure/rank API | Flat/rank bridge; one shared basic-lemma edit/check group | `isFlat_iff_forall_eRk_lt_insert`; none | KERNEL_PROVED |
| N014 | `def:matroid-flat` basis clause; pinned `IsBase.closure_of_superset` | Same shared basic-lemma group | `IsFlat.eq_ground_of_isBase_subset`; none | KERNEL_PROVED |
| N017 | `def:hyperplane-cocircuit`; manuscript definition | Same shared basic-lemma group | `IsHyperplane`; none | KERNEL_PROVED |
| N030 | Contracted spanned element; pinned `contract_isLoop_iff_mem_closure` | Same shared basic-lemma group | `isLoop_contract_of_mem_closure`; none | KERNEL_PROVED |
| N033 | `def:modular-pair`; manuscript definition | Same shared basic-lemma group | `IsModularPair`; none | KERNEL_PROVED |
| N050 | `prop:functional-zero-flat`; N045 span/closure | Same shared basic-lemma group | `Represents.isFlat_functional_zero`; none | KERNEL_PROVED |
| N052 | Tutte regular⇒TU converse after `def:regular-matroid`; Oxley, *Briefly, What Is a Matroid?*, Lemma 4.4 | Literature and pinned-mathlib reconnaissance; 0 substantive edit/check cycles | N053 already gives TU⇒regular. Need exact labeled finite real-coordinate TU existence and bridge from project's all-fields `Regular` predicate. | UNRESOLVED; no admission; cumulative earlier converse effort UNKNOWN |
| N054 | `prop:regular-basic-properties` minor closure; N048/N049 represented minors | Same shared basic-lemma group | `Regular.delete`, `Regular.contract_any`; none | KERNEL_PROVED |
| N065 | `def:regular-matroid-sums` proper 2-sum; Oxley, *Briefly, What Is a Matroid?*, Theorem 5.1 gives a circuit description | Manuscript/source/API reconnaissance; 0 substantive edit/check cycles | Construct labeled proper 2-sum with cycle symmetric differences, prove matroid existence and regularity. The cited theorem's circuit form still needs a cycle bridge. | UNRESOLVED; manuscript definition cannot be admitted |
| N070 | `def:r10` displayed rank-five regular matrix; same Oxley source, pp. 11–12, displays the matrix as TU | Rank route plus generic finite-TU `decide` route; 2 substantive proof/check groups observed. The latter hit heartbeat, then recursion limit, then a 45-second timeout after raising limits. | `r10Matrix_rank`, `r10_eRank`; produce a small kernel-checked TU minor certificate and derive regularity via N053. | UNRESOLVED; no admission |
| N097 | Flat-lattice join; pinned closure API | Shared basic-lemma group | `flat_join_isFlat`, `flat_join_upper`, `flat_join_least`; none | KERNEL_PROVED |
| N109 | Positive half of `prop:support-linear-characterization`; N045 | One shared support-lemma edit/check group | `positiveSpanningSupport_eq_reconstruction`; none | KERNEL_PROVED |
| N174 | Graphic minor closure; no exact labeled multigraph contraction source verified | Graph API reconnaissance; 0 substantive edit/check cycles | Define edge contraction retaining loops/parallel labels and prove graphic-matroid correspondence. | UNRESOLVED; no admission |
| N175 | Cographic minor closure; N174 and local duality | Duality/API reconnaissance; 0 substantive edit/check cycles | Derive cographic deletion/contraction from a completed labeled N174 bridge. | UNRESOLVED; no admission |
| N207 | `sec:r10-pointed` six-path graphic double star; N264 reachability | Manuscript/local API reconnaissance; 0 substantive edit/check cycles | Define exact 18-edge labeled graph and show its target path iff a full row and column; derive nine minimal sets. | UNRESOLVED; manuscript proof cannot be admitted |
| N214 | `eq:seymour-two-sum-P` loop/coloop convention; N122 | One shared ratio-lemma edit/check group | `twoSumPortRatio_eq_top_of_isLoop`, `twoSumPortRatio_eq_zero_of_isColoop`; none | KERNEL_PROVED |
| N243 | `prop:relation-fundamental-circuits` free-basis clause | One shared quotient-lemma edit/check group | `freeRelation_generators_isBase`; none | KERNEL_PROVED |
| N246 | `prop:quotient-normal-form-contraction`; N049 | Same shared quotient-lemma group | `freeRelation_contract_eq_quotient`; none | KERNEL_PROVED |
| N247 | `thm:quotient-normal-form-correct` positive matroid implication | Same shared quotient-lemma group | `freeRelation_positive_closure_of_equation`; none | KERNEL_PROVED |
| N248 | Same theorem, negative matroid implication | Same shared quotient-lemma group | `freeRelation_negative_nonclosure`; none | KERNEL_PROVED |
| N257 | Rank-one uniform regularity; N053 | One shared one-row-TU edit/check group | `uniformOn_one_regular`; none | KERNEL_PROVED |
| N266 | `eq:seymour-three-sum-phi` and five entries; N158 | One triangle-signature edit/check group, followed by a substantive correction of the three `p_i` indices to singleton closure classes | `weightedTrianglePhi`, `weightedTriangleSignature`, `weightedTrianglePhi_eq_zero_of_not_five`; none | KERNEL_PROVED |

All still-open external results are below their reliably observed cumulative 12-cycle ceiling. The source match for N052 supports only a future narrowly scoped external premise after serious proof work and an exact signature match; it does not itself authorize an admission. The six open targets and next proof steps are detailed in `DEPTH6_AUDIT.md`.

## Depth-6 continuation checkpoint — 2026-10-12

The entry build and diff check passed. Per-node start/end times, token deltas, and a complete count of material edit/check cycles were not exposed; these remain `UNKNOWN`. The lower bounds below count only distinguishable substantive proof groups retained in the continuation trace. They are **not** claimed as exact cycle totals. Previous-pass observations above remain cumulative: N070 had two recorded groups; the other five targets had reconnaissance only. The only admitted premise is the precisely sourced N052 converse described below. No manuscript-facing declaration contains an admission.

| ID | Manuscript use and source | Route; reliably observed new groups | Checked result or exact residual goal | Status and decision |
| --- | --- | --- | --- | --- |
| N207 | `sec:r10-pointed` double-star query example; manuscript-local | Exact labeled graph, reachability, and minimal-support routes; **at least 3** material groups. Time/tokens `UNKNOWN`. | `DoubleStar.target_mem_graphic_closure_iff`, `minimal_accepting_iff`, `support_injective`, `support_ncard`; no residual goal. | `KERNEL_PROVED`; no admission. |
| N070 | `def:r10` 5×10 regular matrix; manuscript-local | Finite canonical-minor certificate, arbitrary-index bridge, identity-block reduction; **at least 3** new groups, plus 2 recorded in previous pass. Time/tokens `UNKNOWN`. | `r10NonbasisBlock_isTotallyUnimodular`, `r10IntegerMatrix_isTotallyUnimodular`, `r10_regular`; no residual goal. | `KERNEL_PROVED`; 252 canonical square minors checked by kernel `decide`. |
| N174 | Graphic minor closure on original multigraph edge labels; no external source needed | Labeled contraction and reachability, graphic-matroid equalities, minor composition; **at least 3** new groups. Time/tokens `UNKNOWN`. | `Graph.reachableOn_contractEdge_iff`, `graphic_deleteEdges_eq_delete`, `graphic_contractEdge_eq_contract`, `IsGraphic.minor`; no residual goal. | `KERNEL_PROVED`; no admission. |
| N052 | Tutte converse after `def:regular-matroid`; Oxley, *Briefly, What Is a Matroid?*, Definition 4.3/Lemma 4.4, printed p. 10 | Route A: finite real coordinate representation on original labels. Route B: binary/ternary representations and TU sign-compatibility search. Narrow cited ground-indexed premise plus formal ambient-label transport after the two routes failed to yield TU signs; **at least 4** new material groups. Time/tokens `UNKNOWN`. | `HasLabeledRealTU.regular`, `RepresentableOver.exists_labeled_matrix`, `Regular.exists_labeled_binary_ternary_matrices`, `Regular.hasLabeledRealTU`; exact remaining *unconditional* goal is proof of `External.regular_ground_exists_realTU` without `sorry`. | `CITED_ASSUMPTION`; sole admission in `External/TutteRegularTU.lean`, downstream converse conditional. Two distinct focused routes justified stopping before the six-group reassessment ceiling. |
| N065 | `def:regular-matroid-sums` proper 2-sum and **cycle** formula; manuscript-local | Matching-cycle closure, binary quotient construction, both directions of cycle correspondence, proper interface; **at least 8** distinguishable material groups. Time/tokens `UNKNOWN`. | `TwoSumCycle.candidate_isCircuitUnion`, `TwoSumCycle.of_candidate_isCircuitUnion`, `exists_twoSum_of_regular`, `regularTwoSum_isCircuitUnion_iff`; no residual goal. | `KERNEL_PROVED`; no admission. Regularity preservation is separately N068 at depth 7. |
| N175 | Cographic minor closure; proposed proof directly uses N174 | Dependency repair only; **0** proof groups. Time/tokens `UNKNOWN`. | Direct edge N174→N175 moves the node to depth 7; exact goal remains cographic minor closure. | `UNRESOLVED`; outside this pass. |

The N052 admission asserts only the source's finite regular-matroid-to-real-TU representation on the **ground subtype**; its extension to ambient labels is locally proved. The source does not assert the Lean label transport. `#print axioms` finds `sorryAx` in that premise and `Regular.hasLabeledRealTU`, and none in N065, N070, N174, or N207. The cumulative external budget cannot be reconstructed from unknown historical time/tokens or uncounted edit groups; no total is fabricated.

## Depth-7 matroid-first pass — 2026-10-13

Per-target start/end times and token deltas were not observed reliably; all are `UNKNOWN`. The counts below are **observed lower bounds of substantive edit followed by Lean feedback**, not inferred elapsed time. A syntax correction within a route is not counted as a new mathematical route. The existing external budgets, especially N052, are cumulative and are not reset. N218 moved to depth 8 after the evidenced N068→N218 edge and receives no proof cycle here. No new admission was made.

| ID | Exact manuscript use / source | Route and observed new-pass cycles | New declaration or exact residual goal | Status / decision |
| --- | --- | --- | --- | --- |
| N018 | `def:hyperplane-cocircuit`; manuscript definition | Complement-of-hyperplane interface; at least 1 shared proof group | `IsHyperplaneCocircuit`, `isHyperplaneCocircuit_iff`; none | KERNEL_PROVED |
| N034 | `def:modular-cut`; manuscript definition | Abstract flat/modular-pair interface; same shared group | `IsModularCut`; none | KERNEL_PROVED |
| N106 | `prop:positive-support-circuits`; manuscript proof | Closure/circuit and finite minimum; at least 1 group | `positiveSpanningSupport_eq_circuitSupport`; none | KERNEL_PROVED |
| N144 | `prop:seymour-two-sum-input-minors`; manuscript proof | N030 contraction and N214 extended ratio; at least 1 group | `contractedPort_isLoop`, `contractedPort_ratio_eq_top`; none | KERNEL_PROVED |
| N149 | `def:regular-matroid-sums` ground calculation; standard finite-set fact | N065 labeled symmetric-difference ground; at least 1 group | `regularTwoSum_ground_ncard`; none | KERNEL_PROVED |
| N175 | `def:graphic-cographic` minor closure; dual of N174 | Matroid duality and labeled graphic minors; at least 1 group | `IsCographic.minor`; none | KERNEL_PROVED |
| N162 | After `prop:regular-triangle-identity`; manuscript positivity | Coindependent complement basis, positive sum; at least 1 group | `weightedTriangle_a_pos`; none | KERNEL_PROVED |
| N163 | Same passage; manuscript positivity | Triangle-pair basis extension and closure; at least 1 group | `weightedTriangle_c_pos`; none | KERNEL_PROVED |
| N244 | `prop:relation-fundamental-circuits`; manuscript proof | General closure/support, fundamental-circuit support, target specialization; at least 3 material groups | `positiveRelation_fundCircuit`, `positiveRelation_fundCircuit_isCircuit`; none | KERNEL_PROVED |
| N182 | `app:r10-atlas` 162 bases; finite certificate derived from N070 | Whole `decide` and membership-partition `decide` in Lean scratch; 2 observed route groups, 0 retained proof modules | Need a compact kernel-checked 252-minor count and proof that computable column indexing matches `r10.IsBase`. `#eval=162` is not a certificate. | UNRESOLVED; no admission |
| N138 | `thm:seymour-two-sum` basis correspondence; manuscript proof | Abstract N065 cycle/excluded-circuit route; at least 2 material groups (cycle/independence helpers and the first-port independence proof) | `regularTwoSum_indep_of_bases_first_port` proves independence of the union when the first basis uses the port; still need opposite orientation, maximality, and converse exactly-one-port decomposition. | UNRESOLVED; compiling partial theorem, no admission |
| N146 | `prop:recursive-r10-closure` circuit gluing; manuscript proof | N065 minimal-cycle route reconnaissance; 0 proof groups | Extract and classify target circuits from matching cycle unions. | UNRESOLVED |
| N152 | Same recursive proof, two-circuit child; manuscript proof | Matroid relabeling route reconnaissance; 0 proof groups | Construct explicit parent/child matroid isomorphism on retained labels. | UNRESOLVED |
| N204 | `sec:r10-pointed` target-parallel construction; manuscript statement design | Exact label/port audit only; 0 proof groups | Specify parallel extension with distinct old port and new target, then prove target preservation after 2-sum. | UNRESOLVED / STATEMENT_DESIGN |
| N068 | Regularity of proper 2-sum after `def:regular-matroid-sums`; external cited | Abstract regular/2-sum and representation API search; 0 proof groups; precise cited theorem not yet source-matched | Prove regularity of N065 result over every field or isolate exact external premise; N065 supplies only existence/cycles. | UNRESOLVED; no admission |
| N161 | `prop:regular-triangle-identity`; manuscript determinant/Plücker proof | Matroid polynomial candidate and TU bridge reconnaissance; 0 proof groups | Prove `a*c=p₁*p₂+p₁*p₃+p₂*p₃` for all coindependent regular triangles, including zero classes. | UNRESOLVED |
| N267 | `eq:k4-five-sums`; manuscript finite graphic computation | Six-edge K4/N266 finite-predicate plan; 0 proof groups | Construct exact labeled K4 and calculate five closure-class sums. | UNRESOLVED |
| N059 | `thm:regular-quotient-form`; manuscript proof | TU standard-form, kernel, and extension route designed; 0 proof groups | Prove both directions with disjoint finite relation labels, free deletion, regular extension, identity-on-E contraction. | UNRESOLVED; any N052 use would be conditional |
| N055 | `prop:regular-basic-properties`; Brylawski–Lucas (1976), Oxley (2011) cited | Pinned uniqueness API reconnaissance; 0 proof groups; exact citation not checked | Prove span isomorphism and nonzero per-column scalars for all real representations of a regular matroid. | UNRESOLVED; no admission |
| N118 | Paragraph before `thm:regular-support-bound`; Oxley (2011) cited | TU signed-circuit API reconnaissance; 0 proof groups; exact citation not checked | Prove circuit-supported dependence with target coefficient one and all other coefficients `±1`. | UNRESOLVED; no admission |
| N169 | `app:r10-atlas` 4-/6-circuit counts; certificate derived | Common N070 finite-minor oracle designed; 0 proof groups | Prove 15 four-circuits and 15 six-circuits. | UNRESOLVED |
| N170 | `app:r10-atlas` absence of triangles; certificate derived | N070→binary parity route; at least 2 material groups (public circuit-sum wrapper, matrix parity specialization). | `r10_circuit_card_ne_three`; no residual goal. | KERNEL_PROVED; no admission |
| N172,N173 | `prop:r10-proper-minors`; certificate derived | Labeled K3,3 isomorphism route designed; 0 proof groups | Give explicit relabeling with graphic/cographic single-element deletion/contraction. | UNRESOLVED |
| N185,N186 | `prop:r10-symmetry`; certificate derived | Finite basis-preserving permutation route designed; 0 proof groups | Prove automorphism completeness/order 720 and transitivity. | UNRESOLVED |
| N193,N194 | Pointed R10 determinant and cofactor; manuscript proof | Exact N070 matrix and N125 weighted-minor plan; 0 proof groups | Prove both indexed pointed polynomial formulas with exact dimensions. | UNRESOLVED |
| N195 | `lem:r10-minimal-positive`; certificate derived | Target-circuit oracle and K3,3 label route designed; 0 proof groups | Prove exactly six matching and nine row-column minimal supports. | UNRESOLVED |
| N225 | R10 nongraphic/noncographic; manuscript claim | Matroid excluded-minor search planned; 0 proof groups | Prove both negative representability statements for N070 object. | UNRESOLVED |
| N238,N239 | Pointed R10 closure balance and five-sensitive witnesses; certificate derived | 512-input oracle route designed; 0 proof groups | Prove 256/256 split and exhibit/verify two five-sensitive labeled inputs. | UNRESOLVED |
| N255 | R10 connectedness; provenance unresolved | Manuscript-role audit and circuit-oracle plan; 0 proof groups | Establish a precise source-matched connectedness/common-circuit claim for N070. | UNRESOLVED / PROVENANCE_UNRESOLVED |

The N182 scratch attempts are recorded as failed routes, not as a proof artifact. The external N068, N055, and N118 nodes have not exhausted two focused proof routes or obtained checked source/hypothesis matches, so no admission is authorized. Historical unknown time and token entries above remain unknown.

## Dependency-aware N138 → N139 batch — 2026-10-19

Per-node elapsed time and token counts are unavailable and remain `UNKNOWN`. The counts below are observed substantive edit/check groups in this batch, not retroactive estimates of earlier work. The original N138 abstract independence route above remains in place.

| ID | Manuscript/source and route | Observed edit/check groups | Checked artifact and residual goal | Decision |
| --- | --- | ---: | --- | --- |
| N138 | Unlabeled basis step in `thm:seymour-two-sum`; Oxley, *Matroid Theory* (2nd ed.), Proposition 7.1.13(ii), 2-sum definition p. 260, Proposition 7.1.20. Exact hypotheses and labels checked before admission; pinned mathlib 2-sum/connection search was empty. | 2: source/signature audit and isolated premise; local pair-uniqueness proof and check | `External.regularTwoSum_isBase_iff` is the precise cited premise; `regularTwoSum_basisPair_unique` is kernel-proved; earlier `regularTwoSum_indep_of_bases_first_port` preserved. No remaining N138 statement obligation relative to the cited source. | `CITED_ASSUMPTION`; one new `sorryAx` |
| N139 | Manuscript `thm:seymour-two-sum`: finite basis-pair bijection, target partition, product splitting, port substitution, positivity, and extended ratio. | At least 6: bijection/uniqueness check; product/xor sum check; sigma-sector bilinear check; port-update check; positivity/factorization check; ratio/boundary/axiom check. | `weightedBasesIn_twoSum`, `weightedBasesOut_twoSum`, `weightedBasisRatio_twoSum`, `twoSumEffectiveWeight_pos`, `weightedBasisSums_twoSum_nonzero`, and loop/coloop ratio corollaries. No remaining local proof goal. | `CONDITIONAL_PROOF`; only transitive N138 premise |

`lake env lean Matroid/TwoSumWeights.lean`, `lake build Matroid.TwoSumAxiomAudit`, and full `lake build` all passed. The audit prints `sorryAx` for the N138 cited theorem and the N139 factorization/ratio descendants, and no `sorryAx` for basis-pair uniqueness, `P₀/P₁` positivity, or non-simultaneous target mass. No additional citation or admission was introduced for N139. The residual-cost overrides for completed N138/N139 have blank scores; their historical effort is recorded here, and no remaining proof cost is scheduled for this batch.

## Scheduler-directed N066 → N055 batch — 2026-10-19

The entry scheduler scored this sequence 5.215 with residual-cost sum 6.0 after the evidenced N032→N107 dependency repair. Per-node elapsed time and token consumption remain `UNKNOWN`; command wall times are recorded in the log. Counts below are observed substantive edit/check groups in this pass, not a reconstruction of all prior work.

| ID | Manuscript/source and attempted route | Observed edit/check groups | Checked artifact and precise residual goal | Status / remaining cost |
| --- | --- | ---: | --- | --- |
| N066 | `def:regular-matroid-sums`, proper common coindependent three-element circuit, factors of size at least seven; abstract binary cycle matching, then quotient representation candidate | 2: matching-triangle cycle-family lemmas and Lean check; quotient candidate and ground theorem and Lean check | `ThreeSumCycle`, `threeSumCycle_empty`, `ThreeSumCycle.subset_symmDiff_ground`, `ThreeSumCycle.symmDiff`, `binaryThreeSumCandidate`, `binaryThreeSumCandidate_ground`. Still prove both directions of `candidate.IsCircuitUnion X ↔ ThreeSumCycle M N T X` using a finite triangle-span quotient kernel theorem, and package all properness hypotheses into an actual matroid construction. Closure of the proposed family alone does not prove matroid existence. | `UNRESOLVED`; residual ordinal cost raised 4.0→6.0 (medium confidence) from the checked quotient route and missing correspondence theorem. No admission. |
| N055 | `prop:regular-basic-properties`; Oxley 2011 Proposition 6.6.5 and Proposition 6.3.12, with explicit rank-zero discussion | 2: exact source/signature/mathlib audit; isolated citation and local TU specialization with Lean check | `External.binary_real_projective_uniqueness` cited; `Regular.real_representations_projectivelyEquivalent` and `Regular.exists_tu_projectivelyEquivalent` compiled. No residual N055 obligation relative to the verified external theorem. | `CITED_ASSUMPTION`; residual cost cleared. The fixed-TU conclusion also inherits previously cited N052. |

The focused `Matroid.ThreeSum`, `Matroid.External.ProjectiveUniqueness`, `Matroid.ProjectiveUniqueness`, and `Matroid.CurrentBatchAxiomAudit` builds and full `lake build` passed. The full build took 10.44 seconds of observed command wall time; it is **not** charged to either theorem individually. The N066 helpers print only `propext`, `Classical.choice`, and `Quot.sound`. The N055 premise and descendants print `sorryAx`; the TU descendant relies on both the new N055 premise and earlier N052. No N066 construction theorem was admitted or marked available.

## Five-batch invocation, batch 1 — 2026-10-19

| ID | Route and observed edit/check groups | Result and remaining cost |
| --- | --- | --- |
| N146 | One source/signature/mathlib audit, one isolated-citation and target-specialization Lean check | `External.regularTwoSum_isCircuit_iff` cited; `regularTwoSum_targetCircuit_iff` local proof. `CITED_ASSUMPTION`, no scheduled residual cost. Per-node time/tokens `UNKNOWN`. |
| N186 | One source/signature/mathlib audit, one binary-to-real bridge and isolated-citation Lean check | `r10_eq_binary` kernel-proved; `External.binaryR10_element_transitive` cited; `r10_element_transitive` local transport. `CITED_ASSUMPTION`, no scheduled residual cost. Per-node time/tokens `UNKNOWN`. |

Focused builds and `MultiBatchAxiomAudit` passed. New `sorryAx` appears only through the two isolated external premises and their local descendants; the binary bridge is axiom clean. The ledger retains historical unresolved attempts above as chronology.

## Five-batch invocation, batch 2 — 2026-10-19

| ID | Route and observed edit/check groups | Result and remaining cost |
| --- | --- | --- |
| N185 | Two groups: manuscript/provenance and ancillary-file audit; exact indexed automorphism type and identity proof with focused Lean check | `R10Automorphism.lean` compiles and states the exact finite cardinality target. The claimed `anc/r10_atlas/` verifier is absent, so no exhaustive preservation/completeness certificate is available. `UNRESOLVED`; remaining ordinal cost 4.0→6.0 (medium confidence), based on the missing checker and 10-label enumeration bridge, not to manipulate selection. Time/tokens `UNKNOWN`. Deferred only for this invocation. |
| N187 | Recorded prerequisite N185 remains unresolved; no theorem attempt is valid yet. | `UNRESOLVED`; residual cost unchanged at 3.0. |

The selected N185→N187 sequence cannot complete because N187 directly requires N185. No group-order result was admitted or marked available.

## Five-batch invocation, batch 3 — 2026-10-19

| ID | Route and observed edit/check groups | Result and remaining cost |
| --- | --- | --- |
| N161 | Two groups: exact five-class determinant proof audit; algebraic coefficient consequence and focused Lean check | `triangle_identity_of_det_coefficients` is kernel-proved. The bridge from N266's closure-class sums to coefficients of the positive-definite determinant, including Cauchy–Binet and triangle column normalization, is absent. N161 remains `UNRESOLVED`, 4.0→6.0 residual score (medium confidence), deferred for this invocation only. Time/tokens `UNKNOWN`. |
| N068 | Two groups: exact Oxley Corollary 7.1.26 and N065 hypothesis check; isolated premise and focused Lean check | `External.regularTwoSum_regular` compiles, `CITED_ASSUMPTION`; no scheduled residual cost. Time/tokens `UNKNOWN`. |

The selected order was N161→N068. N068 is independently eligible despite the N161 stall. No new direct dependency was needed.


## Five-batch invocation, batch 4 — 2026-10-19

The provisional N218→N195 recommendation was rejected before proof work: the manuscript's recursive proper gluing requires base R10 connectedness N255, absent from N218's direct edges. Added N255→N218 and recomputed all active depths; none changed because both N255 and existing N068 have depth 7. The strict rerun selected N059→N032 (score 3.930, residual sum 7.32).

| ID | Route and observed edit/check groups | Result and remaining cost |
| --- | --- | --- |
| N059 | Two groups: exact theorem and TU construction API audit; checked standard-form kernel-block multiplication | `standardForm_mul_kernelBlock` is kernel-proved. Existing N056/N057 cover pivot and TU augmentation, but no faithful disjoint-label free-extension object or proof that its contraction is the original matroid has been built. The regular converse also needs labeled transport. `UNRESOLVED`; 4.0→6.0 residual score (medium confidence), deferred only this invocation. Time/tokens `UNKNOWN`. |
| N032 | Two groups: manuscript/hypothesis and mathlib API audit; basis-extension proof and focused Lean check | `cocircuit_separates_closure` is kernel-proved for `A⊆E` and `e∈E` explicit. The manuscript's ambient-ground convention implies the latter; without it the statement is false. No residual cost. Time/tokens `UNKNOWN`. |

N032's conclusion uses mathlib's `IsCocircuit`, whose definition is a dual circuit and mathematically equivalent to complement of a hyperplane. The project's N018 predicate records that same complement convention. A tracked axiom print checks the new theorem.


## Five-batch invocation, batch 5 — 2026-10-19

The strict scheduler selected N107→N263 (score 4.790, residual sum 4.2). The N263 proof route needs the separator N032 directly; added N032→N263 before implementation and recalculated all depths. N263 and descendants N196/N201/N227/N229 moved up one depth. Strict validation then retained N107→N263.

| ID | Route and observed edit/check groups | Result and remaining cost |
| --- | --- | --- |
| N107 | Two groups: exact finite pointed support convention and nonempty minimum; Lean definition/spec and N018 cocircuit-interface bridge | `negativeTargetSupport` minimizes `|D|−1` over manuscript hyperplane-complement cocircuits avoiding `A`. `negativeTargetSupport_spec` uses N032 to prove attainment. `KERNEL_PROVED`; no residual cost. Time/tokens `UNKNOWN`. |
| N263 | Three groups: mathlib minimal-nonspanning cocircuit API audit; maximal-flat proof; manuscript N018 cocircuit conclusion and focused build | `maximal_nonspanning_isHyperplane` proves hyperplane, mathlib cocircuit, and target membership; `maximal_nonspanning_isHyperplaneCocircuit` proves the manuscript cocircuit predicate. `KERNEL_PROVED`; no residual cost. Time/tokens `UNKNOWN`. |

The bridge `IsCocircuit.isHyperplaneCocircuit` and N032's manuscript-predicate corollary are kernel-proved. The five selected batches are complete as an invocation checkpoint; N185, N161, and N059 remain unresolved.

## Five-batch invocation closeout — 2026-10-19

Full `lake build` passed (9171 jobs; command wall time 10.21 seconds, shared check rather than a per-node cost). The tracked `MultiBatchAxiomAudit` printed `sorryAx` on precisely the three new source-verified external premises N146/N186/N068 and their expected local descendants; all new N032/N107/N263 declarations and all three partial-proof lemmas printed only ordinary Lean axioms. Eight scheduler tests passed. The strict scheduler with run-local deferrals was rerun after batch 5; it proposed N255→N218. All deferrals were then cleared and the clean strict scheduler again proposed N255→N218. No unresolved result was marked available.

## Current five-batch invocation, batch 1 — 2026-10-19

The clean strict scheduler selected N255→N218 (score 3.782; residual sum 5.5). Both direct prerequisite sets were confirmed in the current DAG. Per-node elapsed time and tokens are `UNKNOWN`.

| ID | Observed route and substantive Lean edit/check groups | Result and residual estimate |
| --- | --- | --- |
| N255 | Four groups: exact manuscript/source and binary representation audit; five then fifteen checked four-column dependencies; proof that R10 has no 1- or 2-element circuit combined with N170's no-triangle theorem; circuit-union minimality and all-pair coverage. | `r10_common_circuit` is `KERNEL_PROVED`; no remaining scheduled cost. The provenance was resolved as `CERTIFICATE_DERIVED` from the exact displayed matrix, without admitting an unsourced external theorem. |
| N218 | Two groups: exact prose and N065/N068/N255 interface audit; indexed recursive-stage predicate, nine disjoint children/ports and sequential proper 2-sums; bridge from the N065 constructor. | `RecursiveR10` and `isProperTwoSum_regularTwoSum` are `KERNEL_PROVED` as the manuscript construction specification; no remaining definition cost. Existence, connectedness, regularity and numerical closure properties remain separate later ledger tasks. |

Focused `lake build Matroid.R10Connected Matroid.RecursiveR10` and `FiveBatchAxiomAudit.lean` passed. The audit printed only ordinary Lean axioms for all N255/N218 declarations. No DAG edge changed.

## Current five-batch invocation, batch 2 — 2026-10-19

The strict rerun selected N195→N147 (score 5.624; residual sum 6.0). They were independently eligible: N195 uses N070/N081, and N147 uses N007/N146. Per-node time and tokens remain `UNKNOWN`.

| ID | Observed route and substantive Lean edit/check groups | Result and residual estimate |
| --- | --- | --- |
| N195 | Five groups: exact source edge-label audit; six four-target and nine six-target binary dependencies; proof that every six-set is a circuit; finite exhaustive target-circuit certificate; graph-label perfect-matching/double-star bridge and N081 closure equivalence. | `r10_minimalTargetSpanning_iff` is `KERNEL_PROVED`; no remaining scheduled cost. The finite `decide` proofs used scoped 16,384 recursion depth and 10,000,000 heartbeat limits but completed in the focused check. |
| N147 | Three groups: statement/hypothesis audit; surviving-ground lemma; full two-direction closure-circuit proof from N146. | `regularTwoSum_target_mem_closure_iff` is `CONDITIONAL_PROOF` on the already verified N146 premise; no remaining local proof cost. No new admission. |

Focused builds for `Matroid.R10TargetCircuits` and `Matroid.TwoSumTargetClosure` passed. The tracked audit printed only ordinary Lean axioms for N195, and `sorryAx` for N147 only through N146. No DAG edge changed.

## Current five-batch invocation, batch 3 — 2026-10-19

Strict scheduling selected N152→N150 (score 5.064; residual sum 4.2). They are independent. Per-node time and tokens remain `UNKNOWN`.

| ID | Observed route and substantive Lean edit/check groups | Result and residual estimate |
| --- | --- | --- |
| N152 | Four groups: exact manuscript reduction/relabel audit; two-element child's unique cycle family; N065 cycle-level port replacement; generic `mapEquiv` circuit bridge. | `UNRESOLVED`, run-locally deferred. The final equivalence between disjoint circuit unions of a matroid and its relabeling, followed by equality of the two matroids, is still required. Residual score 2.0→4.5 (medium confidence) reflects this checked missing bridge, not sunk work. |
| N150 | Two groups: N138 source/hypothesis interface audit; finite basis-cardinality proof and focused check. | `regularTwoSum_eRank_add_one` is `CONDITIONAL_PROOF` on N138's previously cited basis correspondence; no remaining local cost. |

Focused builds and the tracked axiom print passed. N152's partial lemmas have no `sorryAx`; N150 inherits `sorryAx` only from N138. No new direct edge. The next scheduler run uses `--defer-node N152` for this invocation only.

## Current five-batch invocation, batch 4 — 2026-10-19

The strict scheduler with N152 temporarily deferred selected N204→N066 (score 3.792; residual sum 9.2). They are independently eligible. Per-node elapsed time and tokens remain `UNKNOWN`.

| ID | Observed route and substantive Lean edit/check groups | Result and residual estimate |
| --- | --- | --- |
| N204 | Four groups: exact uncited manuscript-prose audit and provenance correction; fresh-label comap construction; proof the old/new targets form a circuit for a nonloop; finite extension and N065 proper-sum existence/retained-target bridge. | `parallelTargetCopy`, `IsParallelTargetConstruction`, and `exists_parallelTargetConstruction` are `KERNEL_PROVED`; no remaining definition cost. The former `EXTERNAL_CITED` metadata was corrected to `MANUSCRIPT_DEFINITION` without an admission. N205/N206 remain separate. |
| N066 | Two new groups in addition to earlier quotient work: complete proper three-sum specification; finite binary paired-triangle span membership iff indexed subset sum. | `UNRESOLVED`, run-locally deferred. The two directions of the quotient candidate's exact cycle correspondence remain; the 6.0→5.5 remaining-cost update reflects the checked subset-sum bridge while retaining a substantial proof obligation. No external premise can discharge this manuscript construction. |

Focused `lake build Matroid.ParallelTarget Matroid.ThreeSum` and the tracked axiom audit passed. All new N204 and N066 helper declarations show only ordinary Lean axioms. The next scheduler run retains `--defer-node N152 --defer-node N066` for this invocation.

## Current five-batch invocation, batch 5 — 2026-10-19

With N152 and N066 deferred only for this run, strict scheduling selected N172→N173 (score 3.512; residual sum 5.6). N172's direct prerequisites N024/N061/N070 and N173's N025/N062/N070 were available. The manuscript's `prop:r10-proper-minors` cites Oxley Lemma 6.6.9 for both single-element identities. The exact printed lemma and its `A10` proof were inspected before either external premise was introduced; the statement, ten-element labels, K3,3 graph, and dual correspond as recorded in `SOURCES.md`. Per-node elapsed time and tokens are `UNKNOWN`.

| ID | Observed route and substantive Lean edit/check groups | Result and residual estimate |
| --- | --- | --- |
| N172 | Three groups: exact Oxley lemma and `A10` source comparison; nine-edge K3,3 graph and labeled graphic matroid; isolated binary deletion premise plus admission-free real-R10 wrapper and focused build. | `CITED_ASSUMPTION` via `External.binaryR10_delete_isK33`. The narrow source-verified premise is complete; no remaining scheduled cost. |
| N173 | Two groups: source dual-contraction comparison; K3,3 bond matroid and original-label embedding premise; real-R10 wrapper and focused build. | `CITED_ASSUMPTION` via `External.binaryR10_contract_isK33Dual`. The narrow source-verified premise is complete; no remaining scheduled cost. |

`lake build Matroid.R10Minors Matroid.FiveBatchAxiomAudit` passed (1919 focused jobs). The tracked audit prints `sorryAx` for N172 and N173, precisely through their isolated external premises; `K33.cycleMatroid_ground` prints only ordinary Lean axioms. No new direct edge or depth change arose. Records were updated before reranking.

Final checks: full `lake build` passed (9183 jobs; shared check, not a per-node time estimate), eight scheduler unit tests passed, and `git diff --check` passed. The tracked five-batch axiom audit has `sorryAx` only where an explicitly recorded cited premise is transitive. The strict scheduler with N152/N066 run-locally deferred selected N185→N187; clearing both deferrals and regenerating `NEXT_BATCH.md` and JSON selected N066→N159 (score 3.729). All ordinal costs and reasons reflect remaining work; per-node elapsed time/tokens remain `UNKNOWN`.
