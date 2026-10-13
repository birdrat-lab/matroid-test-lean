# Structural depth-7 source and trust audit

Entry checkpoint: 2026-10-13. The entry active DAG had 197 nodes and 448 direct edges. Mechanical comparison of `LEDGER.md`, `DEPENDENCY_EDGES.csv`, and `DEPTHS.csv` gave exactly the 34 unresolved candidate IDs in `AGENTS.md`; all their direct prerequisites had depth at most 6. `lake build` and `git diff --check` passed before proof edits. Kernel certification is through depth 5; depth 6 is complete only relative to the cited N052 premise. This file records the current pass, not a claim that every candidate has been proved.

The manuscript's recursive-construction proof explicitly invokes regular 2-sum closure to make each newly attached stage a valid regular input for N065. The direct edge **N068→N218** was therefore added with that evidence. The active graph now has 449 edges; N218 moves from depth 7 to 8, and N151, N219, N220, N223, N224, N226, and N228 move one layer downstream. The frozen in-scope depth-7 set has 33 original candidates. No N218 proof is attempted in this pass.

## Matroid-first plans recorded before the first proof edits

| ID | Manuscript statement and minimal abstract hypotheses | Matroid-only route; representation need | Direct prerequisites | Current result |
| --- | --- | --- | --- | --- |
| N018 | `def:hyperplane-cocircuit`: for a matroid on `E`, a cocircuit is `E \ H` for a maximal proper flat `H`. | Define the complement predicate from `IsHyperplane`. No realization is needed. | N017 | **PASS:** `IsHyperplaneCocircuit` and its exact unfolding theorem. No `sorryAx`. This is the manuscript definition; an equivalence to mathlib's separate dual-circuit predicate is a possible later API bridge, not part of the definition. |
| N034 | `def:modular-cut`: a family of flats is upward closed among flats and closed under intersection of modular pairs. | State the two closure axioms directly using `IsFlat` and N033 `IsModularPair`; no realization is needed. | N012, N033 | **PASS:** `IsModularCut` contains flat membership and exactly both closure conditions. No `sorryAx`. |
| N106 | `prop:positive-support-circuits`: on accepted input, the least available spanning-set size is the least `|C|-1` for a target circuit with its other elements available. | Use mathlib's closure–circuit equivalence, finite cardinality, and minimality of `sInf`; target excluded from availability. No realization is needed. | N015, N081, N105 | **PASS:** `positiveSpanningSupport_eq_circuitSupport`, with finite ground, `τ∈E`, `A⊆E\{τ}`, and `τ∈cl A`. No `sorryAx`. |
| N144 | In `prop:seymour-two-sum-input-minors`, if available `A` spans target `e`, then `e` is a loop in `N/A`, and the port weight convention reads `∞`. | Apply N030, then N214's extended ratio theorem. No realization is needed. | N025, N030 | **PASS:** `contractedPort_isLoop` and `contractedPort_ratio_eq_top`; the latter has explicit finite contracted ground and strict positivity of surviving non-target weights. No `sorryAx`. |
| N149 | Proper 2-sum ground size: `|E(M ⊕₂ N)| = |E(M)| + |E(N)| - 2`. | Use N065's exact symmetric-difference ground and singleton intersection; finite-set cardinality identities. No realization is needed. | N065 | **PASS:** `regularTwoSum_ground_ncard`, with all N065 properness assumptions. No `sorryAx`. |
| N175 | Every minor of a cographic matroid on a finite labeled graph is cographic. | Express cographic as dual graphic, dualize the minor relation, apply N174, and dualize back. No new graph construction is needed; the bridge is N174's labeled graphic theorem. | N026, N062, N174 | **PASS:** `IsCographic.minor`; the dual/minor bridge uses exact deletion-contraction duality and retains edge labels. No `sorryAx`. |

## Group B plans recorded before proof edits

| ID | Exact source use and minimal hypotheses | Matroid-first candidate and realization decision | Direct prerequisites; initial disposition |
| --- | --- | --- | --- |
| N138 | `thm:seymour-two-sum` proof: a basis of a proper 2-sum uses the common element on exactly one side; finite summands and N065 properness hypotheses. | A first abstract route proves `regularTwoSum_indep_of_bases_first_port` using N065 cycles: a cycle inside the proposed union forces a cycle in the port-containing first basis, then in the second basis, so it is empty. No new realization is used. The opposite port orientation, maximality, and converse are not yet proved. | N002, N065; **partial**, remains `UNRESOLVED`. |
| N146 | `prop:recursive-r10-closure` proof: a target circuit in a proper 2-sum either avoids glue on the target side or joins two glue-containing circuits. | Extract minimal nonempty members of N065's cycle family and prove the two circuit cases using matroid circuit elimination. No new representation is logically necessary. | N015, N065; open. |
| N152 | Same recursive proof: a child reduced to a two-element circuit on glue and leaf makes the parent 2-sum a relabeling of that port. | Use N065's cycle equivalence plus the unique cycle family of `U_{1,2}` to prove an explicit original-label matroid isomorphism. No new representation is necessary. | N015, N025, N065; open. |
| N204 | Unlabeled second-program passage in `sec:r10-pointed`: add a target-parallel copy, glue the old target to a graphic piece by 2-sum, and keep the copy as target. | First specify the parallel extension and two distinct target/glue labels, then prove the result's target label and ground. The graph occurs only for the manuscript's concrete second program; generic construction remains matroidal. | N021, N065; statement design open. |
| N068 | After `def:regular-matroid-sums`, regularity survives proper 2-sum. | Seek abstract minor/representation theorem first. If only an arbitrary-field representation construction works, isolate the field bridge and prove equality with N065's cycle matroid. Oxley/Seymour citation must be matched before any admission. | N051, N065; external cited, open. |
| N218 | Recursive passage in `sec:r10-recursive`: attach nine fresh pointed copies by proper 2-sums and retain root target. | Induct using N065 on original labels; regularity of each prior stage is needed to call that constructor. The R10 representation is necessary only for the seed N070, while the recursive glue is abstract. | **Moved to depth 8** by N068→N218; no proof this pass. |

Later target plans and completed declaration audits will be appended before their proof edits. The finite R10 claims require their exact N070 representation; the current completed claims have general matroid interfaces.

## Group C plans recorded before proof edits

| ID | Exact manuscript claim and minimal hypotheses | Matroid-first route and representation decision | Direct prerequisites; initial disposition |
| --- | --- | --- | --- |
| N162 | Following `prop:regular-triangle-identity`: with coindependent triangle `T`, positive weights on `E\T`, the `a=Φ_T` class is strictly positive. | Coindependence makes `E\T` spanning. Take a basis `S` of that set, verify `cl S=E`, then isolate its positive product in N266's finite sum. No realization is needed. | N004, N266; **PASS:** `weightedTriangle_a_pos`, no `sorryAx`. |
| N163 | Same passage: `c=Φ_∅` is strictly positive under the same hypotheses. | Extend an independent pair of the triangle to a full basis and remove the triangle; `Indep.closure_inter_eq_inter_closure` shows its remaining elements span no nonloop triangle element. Isolate its positive product. No realization is needed. | N004, N266; **PASS:** `weightedTriangle_c_pos`, distinct triangle elements and positive nontriangle weights explicit; no `sorryAx`. |
| N161 | `prop:regular-triangle-identity`: for every regular coindependent triangle and positive nontriangle weights, `ac=p₁p₂+p₁p₃+p₂p₃`, including zero singleton classes. | First inspect whether N266's five weighted-basis classes admit an intrinsic polynomial exchange identity. If no short abstract identity appears, isolate the manuscript's TU Cauchy–Binet/Plücker determinant bridge using N052 and N125. Realization is necessary only for that Plücker step, and the output must be the five matroid class sums. | N051, N125, N266; open. |
| N267 | `eq:k4-five-sums`: for `M(K₄)` with three triangle edges and spoke weights `(α₁,α₂,α₃)`, the five N266 classes are `(α₁α₂α₃, α₂α₃, α₁α₃, α₁α₂, α₁+α₂+α₃)`. | The object is a specific finite graphic matroid, so enumerate its six labeled edges and N266's independent/spanning/closure predicates with a kernel-checked finite certificate. Bridge back through `weightedTriangleSignature`; no generic graph specialization is claimed. | N061, N266; open. |

## Finite R10 certificate plans recorded before proof edits

The exact displayed matrix is N070's `r10IntegerMatrix`, with ten original `Fin 10` column labels. The finite claims below are about this specific object; matrix computation is logically necessary for its certificate, then every result must be stated in the `r10` matroid interface. A finite integer minor predicate should be proved equivalent to matroid independence/basis membership once and reused; `decide` is kernel checked, while `native_decide` would add an unacceptable computation axiom.

| ID | Manuscript claim and abstract output | Finite proof route; initial status |
| --- | --- | --- |
| N169 | Geometry paragraph of `app:r10-atlas`: exactly fifteen 4-circuits and fifteen 6-circuits of `r10`. | Enumerate finite subsets and test minimal dependence through the common minor/independence oracle; open. |
| N170 | Same paragraph: `r10` has no 3-circuit. | N053 transfers the exact N070 TU representation to `ZMod 2`; each displayed column has coordinate sum one, so every binary circuit has even size. This returns a circuit-size statement on `r10` and avoids 120 triple tests. | **PASS:** `r10_circuit_card_ne_three`; no `sorryAx`. |
| N182 | Same paragraph: `r10` has exactly 162 bases. | Reuse N125's full-row-rank determinant/base equivalence, transfer real determinant nonvanishing to the integer matrix, and count the 252 five-column minors with kernel `decide`; open. |
| N185 | `prop:r10-symmetry`: automorphism group order 720. | Define labeled automorphisms by preservation of the finite basis predicate, enumerate all and prove completeness rather than only exhibit candidates; open. |
| N186 | Same proposition: automorphisms act transitively on all ten elements. | Derive from explicit certified automorphisms that preserve the finite basis predicate; open. |
| N172/N173 | `prop:r10-proper-minors`: each labeled single-element deletion/contraction is isomorphic to `M(K₃,₃)` / its dual. | Build an explicit labeled edge permutation and test equality of finite independent sets through the oracle; rank/circuit counts alone are insufficient; open. |
| N193/N194 | Pointed determinant and cofactor formulas: target-out and target-in weighted basis polynomials. | Expand exact determinant/cofactor of the N070 matrix and identify monomials with indexed bases using N125; coordinates are intrinsic to the claim; open. |
| N195 | `lem:r10-minimal-positive`: six perfect matchings plus nine row-column supports are exactly the minimal target-spanning subsets of `r10`. | Enumerate target circuits via finite independence oracle, then compare explicit K3,3 label map; N207's separate graphic program is only a comparison; open. |
| N225 | R10 itself neither graphic nor cographic. | Seek a matroidal excluded-minor/planarity route first, then use certified finite circuits if needed; open. |
| N238/N239 | The pointed closure predicate has 256 positive/256 negative inputs and two five-sensitive witnesses. | Enumerate all 512 non-target subsets using the finite oracle, prove target closure and toggling statements on original labels; open. |
| N255 | Connectedness of displayed R10 as used for target/non-target common circuits. | First audit the unlabeled manuscript claim and exact role, then derive common circuits from the finite oracle; provenance is still unresolved; open. |

## Group D plans recorded before proof edits

| ID | Exact manuscript claim and minimal hypotheses | Matroid-first route; representation decision | Direct prerequisites; initial disposition |
| --- | --- | --- | --- |
| N244 | `prop:relation-fundamental-circuits`: the free target and every response generator form a basis before relation contraction; a positive relation has fundamental circuit equal to itself, target, and exactly the response coordinates with nonzero coefficients. | N243 supplies the basis. A closure/support equivalence proves the general matroid fundamental-circuit/coordinate-support lemma for the indexed free-relation representation. The representation identifies coefficient support; output is an exact labeled matroid circuit. | N031, N243; **PASS:** `positiveRelation_fundCircuit` and `positiveRelation_fundCircuit_isCircuit`; no `sorryAx`. |
| N059 | `thm:regular-quotient-form`: finite regular `M` on `E` iff it is the identity-on-`E` contraction of a regular extension on disjoint finite relation labels, whose deletion is free on `E`. | Reverse implication uses N049 minor closure. Forward implication selects N052's TU representation, pivots to `[I D]`, uses a kernel basis `[-D;I]` and TU identity-extension preservation, then N020 contraction representation. The coordinate construction is essential for regularity of the extension; the output must be matroidal and preserve labels. | N020, N049, N051, N052, N056, N057; open, conditionally dependent on N052. |
| N055 | `prop:regular-basic-properties`: every real representation of a regular matroid is projectively equivalent to a fixed real TU representation, with isomorphism on column spans and nonzero scalars on nonloops. | Try a short representation uniqueness bridge in pinned mathlib; the claim is inherently representational and cannot follow from matroid independence alone. Exact Brylawski–Lucas/Oxley source and external budget gate apply before any admission. | N047, N051, N052; external cited, open. |
| N118 | Signed circuit dependency in the paragraph preceding `thm:regular-support-bound`: in a TU representation, a circuit containing a nonloop target has a dependency normalized to target coefficient one and every other nonzero coefficient in `{±1}`. | Matroid circuit gives unique dependency support; determinant/Cramer's-rule bridge over the TU matrix supplies unit magnitudes. Coordinates are essential for the sign assertion, and the resulting statement must quantify over the actual circuit and representation. | N015, N052; external cited, open. |

## Full corrected depth-7 status and source correspondence

The following is the entire corrected structural layer. `COMPLETE` in the ledger is used only for the ten rows with kernel proofs. The finite and externally cited rows remain open until their exact conclusions are proved or, for a genuinely external theorem only, a separately justified premise is admitted.

| ID | Source claim / use | Direct prerequisites | Lean declaration or residual | Trust status |
| --- | --- | --- | --- | --- |
| N018 | Cocircuit (def:hyperplane-cocircuit) | N017 | Matroid.IsHyperplaneCocircuit; isHyperplaneCocircuit_iff | `KERNEL_PROVED` |
| N034 | Modular cut (def:modular-cut) | N012, N033 | Matroid.IsModularCut | `KERNEL_PROVED` |
| N055 | Projective uniqueness of regular matroids (`prop:regular-basic-properties`) | N047, N051, N052 | See exact residual in `PROOF_BUDGET.md` | `UNRESOLVED` |
| N059 | Regular free quotient form (`thm:regular-quotient-form`) | N020, N049, N051, N052, N056, N057 | See exact residual in `PROOF_BUDGET.md` | `UNRESOLVED` |
| N068 | Two-sum preserves regularity (—) | N051, N065 | See exact residual in `PROOF_BUDGET.md` | `UNRESOLVED` |
| N106 | Positive support by target circuits (prop:positive-support-circuits) | N015, N081, N105 | Matroid.positiveSpanningSupport_eq_circuitSupport | `KERNEL_PROVED` |
| N118 | Signed circuit dependency (—) | N015, N052 | See exact residual in `PROOF_BUDGET.md` | `UNRESOLVED` |
| N138 | Proper 2-sum basis correspondence (—) | N002, N065 | partial: `regularTwoSum_indep_of_bases_first_port`; residual in `PROOF_BUDGET.md` | `UNRESOLVED` |
| N144 | Positive contraction loop (prop:seymour-two-sum-input-minors; N030 and N214) | N025, N030 | Matroid.contractedPort_isLoop; contractedPort_ratio_eq_top | `KERNEL_PROVED` |
| N146 | Two-sum target-circuit gluing (—) | N015, N065 | See exact residual in `PROOF_BUDGET.md` | `UNRESOLVED` |
| N149 | Two-sum ground-set cardinality (def:regular-matroid-sums; N065) | N065 | Matroid.regularTwoSum_ground_ncard | `KERNEL_PROVED` |
| N152 | Recover parent across a two-element circuit (—) | N015, N025, N065 | See exact residual in `PROOF_BUDGET.md` | `UNRESOLVED` |
| N161 | Triangle five-sum identity (`prop:regular-triangle-identity`) | N051, N125, N266 | See exact residual in `PROOF_BUDGET.md` | `UNRESOLVED` |
| N162 | Triangle a positivity (following prop:regular-triangle-identity) | N004, N266 | Matroid.weightedTriangle_a_pos | `KERNEL_PROVED` |
| N163 | Triangle c positivity (following prop:regular-triangle-identity) | N004, N266 | Matroid.weightedTriangle_c_pos | `KERNEL_PROVED` |
| N169 | R10 circuit counts (—) | N015, N070 | See exact residual in `PROOF_BUDGET.md` | `UNRESOLVED` |
| N170 | R10 has no triangles (app:r10-atlas; N053 field transfer; N070 exact matrix) | N015, N070 | Matroid.r10_circuit_card_ne_three | `KERNEL_PROVED` |
| N172 | R10 single deletion (`prop:r10-proper-minors`) | N024, N061, N070 | See exact residual in `PROOF_BUDGET.md` | `UNRESOLVED` |
| N173 | R10 single contraction (`prop:r10-proper-minors`) | N025, N062, N070 | See exact residual in `PROOF_BUDGET.md` | `UNRESOLVED` |
| N175 | Cographic minor closure (Duality of labeled graphic minors; N174) | N026, N062, N174 | Matroid.IsCographic.minor | `KERNEL_PROVED` |
| N182 | R10 total basis count (`prop:r10-basis-polynomials`) | N002, N070 | See exact residual in `PROOF_BUDGET.md` | `UNRESOLVED` |
| N185 | R10 automorphism order (`prop:r10-symmetry`) | N070 | See exact residual in `PROOF_BUDGET.md` | `UNRESOLVED` |
| N186 | R10 element transitivity (`prop:r10-symmetry`) | N070 | See exact residual in `PROOF_BUDGET.md` | `UNRESOLVED` |
| N193 | R10 pointed determinant (—) | N070, N122, N125 | See exact residual in `PROOF_BUDGET.md` | `UNRESOLVED` |
| N194 | R10 pointed cofactor (—) | N070, N122, N125 | See exact residual in `PROOF_BUDGET.md` | `UNRESOLVED` |
| N195 | Pointed R10 target circuits (`lem:r10-minimal-positive`) | N070, N081 | See exact residual in `PROOF_BUDGET.md` | `UNRESOLVED` |
| N204 | Parallel target construction (—) | N021, N065 | See exact residual in `PROOF_BUDGET.md` | `UNRESOLVED` |
| N225 | R10 nongraphic/noncographic status (—) | N061, N062, N070 | See exact residual in `PROOF_BUDGET.md` | `UNRESOLVED` |
| N238 | Pointed R10 closure balance (—) | N007, N070 | See exact residual in `PROOF_BUDGET.md` | `UNRESOLVED` |
| N239 | Pointed R10 sensitivity witnesses (—) | N007, N070 | See exact residual in `PROOF_BUDGET.md` | `UNRESOLVED` |
| N244 | Relation fundamental-circuit support (prop:relation-fundamental-circuits; N243) | N031, N243 | Matroid.positiveRelation_fundCircuit; Matroid.positiveRelation_fundCircuit_isCircuit | `KERNEL_PROVED` |
| N255 | R10 connectedness (—) | N015, N070 | See exact residual in `PROOF_BUDGET.md` | `UNRESOLVED` |
| N267 | Weighted K4 triangle signature (`eq:k4-five-sums`) | N061, N266 | See exact residual in `PROOF_BUDGET.md` | `UNRESOLVED` |

N018/N034 are exact manuscript definitions. N106 includes target exclusion and the `|C|-1` minimum. N144 separates loop status from the extended `∞` port ratio. N149 retains proper-port hypotheses and finite cardinality. N175 retains edge labels and uses duality of N174. N162/N163 include coindependence, distinct triangle elements where needed, and positive nontriangle weights. N170 proves the no-three-circuit fact through N053 field transfer and the exact N070 binary parity certificate. N244 uses N243 for the free basis and proves exact relation/target/nonzero-response circuit support. Each of these ten declarations prints only foundational axioms (`propext`, `Classical.choice`, `Quot.sound`) or none; none depends on N052.

For N059, a future proof using N052 would be `CONDITIONAL_PROOF`, not `KERNEL_PROVED`. N068, N055, and N118 have neither an exact checked literature match nor exhausted serious proof routes; they remain unresolved and have no admission. N204 is a statement-design blocker; N255 retains unresolved provenance. N182 has a numerical `#eval` but no kernel certificate. The corrected DAG has 197 active nodes, 449 edges, and 33 depth-7 nodes, 10 kernel-proved. Kernel-certified depth is 5 and citation-relative depth is 6.
