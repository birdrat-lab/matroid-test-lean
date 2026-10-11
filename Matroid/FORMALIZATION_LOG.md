# First basis/rank/closure/circuit formalization pass

The manuscript source is `Manuscript/main.tex`, lines around `def:matroid` through `prop:closure-circuit`. The proof plans below were recorded from that text before mathlib reconnaissance. Only N001, N002, N015, N003, N006, N007, and N016 are targets of this pass.

## N001 — Finite matroid

- **Ledger ID:** N001
- **TeX label:** `def:matroid`
- **Requirement:** A finite ground set with independent sets satisfying the empty-set, hereditary, and cardinality augmentation axioms.
- **Manuscript proof status:** Definition; no proof claimed.
- **Manuscript proof plan:** Use the manuscript's independent-set presentation as the mathematical interpretation of the foundational matroid object. Check that the existing matroid abstraction exposes independent sets and the corresponding axioms on a finite ground set.
- **Lean declaration:** `Matroid α` with `[M.Finite]`; no new project constant.
- **Formalization source:** `MATHLIB_EXACT`.
- **Mathlib declarations used:** `Matroid`, `Matroid.Finite`, `Matroid.Indep`, `Matroid.Indep.augment`, and `IndepMatroid.matroid` (the existing independence-axiom-to-matroid construction).
- **Deviation from manuscript proof:** Mathlib packages the matroid with bases, independence, base exchange, and maximality fields rather than the manuscript pair `(E, 𝓘)`. On finite ground sets its `Indep.augment` supplies (I3); this is a representation choice, not a change in mathematical object.
- **Build status:** `lake build` passed.
- **Notes:** No competing matroid structure is intended.

## N002 — Basis

- **Ledger ID:** N002
- **TeX label:** `def:matroid-basis`
- **Requirement:** A maximal independent subset of `A`, with the whole-ground-set basis as its special case.
- **Manuscript proof status:** Definition; no proof claimed.
- **Manuscript proof plan:** Interpret a basis of `A` as an independent subset of `A` maximal under inclusion. For `A=E`, recover the ordinary basis of the matroid.
- **Lean declaration:** `Matroid.IsBasis I X`; `Matroid.IsBase B` for `X=M.E`. No new project constant.
- **Formalization source:** `MATHLIB_EXACT`.
- **Mathlib declarations used:** `Matroid.IsBasis`, `Matroid.isBasis_ground_iff`, and `Matroid.IsBasis.indep` / `Matroid.IsBasis.subset`.
- **Deviation from manuscript proof:** None; mathlib defines `IsBasis` as maximal independent in `X` with `X ⊆ M.E`.
- **Build status:** `lake build` passed.
- **Notes:** Subset bases and full bases must remain distinguishable.

## N015 — Circuit

- **Ledger ID:** N015
- **TeX label:** `def:matroid-circuit`
- **Requirement:** A minimal dependent subset of the ground set.
- **Manuscript proof status:** Definition; no proof claimed.
- **Manuscript proof plan:** Identify the existing circuit predicate with dependence plus independence of every proper subset.
- **Lean declaration:** `Matroid.IsCircuit C`; no new project constant.
- **Formalization source:** `MATHLIB_EXACT`.
- **Mathlib declarations used:** `Matroid.IsCircuit`, `Matroid.isCircuit_iff_forall_ssubset`, and `Matroid.isCircuit_iff_minimal_not_indep`.
- **Deviation from manuscript proof:** None; the predicate is minimal dependence on the ground set.
- **Build status:** `lake build` passed.
- **Notes:** The manuscript uses finite ground sets.

## N003 — Equal basis cardinalities

- **Ledger ID:** N003
- **TeX label:** `def:matroid-basis` (unlabeled prose immediately after the definition).
- **Requirement:** Two bases of the same subset have equal cardinality.
- **Manuscript proof status:** `MANUSCRIPT_SKETCH`.
- **Manuscript proof plan:** Suppose one subset basis is smaller. Cardinality augmentation adds an element from the larger independent basis to the smaller one, contradicting maximality. Repeat symmetrically to rule out either strict inequality.
- **Lean declaration:** `Matroid.isBasis_ncard_eq`.
- **Formalization source:** `MATHLIB_BRIDGE`.
- **Mathlib declarations used:** `Matroid.IsBasis.encard_eq_encard`, `Set.ncard_def`, and the underlying base-exchange cardinality theorem `Matroid.IsBase.encard_eq_encard_of_isBase`.
- **Deviation from manuscript proof:** The Lean proof delegates exchange to mathlib and converts `encard` equality to natural cardinality. This follows the manuscript exchange argument at the level of the key mathematical step.
- **Build status:** `lake build` passed.
- **Notes:** The manuscript states the exchange consequence but does not write the argument.

## N006 — Rank

- **Ledger ID:** N006
- **TeX label:** `def:matroid-rank`
- **Requirement:** Maximum cardinality of an independent subset of `A`, equivalently the cardinality of any basis of `A`.
- **Manuscript proof status:** `MANUSCRIPT_SKETCH` for the basis-cardinality equivalence; the rank formula itself is a definition.
- **Manuscript proof plan:** Define rank by the maximum independent cardinality; a basis reaches this maximum by exchange, and N003 makes its cardinality independent of the basis choice.
- **Lean declaration:** `Matroid.isBasis_eRk_eq_ncard` and `Matroid.indep_ncard_le_isBasis_ncard`.
- **Formalization source:** `MATHLIB_BRIDGE`.
- **Mathlib declarations used:** `Matroid.eRk`, `Matroid.exists_isBasis`, `Matroid.IsBasis.encard_eq_eRk`, `Matroid.Indep.encard_le_eRk_of_subset`, `Matroid.IsBasis.Finite`, `Set.Finite.encard_eq_coe`, and `Set.encard_le_coe_iff_finite_ncard_le`.
- **Deviation from manuscript proof:** Mathlib defines `eRk` through bases and stores finite rank in `ℕ∞`, whereas the manuscript defines a natural-number maximum over independent subsets. The two bridge theorems show a basis attains that maximum and every independent subset has no larger natural cardinality.
- **Build status:** `lake build` passed.
- **Notes:** The manuscript rank is finite and integer-valued.

## N007 — Closure

- **Ledger ID:** N007
- **TeX label:** `def:matroid-closure`
- **Requirement:** `e ∈ cl(A)` exactly when adding `e` to `A` leaves rank unchanged.
- **Manuscript proof status:** Definition; no proof claimed.
- **Manuscript proof plan:** Identify closure with the rank-equality condition after adjoining a singleton, using the finite rank notion of N006.
- **Lean declaration:** `Matroid.mem_closure_iff_eRk_insert_eq`.
- **Formalization source:** `MATHLIB_BRIDGE`.
- **Mathlib declarations used:** `Matroid.closure`, `Matroid.eRk_closure_eq`, `Matroid.closure_insert_eq_of_mem_closure`, and `Matroid.IsRkFinite.closure_eq_closure_of_subset_of_eRk_ge_eRk`.
- **Deviation from manuscript proof:** Mathlib defines closure using flats rather than the manuscript rank test. The bridge proves the rank test in both directions on a finite ground set; this is formalization of the manuscript definition, not a manuscript proof transcription.
- **Build status:** `lake build` passed.
- **Notes:** The project-facing statement should expose the manuscript's rank test even if closure is primitive in mathlib.

## N016 — Circuit characterization of closure

- **Ledger ID:** N016
- **TeX label:** `prop:closure-circuit`
- **Requirement:** For `e ∉ A`, `e ∈ cl(A)` iff a circuit contains `e` and has all other elements in `A`.
- **Manuscript proof status:** `MANUSCRIPT_STATEMENT_ONLY`.
- **Manuscript proof plan:** No detailed proof appears in the manuscript. The surrounding prose interprets the circuit as a minimal dependence witnessing failure of rank increase. Prove the exact equivalence using standard circuit/closure mathematics, preserving `e ∉ A`.
- **Lean declaration:** `Matroid.mem_closure_iff_exists_circuit_sdiff`.
- **Formalization source:** `MATHLIB_BRIDGE`.
- **Mathlib declarations used:** `Matroid.mem_closure_iff_exists_isCircuit` and `Matroid.IsCircuit`.
- **Deviation from manuscript proof:** There is no manuscript proof to follow. The local bridge converts mathlib’s circuit containment `C ⊆ insert e A` into the exact manuscript form `e ∈ C ∧ C \ {e} ⊆ A`, retaining finite-ground and `A ⊆ M.E` hypotheses.
- **Build status:** `lake build` passed.
- **Notes:** Do not replace the exact side condition or circuit containment conclusion with a similar variant.

# Second frontier pass

The frozen target set is recorded in `FRONTIER_PASS_2.md`. Plans below follow the frozen manuscript; mathlib declarations were inspected afterward. `BLOCKED_*` results retain an incomplete ledger status.

## N004 — Extension within a subset

- **Ledger ID:** N004
- **TeX label:** unlabeled; material uses S: `prop:cocircuit-separates-closure`, `prop:support-linear-characterization`, `prop:r10-proper-minors`
- **Requirement:** An independent I ⊆ A extends to a basis of A
- **Manuscript proof status:** MANUSCRIPT_STATEMENT_ONLY
- **Manuscript proof plan:** Extend an independent set inside the specified subset to a maximal independent subset.
- **Lean declaration:** Matroid.Indep.subset_isBasis_of_subset
- **Formalization source:** MATHLIB_EXACT
- **Mathlib declarations used:** Matroid.Indep.subset_isBasis_of_subset
- **Deviation from manuscript proof:** None; the manuscript invokes the extension in the proof of `prop:cocircuit-separates-closure`.
- **Result:** COMPLETE
- **Build status:** `lake build` passed for completed declarations; blocked entries leave no unproved active declaration.
- **Notes:** The theorem retains the subset-of-ground hypothesis.

## N008 — Closure extensivity

- **Ledger ID:** N008
- **TeX label:** unlabeled; material uses S: `prop:target-extension-criterion`, `prop:query-separation-cover`
- **Requirement:** A ⊆ cl_M(A)
- **Manuscript proof status:** MANUSCRIPT_STATEMENT_ONLY
- **Manuscript proof plan:** Adding an element already in a set preserves rank, hence every ground element of the set lies in its closure.
- **Lean declaration:** Matroid.subset_closure
- **Formalization source:** MATHLIB_EXACT
- **Mathlib declarations used:** Matroid.subset_closure
- **Deviation from manuscript proof:** Mathlib proves the closure law from its flat-based closure; N007 relates that closure to rank.
- **Result:** COMPLETE
- **Build status:** `lake build` passed for completed declarations; blocked entries leave no unproved active declaration.
- **Notes:** Requires the manuscript hypothesis `A ⊆ E`.

## N009 — Closure monotonicity

- **Ledger ID:** N009
- **TeX label:** unlabeled; material uses S: `prop:target-extension-criterion`, `prop:query-separation-cover`
- **Requirement:** A ⊆ B implies cl_M(A) ⊆ cl_M(B)
- **Manuscript proof status:** MANUSCRIPT_STATEMENT_ONLY
- **Manuscript proof plan:** Use monotonicity of rank and the closure operator to carry closure membership from a subset to a superset.
- **Lean declaration:** Matroid.closure_subset_closure
- **Formalization source:** MATHLIB_EXACT
- **Mathlib declarations used:** Matroid.closure_subset_closure; Matroid.closure_mono
- **Deviation from manuscript proof:** Mathlib proves the flat-based form, linked to the manuscript rank closure by N007.
- **Result:** COMPLETE
- **Build status:** `lake build` passed for completed declarations; blocked entries leave no unproved active declaration.
- **Notes:** No additional qualification.

## N010 — Closure idempotence

- **Ledger ID:** N010
- **TeX label:** unlabeled; material uses S: `prop:target-extension-criterion`, `prop:query-separation-cover`
- **Requirement:** cl_M(cl_M(A)) = cl_M(A)
- **Manuscript proof status:** MANUSCRIPT_STATEMENT_ONLY
- **Manuscript proof plan:** Closing a set adds every element already rank-dependent on it, so closing again adds nothing.
- **Lean declaration:** Matroid.closure_closure
- **Formalization source:** MATHLIB_EXACT
- **Mathlib declarations used:** Matroid.closure_closure
- **Deviation from manuscript proof:** Mathlib proves the flat-based form, linked to the manuscript rank closure by N007.
- **Result:** COMPLETE
- **Build status:** `lake build` passed for completed declarations; blocked entries leave no unproved active declaration.
- **Notes:** Used when replacing availability sets by closures in `prop:target-extension-criterion`.

## N011 — Steinitz closure exchange

- **Ledger ID:** N011
- **TeX label:** unlabeled; material uses S: `prop:agreement-set-flat`, `lem:r10-minimal-positive`
- **Requirement:** If e ∈ cl_M(A ∪ {f}) \ cl_M(A), then f ∈ cl_M(A ∪ {e})
- **Manuscript proof status:** MANUSCRIPT_SKETCH
- **Manuscript proof plan:** Apply Steinitz exchange to an element newly spanned after one insertion; the agreement-flat proof invokes this principle by name.
- **Lean declaration:** Matroid.closure_exchange
- **Formalization source:** MATHLIB_EXACT
- **Mathlib declarations used:** Matroid.closure_exchange
- **Deviation from manuscript proof:** Mathlib supplies the standard exchange proof omitted by the manuscript.
- **Result:** COMPLETE
- **Build status:** `lake build` passed for completed declarations; blocked entries leave no unproved active declaration.
- **Notes:** Mathlib gives the stronger conclusion that the exchanged element was also outside the original closure.

## N012 — Flat

- **Ledger ID:** N012
- **TeX label:** `def:matroid-flat`
- **Requirement:** A set fixed by matroid closure
- **Manuscript proof status:** MANUSCRIPT_DEFINITION
- **Manuscript proof plan:** Interpret a flat as a set equal to its closure.
- **Lean declaration:** Matroid.IsFlat
- **Formalization source:** MATHLIB_EXACT
- **Mathlib declarations used:** Matroid.IsFlat; Matroid.isFlat_iff_closure_eq
- **Deviation from manuscript proof:** None.
- **Result:** COMPLETE
- **Build status:** `lake build` passed for completed declarations; blocked entries leave no unproved active declaration.
- **Notes:** No additional qualification.

## N020 — Free matroid

- **Ledger ID:** N020
- **TeX label:** `def:free-matroid`
- **Requirement:** All subsets independent; equivalently unique basis `E` and identity closure
- **Manuscript proof status:** MANUSCRIPT_DEFINITION
- **Manuscript proof plan:** Construct the matroid with all subsets of E independent; its only full basis is E and closure on subsets of E is identity.
- **Lean declaration:** Matroid.freeOn
- **Formalization source:** MATHLIB_EXACT
- **Mathlib declarations used:** Matroid.freeOn; Matroid.freeOn_indep_iff; Matroid.freeOn_isBase_iff; Matroid.freeOn_closure_eq
- **Deviation from manuscript proof:** Mathlib states closure on arbitrary ambient subsets as `X ∩ E`; on manuscript subsets `X ⊆ E` this is X.
- **Result:** COMPLETE
- **Build status:** `lake build` passed for completed declarations; blocked entries leave no unproved active declaration.
- **Notes:** No additional qualification.

## N021 — Loop

- **Ledger ID:** N021
- **TeX label:** `def:loop-coloop`
- **Requirement:** e is a loop iff e ∈ cl_M(∅), equivalently {e} is a circuit
- **Manuscript proof status:** MANUSCRIPT_DEFINITION
- **Manuscript proof plan:** Identify loops with elements in closure of the empty set and with singleton circuits.
- **Lean declaration:** Matroid.IsLoop
- **Formalization source:** MATHLIB_EXACT
- **Mathlib declarations used:** Matroid.IsLoop; Matroid.closure_empty; Matroid.singleton_isCircuit
- **Deviation from manuscript proof:** None.
- **Result:** COMPLETE
- **Build status:** `lake build` passed for completed declarations; blocked entries leave no unproved active declaration.
- **Notes:** No additional qualification.

## N022 — Coloop

- **Ledger ID:** N022
- **TeX label:** `def:loop-coloop`
- **Requirement:** e is a coloop iff it lies in every basis
- **Manuscript proof status:** MANUSCRIPT_DEFINITION
- **Manuscript proof plan:** Identify coloops with elements of every full basis.
- **Lean declaration:** Matroid.IsColoop
- **Formalization source:** MATHLIB_EXACT
- **Mathlib declarations used:** Matroid.IsColoop; Matroid.isColoop_iff_forall_mem_isBase
- **Deviation from manuscript proof:** None.
- **Result:** COMPLETE
- **Build status:** `lake build` passed for completed declarations; blocked entries leave no unproved active declaration.
- **Notes:** No additional qualification.

## N023 — Restriction

- **Ledger ID:** N023
- **TeX label:** `def:matroid-minors`
- **Requirement:** M&#124;A has precisely the independent subsets of A from M
- **Manuscript proof status:** MANUSCRIPT_DEFINITION
- **Manuscript proof plan:** Restrict ground to A and retain precisely independent subsets of A.
- **Lean declaration:** Matroid.restrict
- **Formalization source:** MATHLIB_EXACT
- **Mathlib declarations used:** Matroid.restrict; Matroid.restrict_ground_eq; Matroid.restrict_indep_iff
- **Deviation from manuscript proof:** Mathlib intersects an arbitrary restriction parameter with the original ground; for `A ⊆ E` it is exactly A.
- **Result:** COMPLETE
- **Build status:** `lake build` passed for completed declarations; blocked entries leave no unproved active declaration.
- **Notes:** No additional qualification.

## N025 — Contraction rank

- **Ledger ID:** N025
- **TeX label:** `def:matroid-minors`
- **Requirement:** For X disjoint from A, r_{M/A}(X) = r_M(X ∪ A) − r_M(A)
- **Manuscript proof status:** MANUSCRIPT_DEFINITION
- **Manuscript proof plan:** For disjoint X and A, choose bases of A and X∪A extending the first; the residual basis computes contraction rank and its size is the difference.
- **Lean declaration:** (M ／ A).eRk X = M.eRk (X ∪ A) - M.eRk A (planned)
- **Formalization source:** FORMALIZATION_SOURCE_UNRESOLVED
- **Mathlib declarations used:** Matroid.contract; Matroid.IsBasis.contract_eq_contract_delete; Matroid.IsBasis.contract_sdiff_isBasis_sdiff; Matroid.IsBasis.eRk_eq_encard
- **Deviation from manuscript proof:** No project proof exists yet. The manuscript gives the equation as a definition, while mathlib defines contraction by dual deletion.
- **Result:** BLOCKED_PROOF
- **Build status:** `lake build` passed for completed declarations; blocked entries leave no unproved active declaration.
- **Notes:** No direct contraction-rank theorem was found in the pinned mathlib. The available basis-contraction results require a local finite-cardinality bridge for dependent A; that bridge is unfinished.

## N031 — Fundamental circuit

- **Ledger ID:** N031
- **TeX label:** `def:fundamental-circuit`
- **Requirement:** For a basis `B` and `e ∉ B`, `B∪{e}` contains a unique circuit
- **Manuscript proof status:** MANUSCRIPT_DEFINITION
- **Manuscript proof plan:** Adjoin a ground element outside a full basis; the resulting dependent set has one circuit, obtained as the fundamental circuit.
- **Lean declaration:** Matroid.fundCircuit
- **Formalization source:** MATHLIB_EXACT
- **Mathlib declarations used:** Matroid.fundCircuit; Matroid.IsBase.fundCircuit_isCircuit; Matroid.IsCircuit.eq_fundCircuit_of_subset
- **Deviation from manuscript proof:** Mathlib states the implicit manuscript condition `e ∈ E` explicitly.
- **Result:** COMPLETE
- **Build status:** `lake build` passed for completed declarations; blocked entries leave no unproved active declaration.
- **Notes:** No additional qualification.

## N042 — Matroid representation

- **Ledger ID:** N042
- **TeX label:** `def:matroid-representability`
- **Requirement:** Indexed vectors over a field represent a matroid iff their linearly independent indexed subfamilies are exactly its independent sets
- **Manuscript proof status:** MANUSCRIPT_DEFINITION
- **Manuscript proof plan:** Use indexed linear independence on each subset of E as the representation test; quantify over a field vector space and map for representability.
- **Lean declaration:** Matroid.Represents; Matroid.RepresentableOver
- **Formalization source:** LOCAL_PROOF
- **Mathlib declarations used:** LinearIndependent; Matroid.Indep
- **Deviation from manuscript proof:** No change to the independence criterion; the map is total on the ambient type but only its restriction to E matters.
- **Result:** COMPLETE
- **Build status:** `lake build` passed for completed declarations; blocked entries leave no unproved active declaration.
- **Notes:** The existential permits a vector-space carrier in a chosen Lean universe.

## N043 — Vector matroid

- **Ledger ID:** N043
- **TeX label:** `def:vector-matroid`
- **Requirement:** Any finite indexed vector family determines its dependence matroid
- **Manuscript proof status:** MANUSCRIPT_DEFINITION
- **Manuscript proof plan:** Show that the indexed linear-independent subfamilies obey finite matroid independent-set axioms, then construct their matroid.
- **Lean declaration:** Matroid.vectorMatroid (planned)
- **Formalization source:** FORMALIZATION_SOURCE_UNRESOLVED
- **Mathlib declarations used:** IndepMatroid.ofFinite; LinearIndependent
- **Deviation from manuscript proof:** No project construction exists yet.
- **Result:** BLOCKED_PROOF
- **Build status:** `lake build` passed for completed declarations; blocked entries leave no unproved active declaration.
- **Notes:** Pinned mathlib has no vector-matroid constructor. The finite augmentation proof for an arbitrary indexed family, including duplicate/zero vectors, remains to be implemented.

## N061 — Graphic matroid

- **Ledger ID:** N061
- **TeX label:** `def:graphic-cographic`
- **Requirement:** A graph’s graphic matroid has forests as independent sets
- **Manuscript proof status:** MANUSCRIPT_DEFINITION
- **Manuscript proof plan:** Take graph edges as ground and acyclic edge sets as independent; prove empty, hereditary, and forest augmentation.
- **Lean declaration:** Matroid.graphic (planned)
- **Formalization source:** FORMALIZATION_SOURCE_UNRESOLVED
- **Mathlib declarations used:** IndepMatroid.ofFinite; SimpleGraph (inspected)
- **Deviation from manuscript proof:** No project construction exists yet.
- **Result:** BLOCKED_IMPLEMENTATION
- **Build status:** `lake build` passed for completed declarations; blocked entries leave no unproved active declaration.
- **Notes:** Pinned mathlib has no graphic-matroid constructor. A graph/edge API allowing the manuscript’s finite graphs, including possible parallel edges and loops, and the forest augmentation proof are needed.

## N062 — Cographic matroid

- **Ledger ID:** N062
- **TeX label:** `def:graphic-cographic`
- **Requirement:** A graph’s cographic matroid has minimal nonempty edge cuts as circuits
- **Manuscript proof status:** MANUSCRIPT_DEFINITION
- **Manuscript proof plan:** Define the cographic matroid as the dual of a graphic matroid and identify its circuits with minimal nonempty edge cuts.
- **Lean declaration:** Matroid.cographic (planned)
- **Formalization source:** FORMALIZATION_SOURCE_UNRESOLVED
- **Mathlib declarations used:** Matroid.dual; Matroid.IsCocircuit
- **Deviation from manuscript proof:** No project construction exists yet.
- **Result:** BLOCKED_IMPLEMENTATION
- **Build status:** `lake build` passed for completed declarations; blocked entries leave no unproved active declaration.
- **Notes:** The graphic constructor and a cut-cocircuit bridge are absent. Defining only the dual would leave the manuscript’s edge-cut circuit characterization unchecked.

## N063 — Regular-matroid cycle

- **Ledger ID:** N063
- **TeX label:** `def:matroid-cycle`
- **Requirement:** A cycle is a disjoint union of circuits, including the empty set
- **Manuscript proof status:** MANUSCRIPT_DEFINITION
- **Manuscript proof plan:** Package an empty or finite pairwise-disjoint family of circuits and take its union.
- **Lean declaration:** Matroid.IsCircuitUnion
- **Formalization source:** LOCAL_PROOF
- **Mathlib declarations used:** Matroid.IsCircuit; Finset; Set.sUnion
- **Deviation from manuscript proof:** The definition applies to any matroid; the manuscript uses it for regular matroids, a valid specialization.
- **Result:** COMPLETE
- **Build status:** `lake build` passed for completed declarations; blocked entries leave no unproved active declaration.
- **Notes:** The empty Finset witnesses the empty cycle.

## N073 — Colored matroid

- **Ledger ID:** N073
- **TeX label:** `def:colored-matroid`
- **Requirement:** A matroid with an auxiliary element-label map; coloring does not change dependence, rank, closure, flats, or circuits
- **Manuscript proof status:** MANUSCRIPT_DEFINITION
- **Manuscript proof plan:** Pair a finite matroid with a map from its ground elements to colors; all matroid operations project to the underlying matroid.
- **Lean declaration:** Matroid.Colored
- **Formalization source:** LOCAL_PROOF
- **Mathlib declarations used:** Matroid; Matroid.Finite
- **Deviation from manuscript proof:** None; color has domain `matroid.E`.
- **Result:** COMPLETE
- **Build status:** `lake build` passed for completed declarations; blocked entries leave no unproved active declaration.
- **Notes:** Coloring does not alter the stored matroid.

## N080 — Finite closure-exchange representation

- **Ledger ID:** N080
- **TeX label:** `def:matroidal-query-system`
- **Requirement:** A finite extensive, monotone, idempotent closure satisfying Steinitz exchange is the closure of a matroid
- **Manuscript proof status:** MANUSCRIPT_STATEMENT_ONLY
- **Manuscript proof plan:** Define independent sets from a finite closure operator by excluding each element from the closure of the others; derive augmentation from exchange and recover the given closure.
- **Lean declaration:** Matroid.ofFiniteClosure (planned)
- **Formalization source:** FORMALIZATION_SOURCE_UNRESOLVED
- **Mathlib declarations used:** ClosureOperator; IndepMatroid.ofFinite
- **Deviation from manuscript proof:** No project construction exists yet.
- **Result:** BLOCKED_PROOF
- **Build status:** `lake build` passed for completed declarations; blocked entries leave no unproved active declaration.
- **Notes:** Pinned mathlib has no closure-axioms-to-matroid constructor. The exchange-to-augmentation theorem and the proof that the constructed closure equals the supplied operator remain open.

## N081 — Pointed matroid port

- **Ledger ID:** N081
- **TeX label:** unlabeled; material uses S: `prop:minimal-query-circuits`, `prop:positive-support-circuits`, `lem:r10-minimal-positive`
- **Requirement:** For a distinguished element `τ`, the minimal subsets of the other elements spanning `τ` are exactly the non-target parts of circuits through `τ`
- **Manuscript proof status:** MANUSCRIPT_STATEMENT_ONLY
- **Manuscript proof plan:** Use the circuit characterization of closure to get a circuit inside a minimal spanning set plus target; minimality makes its non-target part equal the set. Conversely a smaller spanning set would contain a circuit properly inside the original circuit.
- **Lean declaration:** Matroid.minimal_spanning_iff_circuit
- **Formalization source:** MATHLIB_BRIDGE
- **Mathlib declarations used:** Matroid.mem_closure_iff_exists_circuit_sdiff; Matroid.IsCircuit.mem_closure_sdiff_singleton_of_mem; Matroid.IsCircuit.eq_of_subset_isCircuit
- **Deviation from manuscript proof:** The cited manuscript prose gives the port correspondence without proof; Lean supplies the minimality argument.
- **Result:** COMPLETE
- **Build status:** `lake build` passed for completed declarations; blocked entries leave no unproved active declaration.
- **Notes:** Assumes the distinguished element is outside the set, as in the manuscript’s port.

## N105 — Positive target support

- **Ledger ID:** N105
- **TeX label:** `def:positive-support`
- **Requirement:** For a pointed matroid (M,τ) and A⊆E(M)\{τ} spanning τ, take the least cardinality of S⊆A with τ∈cl_M(S)
- **Manuscript proof status:** MANUSCRIPT_DEFINITION
- **Manuscript proof plan:** Take the infimum in natural numbers of sizes of target-spanning subsets of the available set; the available set itself witnesses nonemptiness.
- **Lean declaration:** Matroid.positiveTargetSupport
- **Formalization source:** LOCAL_PROOF
- **Mathlib declarations used:** Nat.sInf; Set.ncard; Matroid.closure
- **Deviation from manuscript proof:** The definition is the pure pointed-matroid part of the application-specific positive support.
- **Result:** COMPLETE
- **Build status:** `lake build` passed for completed declarations; blocked entries leave no unproved active declaration.
- **Notes:** Phase-A correspondence repair: the public argument now requires `A ⊆ M.E \ {τ}`, exactly matching the manuscript's available set and excluding the target. Finite M and this inclusion ensure candidate cardinalities are finite; hspan supplies a candidate.

## N122 — Weighted target basis sums

- **Ledger ID:** N122
- **TeX label:** unlabeled; material uses S: `thm:regular-matroid-energy`, `prop:seymour-one-sum`, `thm:seymour-two-sum`, `thm:r10-fixed-weight-evaluation`
- **Requirement:** For a pointed matroid with positive non-target weights, split the weighted basis generating sum into bases containing and omitting the target
- **Manuscript proof status:** MANUSCRIPT_DEFINITION
- **Manuscript proof plan:** Enumerate bases of the finite ground and partition the weighted products according to target membership, omitting target from each product.
- **Lean declaration:** Matroid.weightedBasesIn; Matroid.weightedBasesOut
- **Formalization source:** LOCAL_PROOF
- **Mathlib declarations used:** Set.Finite.toFinset; Finset.powerset; Finset.sum; Finset.prod; Matroid.IsBase
- **Deviation from manuscript proof:** The definitions admit arbitrary commutative-semiring weights; positive real non-target weights are the manuscript specialization.
- **Result:** COMPLETE
- **Build status:** `lake build` passed for completed declarations; blocked entries leave no unproved active declaration.
- **Notes:** No weight is assigned to the target in the product.

## N129 — Uniform matroid

- **Ledger ID:** N129
- **TeX label:** unlabeled; material uses S: `prop:grover-source-value`, `prop:grover-program-value`, `lem:r10-targeted-query-matroid`
- **Requirement:** U_{r,n} has independent sets exactly the subsets of cardinality at most r
- **Manuscript proof status:** MANUSCRIPT_STATEMENT_ONLY
- **Manuscript proof plan:** Use independent-set axioms for the family of subsets of E with cardinality at most r; augmentation selects an element from the larger independent set.
- **Lean declaration:** Matroid.uniformOn; Matroid.uniformOn_indep_iff
- **Formalization source:** LOCAL_PROOF
- **Mathlib declarations used:** IndepMatroid.ofFinite; Set.exists_mem_notMem_of_ncard_lt_ncard; Set.ncard_insert_of_notMem
- **Deviation from manuscript proof:** The manuscript uses uniform notation without a labeled definition; Lean constructs the generic finite object.
- **Result:** COMPLETE
- **Build status:** `lake build` passed for completed declarations; blocked entries leave no unproved active declaration.
- **Notes:** No constraint r≤|E| is needed for the independent-set characterization.

## N132 — Dual matroid bases

- **Ledger ID:** N132
- **TeX label:** unlabeled; material uses S: `def:graphic-cographic`, `prop:r10-proper-minors`, `prop:recursive-r10-closure`
- **Requirement:** Bases of M* are complements of bases of M
- **Manuscript proof status:** MANUSCRIPT_STATEMENT_ONLY
- **Manuscript proof plan:** Take complements in E of full bases to obtain exactly the dual bases.
- **Lean declaration:** Matroid.dual_isBase_iff
- **Formalization source:** MATHLIB_EXACT
- **Mathlib declarations used:** Matroid.dual; Matroid.dual_isBase_iff; Matroid.IsBase.compl_isBase_dual
- **Deviation from manuscript proof:** Mathlib supplies the standard dual-base statement implicit in the manuscript notation.
- **Result:** COMPLETE
- **Build status:** `lake build` passed for completed declarations; blocked entries leave no unproved active declaration.
- **Notes:** No additional qualification.

## N158 — Five 3-sum boundary classes

- **Ledger ID:** N158
- **TeX label:** unlabeled; material uses S: `lem:seymour-three-sum-five`, `prop:regular-triangle-identity`
- **Requirement:** For independent nontriangle `S` spanning after adjoining a coindependent triangle `T`, `cl(S)∩T` is empty, one of three singleton elements, or all of `T`
- **Manuscript proof status:** MANUSCRIPT_SKETCH
- **Manuscript proof plan:** Any two elements of the circuit triangle span the third; a subset of a three-element triangle therefore meets a closure in only the empty, singleton, or full classes.
- **Lean declaration:** Matroid.triangle_closure_five_classes
- **Formalization source:** LOCAL_PROOF
- **Mathlib declarations used:** Matroid.IsCircuit.mem_closure_sdiff_singleton_of_mem; Matroid.closure_subset_closure; Matroid.closure_closure
- **Deviation from manuscript proof:** The proof omits the manuscript’s independence, cospanning and coindependence hypotheses on S because the five-class conclusion follows from the triangle circuit alone.
- **Result:** COMPLETE
- **Build status:** `lake build` passed for completed declarations; blocked entries leave no unproved active declaration.
- **Notes:** The three named triangle elements are explicitly assumed distinct.

## N261 — TU row restriction

- **Ledger ID:** N261
- **TeX label:** unlabeled; material uses S: `thm:regular-matroid-energy`
- **Requirement:** Retaining a row basis from a column restriction of a TU matrix gives a full-row-rank TU matrix
- **Manuscript proof status:** MANUSCRIPT_SKETCH
- **Manuscript proof plan:** After restricting TU columns, select a basis of the row space; row deletion preserves TU and the retained rows span the deleted rows.
- **Lean declaration:** No Lean declaration
- **Formalization source:** FORMALIZATION_SOURCE_UNRESOLVED
- **Mathlib declarations used:** Matrix.IsTotallyUnimodular.submatrix; Matrix rank/row-space API
- **Deviation from manuscript proof:** The row deletion claim is matrix-theoretic; no matroid-facing formulation is fixed.
- **Result:** BLOCKED_SCOPE
- **Build status:** `lake build` passed for completed declarations; blocked entries leave no unproved active declaration.
- **Notes:** The precise statement belongs to a TU matrix/linear-algebra layer rather than the reusable matroid API. The manuscript also needs preservation of reconstruction under row compression, beyond TU preservation. Scope adjudication is required; dependency graph unchanged.

# Subject-module reorganization and blocker pass

Phase A moved the five existing rank/closure/circuit bridges from `Internal/Basic.lean` to `RankClosure.lean` and split `Internal/Frontier2.lean` into mathematical subject modules. Declaration names, statements, and proof bodies were preserved. The umbrella import now exposes these modules; `lake build` passed before blocker work. The historical pass-2 frontier snapshot was moved intact to `logs/formalization/FRONTIER_PASS_2.md`.

The manuscript definition `def:graphic-cographic` explicitly denotes the cographic matroid as the dual of the graphic matroid. The missing direct edge N061 → N062 was added to `DEPENDENCY_EDGES.csv` as `DEFINITIONAL`. Reinspection of the proof of `thm:regular-matroid-energy` confirms N261 is a TU matrix row-selection/compression step; its scope is now `OUT_OF_SCOPE_CONTEXT`, with the row retained for future matrix/TU work.

## Primary blocker outcomes

### N025

- **Ledger ID:** N025
- **TeX label:** `def:matroid-minors`
- **Requirement:** For X⊆E\A, finite contraction rank is r_M(X∪A)−r_M(A).
- **Manuscript proof status:** MANUSCRIPT_DEFINITION
- **Manuscript proof plan:** Choose a basis I of A and extend it to a basis J of A∪X. The residual J\I is a basis of X after contracting I. Contracting A further deletes A\I, disjoint from X; cardinality gives the rank difference.
- **Lean declaration:** Matroid.contract_rank_toNat_eq_sub
- **Formalization source:** MATHLIB_BRIDGE
- **Mathlib declarations used:** Matroid.exists_isBasis_subset_isBasis; Matroid.IsBasis.contract_sdiff_isBasis_sdiff; Matroid.IsBasis.contract_eq_contract_delete; Matroid.restrict_eRk_eq; Set.ncard_sdiff_add_ncard_of_subset
- **Deviation from manuscript proof:** Mathlib defines contraction by dual deletion; the proof bridges its basis API to the manuscript natural-rank formula using `eRk.toNat`.
- **Result:** COMPLETE
- **Downstream effect:** Discharges a prerequisite for 25 descendants, including 14 direct children.
- **Build status:** `lake build` passed.
- **Notes:** No alternative contraction definition was introduced.

### N043

- **Ledger ID:** N043
- **TeX label:** `def:vector-matroid`
- **Requirement:** A finite indexed vector family yields a matroid on E with exactly its linearly independent indexed subfamilies as independent sets.
- **Manuscript proof status:** MANUSCRIPT_DEFINITION
- **Manuscript proof plan:** Ground type is the vector index type α with ground set E. Independence is `I⊆E` plus `LinearIndepOn K φ I`. Empty and heredity follow from linear independence. For augmentation, if every element of a larger independent J lay in the span of I, then finrank of span J would be at most |I|, contradicting |I|<|J|.
- **Lean declaration:** Matroid.vectorMatroid; Matroid.vectorMatroid_indep_iff; Matroid.vectorMatroid_ground; Matroid.vectorMatroid_represents
- **Formalization source:** LOCAL_PROOF
- **Mathlib declarations used:** IndepMatroid.ofFinite; LinearIndepOn.insert; finrank_span_eq_card; Submodule.finrank_mono; finrank_range_le_card
- **Deviation from manuscript proof:** The map `φ : α → V` is total on the ambient index type, but only E is ground; duplicate and zero vectors remain indexed and become dependent as required.
- **Result:** COMPLETE
- **Downstream effect:** Discharges a prerequisite for 70 descendants, including 10 direct children.
- **Build status:** `lake build` passed.
- **Notes:** The result is a matroid using mathlib’s foundational type, with no axioms or placeholders.

### N061

- **Ledger ID:** N061
- **TeX label:** `def:graphic-cographic`
- **Requirement:** For a finite graph G, the ground set is its edges and independent edge sets are exactly those with no graph cycle.
- **Manuscript proof status:** MANUSCRIPT_DEFINITION
- **Manuscript proof plan:** Use mathlib `Graph α β` for vertices α and edge labels β; it supports loops and parallel edges. For a finite edge set, define independence as acyclicity of the edge-selected subgraph and prove the forest augmentation axiom.
- **Lean declaration:** No Lean graphic-matroid declaration
- **Formalization source:** FORMALIZATION_SOURCE_UNRESOLVED
- **Mathlib declarations used:** Graph; Graph.deleteEdges; Graph.IsBridge; SimpleGraph.IsAcyclic; IndepMatroid.ofFinite (inspected)
- **Deviation from manuscript proof:** No statement was weakened to simple graphs.
- **Result:** BLOCKED_MATHLIB_INFRASTRUCTURE
- **Downstream effect:** Still holds 22 descendants after the N061→N062 edge correction, including N062.
- **Build status:** `lake build` passed; no unproved declaration was left active.
- **Notes:** The pinned multigraph Graph API has edge cuts and bonds but no walk/cycle/forest predicate or forest exchange theorem. The SimpleGraph acyclicity API loses loops and parallel edges; a faithful augmentation proof requires new multigraph cycle/forest infrastructure.

### N062

- **Ledger ID:** N062
- **TeX label:** `def:graphic-cographic`
- **Requirement:** The cographic matroid is M(G)* on the same edge ground, with minimal nonempty edge cuts as circuits.
- **Manuscript proof status:** MANUSCRIPT_DEFINITION
- **Manuscript proof plan:** After constructing N061, take its mathlib matroid dual. Prove that graphic cocircuits coincide with graph bonds, giving the manuscript cut-circuit characterization.
- **Lean declaration:** No Lean cographic-matroid declaration
- **Formalization source:** FORMALIZATION_SOURCE_UNRESOLVED
- **Mathlib declarations used:** Matroid.dual; Matroid.IsCocircuit; Graph.IsBond (inspected)
- **Deviation from manuscript proof:** No dual of an unverified candidate was published.
- **Result:** BLOCKED_MATHLIB_INFRASTRUCTURE
- **Downstream effect:** Still holds 13 descendants; N061 is now an explicit direct prerequisite.
- **Build status:** `lake build` passed; no unproved declaration was left active.
- **Notes:** The graphic matroid has not been constructed, and the bond/cocircuit correspondence is not present in mathlib. N062 was assessed after N061 as required.

## Resulting active frontier

The current frontier was recomputed mechanically from the updated ledger and direct-edge CSV after all four primary targets were assessed. It has 196 active requirements, 29 complete requirements, and 30 unresolved nodes whose direct active prerequisites are complete. Seven frontier nodes were newly exposed by N025/N043. N062 is now held behind the corrected N061 → N062 edge; N261 is excluded after re-scoping. The complete current list and remaining descendant counts are in `Matroid/FRONTIER.md`. No newly exposed target was formalized in this pass.

# Structural-depth pass: shallow layer

The initial mechanical depth table had one complete depth-0 requirement and two unresolved depth-1 requirements, N061 and N080. The depth-2 set was not started because N061 remains active and unresolved. No dependency edge changed during this pass: the cut/cycle comparison below belongs to the proof of N061, rather than a distinct manuscript dependency.

## N061 — graphic matroid, depth 1

- **Ledger ID:** N061
- **Structural depth:** 1
- **TeX label:** `def:graphic-cographic`
- **Requirement:** A finite graph has a matroid on its edges whose independent sets are precisely the edge sets containing no graph cycle.
- **Manuscript proof status:** MANUSCRIPT_DEFINITION
- **Manuscript construction plan:** Use actual labeled edges as the ground type. A forest can be characterized by each selected edge admitting a cut isolating it from all other selected edges (the bridge criterion); show this agrees with absence of graph cycles, then establish matroid exchange.
- **Lean declaration:** `Graph.edgeCutMatroid`, `Graph.edgeCutMatroid_indep_iff` (partial construction).
- **Formalization source:** FORMALIZATION_SOURCE_UNRESOLVED for the full manuscript requirement; the cut-based partial construction is a LOCAL_PROOF.
- **Mathlib declarations used:** `Graph`, `Graph.edgeCut_symmDiff`, `Graph.edgeSet`, `Matroid.ofFiniteClosure`, `Matroid.SteinitzExchange`.
- **Deviation from manuscript route:** Exchange is established through symmetric differences of edge cuts and the N080 closure construction, avoiding a direct forest augmentation proof. The mathematical identification with cycle-free forests remains to be formalized.
- **Result:** BLOCKED_MATHLIB_INFRASTRUCTURE. The pinned multigraph `Graph` API provides cuts but no walk/cycle predicate or theorem that an edge cut isolating every selected edge is equivalent to absence of cycles. The candidate matroid is not asserted as N061 complete.
- **Build status:** `lake build` passed with the partial construction.
- **Notes:** The edge ground type is the subtype of `G.edgeSet`, retaining loops and parallel edge labels. The missing comparison is a proof-route bridge within N061, so no new canonical ledger row or direct edge was introduced.

## N080 — finite closure-exchange representation, depth 1

- **Ledger ID:** N080
- **Structural depth:** 1
- **TeX label:** `def:matroidal-query-system`
- **Requirement:** A finite closure operator satisfying Steinitz exchange is the closure of a matroid.
- **Manuscript proof status:** MANUSCRIPT_STATEMENT_ONLY
- **Manuscript proof plan:** Define independence by excluding each element from the closure of the remaining elements. Exchange preserves independence when an element lies outside the current closure. Extend independent sets maximally; their closures span the specified set. Minimal spanning sets satisfy basis exchange, so mathlib constructs a matroid. Finally use the exact independence predicate and matroid basis closure to recover the original closure on every set.
- **Lean declaration:** `Matroid.ofFiniteClosure`, `Matroid.ofFiniteClosure_indep_iff`, `Matroid.ofFiniteClosure_closure`.
- **Formalization source:** LOCAL_PROOF
- **Mathlib declarations used:** `ClosureOperator`, `Matroid.ofIsBaseOfFinite`, `Matroid.IsBasis.mem_of_insert_indep`, `Matroid.Indep.mem_closure_iff'`.
- **Deviation from manuscript route:** The manuscript states the query matroid's existence without proof. Lean supplies a finite basis-exchange construction. The query set is the finite index type (or the subtype of a finite query set), so the matroid ground is `univ` on that type.
- **Result:** COMPLETE; the construction and equality of closure operators are kernel checked.
- **Build status:** `lake build` passed.
- **Notes:** This proves both required obligations: matroid construction and exact recovery of the supplied closure. It adds no new foundational matroid type.

# N061 closure pass

- **Ledger ID:** N061
- **Structural depth:** 1
- **TeX label:** `def:graphic-cographic`
- **Requirement:** A finite graph has a matroid with ground set its edges, and an edge set is independent exactly when it contains no graph cycle.
- **Manuscript proof status:** MANUSCRIPT_DEFINITION
- **Manuscript construction plan:** A set contains a cycle exactly when some selected edge closes a finite walk through the other selected edges. This characterization covers loops (the remaining walk is empty) and parallel edges (the remaining walk has one edge). An edge does not close such a walk exactly when a graph cut isolates it from the other selected edges. Use the edge cuts to construct the matroid.
- **Lean declaration:** `Matroid.graphic`, `Matroid.graphic_ground`, `Matroid.graphic_indep_iff`; graph-side `Graph.ReachableOn`, `Graph.HasEdgeCycle`, `Graph.IsForestIn`, and loop/parallel-cycle lemmas.
- **Formalization source:** LOCAL_PROOF
- **Mathlib declarations used:** `Graph.edgeCut_symmDiff`, `Graph.IsLink.mem_edgeCut_iff`, `Relation.ReflTransGen`, `Matroid.ofFiniteClosure`, `Matroid.mapEmbedding`.
- **Deviation from manuscript route:** The manuscript gives the cycle-free independence definition without an axiom proof. Lean proves exchange via symmetric differences of cuts and finite closure exchange. Mathlib's multigraph API has no cycle predicate, so the formal forest predicate uses the equivalent edge-closes-a-walk criterion; a walk can be shortened to a simple path, and removing one edge from a usual cycle yields such a walk.
- **Result:** COMPLETE. The mapped matroid has ground set exactly `G.edgeSet`; `graphic_indep_iff` gives independence exactly for subsets with no edge-closing walk. Formal loop and parallel-edge lemmas check the cases a simple-graph model would miss.
- **Build status:** `lake build` passed (1602 jobs).
- **Notes:** The construction assumes a finite edge set, which follows from the manuscript's finite-graph hypothesis; vertex finiteness is unnecessary. The direct mathematical prerequisites remain as recorded; the proof-route cut and walk lemmas do not require a new ledger node or dependency edge. At the user's direction, no depth-2 target was attempted after N061 completed.

# Remaining structural depth-2 pass

The target snapshot is frozen in `FRONTIER.md`. Before searching mathlib, the statements and proof contexts were checked in the frozen manuscript: `def:matroid-minors`, `def:single-element-extension`, the prose after `def:vector-matroid`, `def:projective-equivalence`, `def:regular-matroid`, the proof of `thm:regular-quotient-form`, `def:graphic-cographic`, `prop:representation-scaling`, `prop:representation-coordinate-invariance`, `prop:grover-source-value`, `prop:grover-program-value`, `lem:r10-targeted-query-matroid`, `sec:introduction`, `sec:discussion`, and `prop:r10-regular-route-b`. The target's manuscript-source classification is the mathematical-provenance field below; no manuscript proof is attributed to an unlabeled standard fact. No direct dependency edge changed.

## N024 — deletion

- **Ledger ID:** N024; **Structural depth:** 2; **TeX label / manuscript location:** `def:matroid-minors`.
- **Requirement:** Deletion by `A` equals restriction to `E(M) \ A`.
- **Manuscript source status:** MANUSCRIPT_DEFINITION.
- **Mathematical proof or construction plan:** Identify the manuscript operation with mathlib's deletion on the same ground set.
- **Lean declaration:** `Matroid.deletion_eq_restriction`.
- **Formalization source:** MATHLIB_BRIDGE. **Mathlib declarations used:** `Matroid.delete_eq_restrict`.
- **Deviation from manuscript route:** None. **Result:** COMPLETE. **Build status:** `lake build` passed.
- **Notes:** No competing deletion operation was introduced.

## N036 — single-element extension

- **Ledger ID:** N036; **Structural depth:** 2; **TeX label / manuscript location:** `def:single-element-extension`.
- **Requirement:** A fresh target `τ` extends `N` exactly when the larger matroid has ground `insert τ N.E` and restricts to `N` on `N.E`.
- **Manuscript source status:** MANUSCRIPT_DEFINITION.
- **Mathematical proof or construction plan:** Package the three defining conditions as a predicate; neither existence nor Crapo classification is part of this definition.
- **Lean declaration:** `Matroid.IsSingleElementExtension`.
- **Formalization source:** LOCAL_PROOF (local definition). **Mathlib declarations used:** `Matroid.restrict`.
- **Deviation from manuscript route:** None. **Result:** COMPLETE. **Build status:** `lake build` passed.
- **Notes:** Loop and coloop extensions satisfy the same predicate when their restriction and ground conditions hold.

## N046 — represented circuits

- **Ledger ID:** N046; **Structural depth:** 2; **TeX label / manuscript location:** unlabeled prose immediately after `def:vector-matroid`; material uses in `prop:represented-minors`, `prop:span-program-matroid-shadow`, `prop:matroid-program-to-linear-span-program`, `prop:support-linear-characterization`, `thm:quotient-normal-form-correct`.
- **Requirement:** Circuits are minimal failures of linear independence of the *indexed* columns.
- **Manuscript source status:** EXTERNAL_UNCITED_STANDARD.
- **Mathematical proof or construction plan:** Combine the completed vector-matroid independence theorem with minimal dependence on subsets of the ground set.
- **Lean declaration:** `Matroid.vectorMatroid_isCircuit_iff`.
- **Formalization source:** MATHLIB_BRIDGE. **Mathlib declarations used:** `Matroid.isCircuit_iff_minimal_not_indep`, `Minimal`; local `vectorMatroid_indep_iff`.
- **Deviation from manuscript route:** None; the Lean statement keeps a subtype-indexed family, so equal columns and zero columns at distinct labels remain distinct. **Result:** COMPLETE. **Build status:** `lake build` passed.
- **Notes:** The explicit `C ⊆ E` hypothesis excludes off-ground sets.

## N047 — projective equivalence

- **Ledger ID:** N047; **Structural depth:** 2; **TeX label / manuscript location:** `def:projective-equivalence`.
- **Requirement:** Two representations of the same matroid over one field differ by a linear equivalence between their column spans and nonzero scalars on nonloop columns.
- **Manuscript source status:** MANUSCRIPT_DEFINITION.
- **Mathematical proof or construction plan:** Use submodule spans as the two linear-equivalence domains; require `ψ e = c e • T(φ e)` for nonloops; derive zero loop columns from representation.
- **Lean declaration:** `Matroid.ProjectivelyEquivalent`, `Matroid.Represents.loop_column_eq_zero`.
- **Formalization source:** LOCAL_PROOF. **Mathlib declarations used:** `Submodule.span`, `LinearEquiv`, `Matroid.singleton_not_indep`, `linearIndepOn_singleton_iff`.
- **Deviation from manuscript route:** Scalars are represented by a total function but nonzero and compatibility conditions apply only on ground-set nonloops. This avoids requiring arbitrary ambient spaces to be isomorphic. **Result:** COMPLETE. **Build status:** `lake build` passed.
- **Notes:** The zero-column lemma formally checks the manuscript's loop convention.

## N051 — regularity

- **Ledger ID:** N051; **Structural depth:** 2; **TeX label / manuscript location:** `def:regular-matroid`.
- **Requirement:** Representability over every field.
- **Manuscript source status:** MANUSCRIPT_DEFINITION.
- **Mathematical proof or construction plan:** Quantify over arbitrary field types using the existing `RepresentableOver` predicate.
- **Lean declaration:** `Matroid.Regular.{u,v,w}`.
- **Formalization source:** LOCAL_PROOF (local definition). **Mathlib declarations used:** `Field`; local `Matroid.RepresentableOver`.
- **Deviation from manuscript route:** Lean's universe parameters express the type universes for fields and representation spaces; no finite or fixed list of fields is substituted. **Result:** COMPLETE. **Build status:** `lake build` passed.
- **Notes:** This does not assert Tutte's TU characterization.

## N056 — TU pivot and standard form

- **Ledger ID:** N056; **Structural depth:** 2; **TeX label / manuscript location:** proof of `thm:regular-quotient-form`; further uses `thm:regular-support-bound`, `thm:regular-matroid-energy`.
- **Requirement:** A TU matrix representing a matroid can be permuted and normalized on a basis to `[I D]` while retaining TU.
- **Manuscript source status:** EXTERNAL_UNCITED_STANDARD.
- **Mathematical proof or construction plan:** Relabel basis columns, use their determinant `±1` to invert the basis block, then show every normalized minor is `0,±1` by a pivot-minor determinant identity.
- **Lean declaration:** `Matrix.isTotallyUnimodular_reindex_iff` supplies the permutation portion; no completed normalization theorem.
- **Formalization source:** FORMALIZATION_SOURCE_UNRESOLVED. **Mathlib declarations used:** `Matrix.reindex_isTotallyUnimodular`, `Matrix.IsTotallyUnimodular.submatrix`; the pinned TU file has no pivot-preservation theorem.
- **Deviation from manuscript route:** None asserted for the unfinished portion. **Result:** BLOCKED_PROOF. **Build status:** `lake build` passed with the verified permutation bridge only.
- **Notes:** Exact obstruction: prove the determinant identity for arbitrary minors after multiplying by the inverse unimodular basis block, including row and column indexing; a mere row permutation/submatrix fact does not imply it. This is matrix proof infrastructure within N056, not a newly discovered matroid prerequisite.

## N057 — TU identity augmentation

- **Ledger ID:** N057; **Structural depth:** 2; **TeX label / manuscript location:** displayed matrices `A=(I_r\;D)`, `K=(-D;I_{n-r})`, and `Â=(I_n\;K)` in the proof of `thm:regular-quotient-form`.
- **Requirement:** The concrete `K` and `Â` are TU whenever `D` is TU.
- **Manuscript source status:** EXTERNAL_UNCITED_STANDARD.
- **Mathematical proof or construction plan:** Prove sign reversal preserves TU, append an identity row block to `-D`, then append an identity column block to `K`.
- **Lean declaration:** `Matrix.IsTotallyUnimodular.neg`, `.kernelBlock`, `.augmentedKernelBlock`.
- **Formalization source:** MATHLIB_BRIDGE. **Mathlib declarations used:** `Matrix.fromRows_one_isTotallyUnimodular_iff`, `Matrix.one_fromCols_isTotallyUnimodular_iff`, `Matrix.det_neg`, `SignType.coe_mul`, `SignType.coe_pow`.
- **Deviation from manuscript route:** The adopted Lean statement uses `Matrix.fromRows` and `Matrix.fromCols` with `Sum` row indices for exactly the displayed block matrices. **Result:** COMPLETE. **Build status:** `lake build` passed.
- **Notes:** The proof establishes both manuscript TU claims; it does not assert the unrelated kernel-basis or regularity claims.

## N062 — cographic matroid

- **Ledger ID:** N062; **Structural depth:** 2; **TeX label / manuscript location:** `def:graphic-cographic`.
- **Requirement:** `M*(G)` is dual to the graphic matroid on the same labeled edges, and its circuits are precisely graph bonds.
- **Manuscript source status:** MANUSCRIPT_DEFINITION.
- **Mathematical proof or construction plan:** Characterize spanning in the cut-closure matroid by meeting every nonempty cut. Minimal nonspanning complements are minimal nonempty cuts. Transport circuits through the edge-label embedding and matroid duality.
- **Lean declaration:** `Matroid.cographic`, `cographic_ground`, `cographic_isCircuit_iff_isBond`; `Graph.edgeCutMatroid_spanning_iff`, `edgeCutMatroid_isCocircuit_iff`.
- **Formalization source:** LOCAL_PROOF. **Mathlib declarations used:** `Matroid.isCocircuit_iff_minimal_compl_nonspanning`, `Matroid.map_dual`, `Matroid.mapEmbedding_indep_iff`, `Graph.IsBond`.
- **Deviation from manuscript route:** The proof uses the N061 cut-closure construction rather than a separate graphic bond theorem. **Result:** COMPLETE. **Build status:** `lake build` passed.
- **Notes:** The formal graph is mathlib's `Graph α β`, with actual labeled edges as `G.edgeSet`; the construction and theorem retain loops and parallel edge labels. The bond theorem is on ambient edge labels, not only the edge subtype.

## N111 — nonzero column rescaling

- **Ledger ID:** N111; **Structural depth:** 2; **TeX label / manuscript location:** unlabeled matroid-side step at `prop:representation-scaling`, `prop:representation-coordinate-invariance`, `prop:regular-representations-are-weights`.
- **Requirement:** Independently scaling indexed columns by nonzero field elements preserves the vector matroid.
- **Manuscript source status:** EXTERNAL_UNCITED_STANDARD.
- **Mathematical proof or construction plan:** Convert nonzero scalars on the ground set to units and use invariance of indexed linear independence.
- **Lean declaration:** `Matroid.vectorMatroid_smul_eq`.
- **Formalization source:** MATHLIB_BRIDGE. **Mathlib declarations used:** `LinearIndependent.units_smul_iff`, `Matroid.ext_indep`.
- **Deviation from manuscript route:** None. **Result:** COMPLETE. **Build status:** `lake build` passed.
- **Notes:** The scalar hypothesis is only needed on actual ground elements. Loop columns remain zero under scaling.

## N112 — ambient linear isomorphism

- **Ledger ID:** N112; **Structural depth:** 2; **TeX label / manuscript location:** unlabeled matroid-side step at `prop:representation-scaling`, `prop:representation-coordinate-invariance`, `prop:regular-representations-are-weights`.
- **Requirement:** Applying a linear equivalence to every indexed column preserves the vector matroid.
- **Manuscript source status:** EXTERNAL_UNCITED_STANDARD.
- **Mathematical proof or construction plan:** Use injectivity of a linear equivalence to preserve and reflect linear independence on each indexed subset.
- **Lean declaration:** `Matroid.vectorMatroid_map_linearEquiv_eq`.
- **Formalization source:** MATHLIB_BRIDGE. **Mathlib declarations used:** `LinearMap.linearIndependent_iff`, `LinearMap.ker_eq_bot`, `Matroid.ext_indep`.
- **Deviation from manuscript route:** None; vectors need not span the ambient space. **Result:** COMPLETE. **Build status:** `lake build` passed.
- **Notes:** This is only the matroid statement; it makes no witness-energy claim.

## N130 — corank-one uniform target circuit

- **Ledger ID:** N130; **Structural depth:** 2; **TeX label / manuscript location:** unlabeled step at `prop:grover-source-value`, `prop:grover-program-value`, `lem:r10-targeted-query-matroid`.
- **Requirement:** In `U_{r,r+1}`, the full ground set is the unique circuit containing a distinguished target.
- **Manuscript source status:** EXTERNAL_UNCITED_STANDARD.
- **Mathematical proof or construction plan:** Every proper subset has cardinality at most `r` and is independent; the full set has cardinality `r+1` and is dependent. Any circuit must therefore equal the ground set.
- **Lean declaration:** `Matroid.uniformOn_isCircuit_iff_eq_ground`, `uniformOn_unique_target_circuit`.
- **Formalization source:** LOCAL_PROOF. **Mathlib declarations used:** `Matroid.isCircuit_iff_forall_ssubset`, `Set.ncard_lt_ncard`; local `uniformOn_indep_iff`.
- **Deviation from manuscript route:** None. **Result:** COMPLETE. **Build status:** `lake build` passed.
- **Notes:** The target theorem explicitly requires `τ ∈ E`.

## N258 — incidence representation of a graphic matroid

- **Ledger ID:** N258; **Structural depth:** 2; **TeX label / manuscript location:** cited incidence construction in `sec:introduction`; graphic program discussion in `sec:discussion`; use in `prop:r10-regular-route-b`.
- **Requirement:** Signed real incidence columns represent the graphic matroid, including loops and parallel labeled edges.
- **Manuscript source status:** EXTERNAL_CITED.
- **Mathematical proof or construction plan:** Choose ordered endpoints only for actual edges; use `δ_u−δ_v` as each edge column. A cycle supplies an alternating signed linear relation. Conversely, a nonzero finite linear relation among forest edges should vanish by a cut-isolation or leaf-elimination argument, yielding the N061 forest criterion.
- **Lean declaration:** `Graph.IsEdgeOrientation`, `exists_edgeOrientation`, `incidenceColumn`, `incidenceColumn_loop` (partial construction); no equality of vector and graphic matroids yet.
- **Formalization source:** FORMALIZATION_SOURCE_UNRESOLVED. **Mathlib declarations used:** `Graph.edge_mem_iff_exists_isLink`, `Graph.eq_or_eq_of_isLink_of_isLink`, `Finsupp.single`; pinned mathlib has `SimpleGraph.IncMatrix` but no corresponding labeled-multigraph signed-incidence independence theorem.
- **Deviation from manuscript route:** The partial code keeps distinct edge labels and uses real finitely supported vertex vectors. Off-ground labels receive zero, while the eventual representation statement must restrict to `G.edgeSet`. **Result:** BLOCKED_PROOF. **Build status:** `lake build` passed with the partial construction.
- **Notes:** Exact obstruction: prove, for every indexed `I ⊆ G.edgeSet`, `LinearIndependent ℝ (fun i : I => G.incidenceColumn ends i)` iff `G.IsForestIn I`; the forward cycle-relation and reverse cut-isolation arguments both remain to be formalized. The orientation is defined on the subtype of actual edges, so no nonempty ambient vertex type is assumed when the graph has no edges. This is the statement of N258 itself, not a newly discovered direct prerequisite.

# Dedicated N056 and N258 attack

The depth audit at the start of this focused pass found no unresolved active node at depth 0 or 1; N056 and N258 were the only unresolved depth-2 nodes. The exact manuscript source for N056 remains the standard-form step in the proof of `thm:regular-quotient-form` (also used by `thm:regular-support-bound` and `thm:regular-matroid-energy`). N258 remains the externally cited incidence construction in `sec:introduction`, with the graphic identification in `sec:discussion` and use at `prop:r10-regular-route-b`. No direct DAG edge changed and no depth-3 proof work was undertaken.

## N056 — focused result

- **Ledger ID:** N056. **Structural depth:** 2. **TeX label / manuscript location:** proof of `thm:regular-quotient-form`.
- **Requirement:** Basis pivoting and column permutation yield a totally unimodular standard form `[I D]` representing the same column matroid.
- **Manuscript source status:** EXTERNAL_UNCITED_STANDARD; the manuscript invokes the step without its proof.
- **Mathematical proof or construction plan:** Relabel basis columns, invert their nonsingular square block `B`, and write `B⁻¹A = [I, B⁻¹C]`. To finish, prove every minor of `B⁻¹C` is, up to the unit `det B`, a minor of the original TU matrix. This is the generalized pivot-minor determinant identity.
- **Lean declaration:** `Matrix.basisNormalize_eq_fromCols` proves the standard-form identity, `Matrix.basisNormalize_vectorMatroid_eq` proves the inverse basis-block row operation preserves the indexed column matroid, and `Matrix.basisNormalize_isTotallyUnimodular_iff` proves that TU of the normalized matrix is equivalent to TU of its nonbasis block. The earlier `Matrix.isTotallyUnimodular_reindex_iff` handles permutations.
- **Formalization source:** FORMALIZATION_SOURCE_UNRESOLVED for the full target. **Mathlib declarations used:** `Matrix.nonsing_inv_mul`, `Matrix.mul_fromCols`, `Matrix.one_fromCols_isTotallyUnimodular_iff`, `Matrix.reindex_isTotallyUnimodular`; local `Matroid.vectorMatroid_map_linearEquiv_eq` supplies representation preservation.
- **Deviation from manuscript route:** None. The checked reduction isolates, but does not assume, the TU claim.
- **Result:** BLOCKED_PROOF. The exact remaining step is `A.IsTotallyUnimodular → (B⁻¹ * C).IsTotallyUnimodular` when `B` is a nonsingular basis-column block of `A`. Pinned mathlib has Schur-complement and determinant-of-inverse infrastructure but no generalized pivot-minor identity or TU pivot theorem; a proof would require formal indexing of arbitrary complementary row and column subsets and the determinant sign.
- **Build status:** `lake build` passed with the checked partial results.
- **Notes:** This determinant lemma is matrix proof infrastructure internal to N056. It is not an omitted independent matroid prerequisite and no new canonical ledger node or DAG edge was added.

## N258 — focused result

- **Ledger ID:** N258. **Structural depth:** 2. **TeX label / manuscript location:** `sec:introduction`, `sec:discussion`, `prop:r10-regular-route-b`.
- **Requirement:** Real signed incidence columns have exactly the graph-cycle dependencies and represent the graphic matroid on finite labeled edges; the matroid is independent of edge orientations.
- **Manuscript source status:** EXTERNAL_CITED; the manuscript gives the incidence construction and identifies its graphic dependence but does not prove the linear-algebra theorem.
- **Mathematical proof or construction plan:** A selected edge closes a walk through the other edges exactly when its endpoint difference belongs to their column span. Signed columns are endpoint differences up to sign, and differences telescope along a walk. In the other direction, a forest edge admits an isolating graph cut; summing vertex coordinates on one side is a linear functional vanishing on the other selected columns and nonzero on that edge.
- **Lean declaration:** `Graph.not_linearIndepOn_incidence_of_cycle`, `Graph.linearIndepOn_incidence_of_forest`, `Graph.incidence_vectorMatroid_eq_graphic`, `Graph.incidence_represents_graphic`, `Graph.incidence_vectorMatroid_orientation_independent`.
- **Formalization source:** LOCAL_PROOF. **Mathlib declarations used:** `Finsupp.lsum`, `linearIndepOn_iff_notMem_span`, `Submodule.span_le`, `linearIndependent_equiv'`, `Matroid.ext_indep`; local `Graph.edgeCutMatroid_indep_iff_noEdgeCycle` and `Matroid.graphic_indep_iff`.
- **Deviation from manuscript route:** The proof uses the already established equivalent edge-closes-a-walk criterion for graph cycles and mathlib's labeled `Graph α β`. It does not restrict to `SimpleGraph`.
- **Result:** COMPLETE. The vector matroid of the incidence columns equals `Matroid.graphic G hE`, and a direct `Represents` theorem and orientation-independence theorem are kernel checked.
- **Build status:** `lake build` passed.
- **Notes:** Orientations are functions on the subtype of actual edge labels; this permits empty graphs even when ambient types contain unused labels. Parallel edges keep distinct labels, and the previously proved loop lemma gives their zero-column boundary case.

# N056 continuation — TU basis normalization closed

- **Ledger ID:** N056. **Structural depth:** 2. **TeX label / manuscript location:** proof of `thm:regular-quotient-form`; the same basis-pivot step is used in `thm:regular-support-bound` and `thm:regular-matroid-energy`.
- **Requirement:** A TU representation with chosen basis columns can be permuted and normalized to `[I D]`, retaining both total unimodularity and its indexed column matroid.
- **Manuscript source status:** EXTERNAL_UNCITED_STANDARD; the manuscript invokes the step without a proof.
- **Mathematical proof or construction plan:** For an arbitrary minor of `D = B⁻¹C`, select its columns `C_g` and rows `f`. Append to `[B C_g]` unit rows selecting `f`; the resulting block matrix `[B C_g; F 0]` is TU. Its Schur complement gives `det B · det(-D[f,g])`, hence this determinant is a sign because `det B` is a nonzero sign. Negation transfers the result to every minor of `D`.
- **Lean declaration:** `Matrix.IsTotallyUnimodular.basisNormalize_nonbasis` proves `D` TU; `Matrix.IsTotallyUnimodular.basisNormalize` proves the full normalized matrix TU; `Matrix.IsTotallyUnimodular.basisStandardForm` packages the `[I D]` identity, `D` TU, and preservation of the indexed vector matroid from linearly independent basis columns. `Matrix.IsTotallyUnimodular.basisNormalize_entry` records the Cramer-rule one-entry case.
- **Formalization source:** LOCAL_PROOF. **Mathlib declarations used:** `Matrix.IsTotallyUnimodular.fromRows_unitlike`, `Matrix.det_fromBlocks₁₁`, `Matrix.one_submatrix_mul`, `Matrix.invOf_eq_nonsing_inv`, `Matrix.linearIndependent_cols_iff_isUnit`, `Matrix.isUnit_iff_isUnit_det`, `Matrix.one_fromCols_isTotallyUnimodular_iff`; local `Matroid.vectorMatroid_map_linearEquiv_eq` supplies representation preservation.
- **Deviation from manuscript route:** The manuscript leaves basis pivoting implicit. The proof uses a TU unit-row augmentation and Schur complement to establish all normalized minors without choosing complementary index sets.
- **Result:** COMPLETE. The formerly missing TU implication is kernel checked; column permutations and representation preservation were already checked.
- **Build status:** `lake build` passed after this continuation.
- **Notes:** No new direct matroid prerequisite or DAG edge was found. The previous `BLOCKED_PROOF` entry documents the intermediate state; this continuation supersedes it.

# Depth-3 short bridges

The Phase-A N105 correspondence repair changed `Matroid.positiveTargetSupport` to require `A ⊆ M.E \ {τ}`. No local caller needed adjustment; the full build passed. Structural depths 0–2 remain complete. The frozen unresolved depth-3 set is N005, N027, N048, N052, N053, N064, N070, N125, N135, N181, N256.

## N005 — extension to a full basis

- **Ledger ID / depth / use labels:** N005, depth 3; `prop:cocircuit-separates-closure`, `prop:support-linear-characterization`, `prop:r10-proper-minors`.
- **Requirement / source:** Every independent set extends to a whole-matroid basis; EXTERNAL_UNCITED_STANDARD.
- **Proof plan and Lean declaration:** Invoke exact mathlib `Matroid.Indep.exists_isBase_superset`; `Matroid.Indep.exists_isBase_superset_manuscript` exposes the manuscript statement in `RankClosure.lean`.
- **Formalization source / result / build:** MATHLIB_EXACT; COMPLETE; `lake build` passed. No deviation or new prerequisite.

## N027 — deletion composition

- **Ledger ID / depth / use labels:** N027, depth 3; `thm:regular-matroid-energy`, `prop:seymour-two-sum-input-minors`, `prop:r10-proper-minors`, `prop:recursive-r10-closure`.
- **Requirement / source:** Sequential deletion of disjoint sets equals deletion of their union; EXTERNAL_UNCITED_STANDARD.
- **Proof plan and Lean declaration:** Exact mathlib `Matroid.delete_delete` proves the stronger unconditional identity; `Matroid.deletion_composition` records it in `Minors.lean`.
- **Formalization source / result / build:** MATHLIB_EXACT; COMPLETE; `lake build` passed. The extra generality does not change the manuscript use; no new prerequisite.

## N048 — represented restriction and deletion

- **Ledger ID / depth / statement label:** N048, depth 3; `prop:represented-minors`.
- **Requirement / source:** Restriction and deletion retain surviving indexed vectors; MANUSCRIPT_PROVED (the proof calls these cases immediate).
- **Proof plan and Lean declarations:** Compare independence on each subset using `Matroid.vectorMatroid_indep_iff` and mathlib `Matroid.restrict_indep_iff`/`Matroid.delete_eq_restrict`. `Matroid.vectorMatroid_restrict_eq` and `Matroid.vectorMatroid_delete_eq` preserve labels even when vector values repeat.
- **Formalization source / result / build:** MATHLIB_BRIDGE; COMPLETE; `lake build` passed. Represented contraction remains N049; no new prerequisite.

## N135 — graphic-cographic duality

- **Ledger ID / depth / use labels:** N135, depth 3; `def:graphic-cographic`, `prop:r10-proper-minors`, `prop:recursive-r10-closure`.
- **Requirement / source:** The cographic matroid is the dual of the graphic matroid; EXTERNAL_UNCITED_STANDARD.
- **Proof plan and Lean declaration:** `Graph.cographic` was already defined as the dual; `Graph.cographic_eq_dual_graphic` proves the exact equality by reflexivity.
- **Formalization source / result / build:** LOCAL_PROOF; COMPLETE; `lake build` passed. No new prerequisite.

## N181 — circuit persistence under deletion

- **Ledger ID / depth / use labels:** N181, depth 3; `prop:r10-no-three-sum`, `prop:r10-proper-minors`.
- **Requirement / source:** A circuit avoiding a deleted element remains a circuit; EXTERNAL_UNCITED_STANDARD.
- **Proof plan and Lean declaration:** A circuit avoiding `e` is disjoint from `{e}`; mathlib `Matroid.delete_isCircuit_iff` supplies the criterion. `Matroid.IsCircuit.of_avoids_deleted_element` records the manuscript form.
- **Formalization source / result / build:** MATHLIB_BRIDGE; COMPLETE; `lake build` passed. No new prerequisite.

# Depth-3 substantial targets and DAG correction

The initial depth-3 target set was frozen before proof work. Mathematical analysis of represented rank and field transfer added five direct edges to `DEPENDENCY_EDGES.csv`: N044→N053 (`def:regular-matroid`, unlabeled remark); N044→N070 (`def:r10` rank assertion); N053→N070 (`def:r10` regularity assertion); N044→N125 (`thm:regular-matroid-energy` and `prop:regular-triangle-identity` basis identification); N053→N052 (`def:regular-matroid` characterization, TU-to-regular direction). These are substantive dependencies rather than Lean helpers. Recomputed structural depths move N053/N125 to depth 5 and N052/N070 to depth 6. No depth-4 formalization was undertaken.

## N052 — Tutte characterization

- **Ledger ID / original depth / location:** N052, initially depth 3; unlabeled characterization after `def:regular-matroid`, used by `thm:regular-quotient-form`, `prop:regular-representations-are-weights`, and `thm:regular-matroid-energy`.
- **Requirement / manuscript source:** `Regular M ↔ ∃` real TU coordinate representation; EXTERNAL_CITED to Tutte and Oxley.
- **Mathematical plan:** The TU-to-regular direction is N053. The converse is Tutte's major regular-matroid characterization; it cannot be replaced by the forward direction.
- **Lean declaration / source / result:** No full Lean declaration. Pinned mathlib has no regular-matroid/Tutte characterization. FORMALIZATION_SOURCE_UNRESOLVED; MISSING_PREREQUISITE (N053) plus the cited converse theorem requiring substantial new local development. No local proof of the converse was attempted. No mathematical deviation or placeholder.
- **Build / graph:** The partial project builds. New direct edge N053→N052 raises N052 to depth 6.

## N053 — TU representation over every field

- **Ledger ID / original depth / location:** N053, initially depth 3; unlabeled remark after `def:regular-matroid`, used by `thm:regular-quotient-form` and `prop:regular-triangle-identity`.
- **Requirement / manuscript source:** The indexed column matroid of a TU matrix is unchanged over any field; EXTERNAL_UNCITED_STANDARD.
- **Mathematical plan:** Encode TU entries as integers, compare each square minor by `RingHom.map_det`, then use the represented-rank/minor criterion to transfer independent indexed sets. In characteristic two, `-1=1` remains nonzero.
- **Lean declaration / source / result:** `Matrix.IsTotallyUnimodular.intCast_minor_ne_zero_iff` proves the nonzero-minor transfer for integer TU matrices, including characteristic two. The missing formal step is the general rectangular-matrix independence criterion via nonzero maximal minors, which belongs to N044; a real TU matrix also needs an integer sign-entry lift. FORMALIZATION_SOURCE_UNRESOLVED; MISSING_PREREQUISITE, not COMPLETE. Pinned mathlib has no directly usable general minor criterion for indexed column independence in the searched matrix API.
- **Build / graph:** The partial result builds. New direct edge N044→N053 raises N053 to depth 5.

## N064 — regular one-sum construction

- **Ledger ID / depth / statement label:** N064, depth 3; `def:regular-matroid-sums`.
- **Requirement / manuscript source:** For disjoint nonempty ground sets, the 1-sum is the ordinary direct sum and its cycles are exactly `C₁ △ C₂` for summand cycles; MANUSCRIPT_DEFINITION.
- **Mathematical plan:** Use mathlib `Matroid.disjointSum`. Its independence criterion proves that each circuit of the sum belongs to exactly one side. Partition a finite pairwise-disjoint circuit family by side; conversely unite two such families. The two resulting cycle sets are disjoint because the ground sets are.
- **Lean declarations / source / result:** `Matroid.oneSum`, `oneSum_ground`, `oneSum_indep_iff`, `oneSum_isCircuit_iff`, and `oneSum_isCircuitUnion_iff` in `Sums.lean`; local proof using mathlib `Matroid.disjointSum_indep_iff` and `Matroid.Dep.exists_isCircuit_subset`. LOCAL_PROOF; COMPLETE. The proof uses the manuscript's `IsCircuitUnion`, not merely an independence-only direct sum.
- **Build / notes:** `lake build` passed. No new direct prerequisite. No 2- or 3-sum work was done.

## N070 — exact R10 object

- **Ledger ID / original depth / labels:** N070, initially depth 3; `def:r10`, `fig:r10-k33`.
- **Requirement / manuscript source:** The exact rank-five, ten-element regular vector matroid of the displayed matrix; MANUSCRIPT_DEFINITION.
- **Mathematical plan:** Store the integer matrix with row type `Fin 5` and column type `Fin 10`; cast to reals for the vector matroid. The index `i : Fin 10` is manuscript column `i` from left to right. The first five columns form the identity, giving the rank lower bound; represented rank gives the upper bound. TU of the displayed integer matrix plus N053 would prove regularity.
- **Lean declarations / source / result:** `Matroid.r10IntegerMatrix`, `r10Matrix`, `r10`, `r10_ground`, `r10_ground_card`, `r10IntegerMatrix_left`, `r10Matrix_left` in `R10.lean`. The exact matrix, labels, ten-element ground, and identity block are checked. Rank-five and regularity remain unproved; no atlas/certificate data was introduced. LOCAL_PROOF for the partial declarations; MISSING_PREREQUISITE for the full target.
- **Build / graph:** `lake build` passed. New direct edges N044→N070 and N053→N070 raise N070 to depth 6; a finite TU certificate for this matrix remains to be supplied when its prerequisites are ready.

## N125 — TU weighted basis determinant

- **Ledger ID / original depth / use labels:** N125, initially depth 3; `thm:regular-matroid-energy`, `prop:regular-triangle-identity`, `app:r10-atlas-response`.
- **Requirement / manuscript source:** For a full-row-rank TU real matrix `C` and positive weights `w`, `det(C diag(w) Cᵀ)` is the weighted sum over bases; EXTERNAL_CITED (Cauchy–Binet and the cited determinant representation).
- **Exact needed identity:** For finite row type of size `r` and finite column set, `det(C diag(w) Cᵀ) = ∑_{S, |S|=r} (det C[:,S])² · ∏_{e∈S} w_e`. TU changes each squared maximal minor to `0` or `1`; represented rank identifies the nonzero terms with bases. Positive weights are part of the manuscript setting, though the polynomial identity itself needs only commutative-ring weights.
- **Lean declaration / source / result:** `Matrix.IsTotallyUnimodular.det_submatrix_sq_of_ne_zero` proves the TU squared-minor component. Pinned mathlib has no directly named rectangular weighted Cauchy–Binet theorem in the searched matrix determinant API. The full identity is not yet proved; FORMALIZATION_SOURCE_UNRESOLVED and MISSING_PREREQUISITE (N044), plus determinant infrastructure.
- **Build / graph:** The partial lemma builds. New direct edge N044→N125 raises N125 to depth 5. No energy-ratio theorem was placed in Matroid.

## N256 — binary cycle symmetric difference

- **Ledger ID / depth / location:** N256, depth 3; prose after `def:matroid-cycle`, used by `def:regular-matroid-sums` and `lem:seymour-three-sum-five`.
- **Requirement / manuscript source:** Cycles, defined as finite disjoint unions of circuits, are closed under symmetric difference for a regular matroid; EXTERNAL_CITED.
- **Mathematical plan:** The manuscript's `def:matroid` assumes a finite ground set, so the eventual Lean closure theorem must include `M.Finite`. Instantiate regularity at `ZMod 2`. For an indexed binary representation, prove `IsCircuitUnion X` iff the sum of representing columns over `X` is zero. Each circuit has a minimal relation whose coefficients are all nonzero, hence all `1` over `ZMod 2`; disjoint unions sum to zero. Conversely, peel off a circuit from any nonempty zero-sum set and induct on finite cardinality. In characteristic two, the indicator of `X △ Y` is the sum of the indicators of `X` and `Y`; hence its column sum is zero, giving closure.
- **Lean declaration / source / result:** `Matroid.Regular.representableF2` and `Matroid.IsCircuitUnion.subset_ground` are checked. Pinned mathlib has no binary matroid/cycle-space API or ready circuit-union/kernel equivalence in the searched matroid files. The equivalence above remains a local proof obligation, so the requested closure is not proved. FORMALIZATION_SOURCE_UNRESOLVED; BLOCKED_PROOF. No conditional axiom or weakened circuit-only result was substituted.
- **Build / notes:** Partial declarations build. No new direct prerequisite or DAG edge was found; this is the current depth-3 blocker.

## N256 continuation — closed

- **Ledger ID / structural depth / location:** N256, depth 3; unlabeled prose immediately after `def:matroid-cycle`. The manuscript's finite-ground-set convention is stated in `def:matroid`.
- **Requirement / mathematical provenance:** Cycles of a regular matroid are closed under symmetric difference; EXTERNAL_CITED (`Seymour1980`, `Oxley2011`). A cycle remains the manuscript's finite disjoint union of circuits, including the empty union.
- **Mathematical proof:** In an indexed `ZMod 2` representation, linear independence is equivalent to every nonempty finite indexed subfamily having nonzero column sum. Minimal dependence then forces each circuit's full column sum to be zero. Conversely, a nonempty zero-sum set contains a circuit; removing it leaves another zero-sum set, so finite induction partitions the set into disjoint circuits. The sum over `X △ Y` is the sum over `X` plus the sum over `Y`, since the common columns occur twice and `2 = 0`. Regularity supplies the binary representation.
- **Lean declarations / source:** `Matroid.isCircuitUnion_iff_binary_sum_eq_zero` exposes the cycle-space characterization; `Matroid.Regular.isCircuitUnion_symmDiff` proves the manuscript conclusion under `[M.Finite]`. LOCAL_PROOF; COMPLETE. The supporting finite-index independence, circuit-removal, and symmetric-difference lemmas are private to `Cycles.lean`.
- **Mathlib support / deviation:** Uses `Fintype.linearIndependent_iff`, `Matroid.Dep.exists_isCircuit_subset`, `Matroid.IsCircuit.eq_of_not_indep_subset`, and finite-set sum identities. The Lean statement preserves the manuscript's indexed elements and finite matroid convention. No alternate cycle definition or conditional axiom was introduced.
- **Build / graph:** `lake build` passed with the closure theorem. No new substantive prerequisite, ledger ID, or dependency edge was needed. The earlier N256 blocker entry above records the prior state.

## Depth-3 correspondence cleanup: N048 and N005

- **N048, `prop:represented-minors`:** The previous implementation proved the restriction/deletion identities for the canonical `vectorMatroid E φ`. The manuscript states the result for an arbitrary representation `φ` of a finite matroid `M`. `Matroid.Represents.eq_vectorMatroid` now identifies `M` with that indexed vector matroid; `Matroid.Represents.restrict` and `Matroid.Represents.delete` apply the existing identities and expose the manuscript-facing conclusions. Equal or zero vector values retain distinct element labels. Represented contraction remains the separate N049 obligation. N048 remains `MATHLIB_BRIDGE`, `COMPLETE` after a successful full `lake build`.
- **N005 provenance:** Checked `prop:cocircuit-separates-closure`, `prop:support-linear-characterization`, and `prop:r10-proper-minors` against `Manuscript/main.tex`. The first two proofs extend an independent set to a whole-matroid basis. The `R10` proper-minors proof instead uses cited single-element minor identities, subsequent minor closure, and planarity; it has no basis-extension step. Removed `prop:r10-proper-minors` from the canonical N005 use list in `LEDGER.md`. The N005 Lean theorem and proof did not change.
- **Boundary audit:** The direct-edge DAG did not change. `DEPTHS.csv` was checked against the canonical ledger statuses and mechanically recomputed depths: 1/1 complete at depth 0, 9/9 at depth 1, 19/19 at depth 2, and 8/8 at depth 3. Minimum unresolved structural depth remains 4; no depth-4 target was worked on.

## Depth-4 pass: N044 represented rank

- **Ledger ID / structural depth:** N044 / 4.
- **Manuscript location / requirement:** Unlabeled rank formula immediately after `def:vector-matroid`: rank of `A` equals the dimension of the span of its indexed represented vectors. Uses include `prop:represented-minors` and `prop:support-linear-characterization`.
- **Manuscript source status:** EXTERNAL_UNCITED_STANDARD.
- **Mathematical proof plan:** Choose a basis `B` of `A`. Its represented vectors are independent. If a vector indexed by `A` were outside their span, adjoining its index would preserve independence, contradicting basis maximality. Thus both spans agree, and basis cardinality equals their finite dimension and matroid rank.
- **Lean declaration / formalization source:** `Matroid.Represents.eRk_eq_finrank_span` in `Representation.lean`; LOCAL_PROOF.
- **Mathlib declarations used:** `Matroid.exists_isBasis`, `Matroid.IsBasis.mem_of_insert_indep`, `finrank_span_eq_card`, `Matroid.isBasis_eRk_eq_ncard`.
- **Deviation from manuscript route:** None; the Lean theorem states the formula for arbitrary `Represents M φ`, finite `M`, and `A ⊆ M.E`. The set image spans vectors while independence remains indexed by ground elements.
- **Result / build status / notes:** COMPLETE. `lake build` passed after this theorem. No new direct prerequisite.

## Depth-4 pass: N067 one-sum preserves regularity

- **Ledger ID / structural depth:** N067 / 4.
- **Manuscript location / requirement:** Unlabeled “Each operation preserves regularity” after `def:regular-matroid-sums`, specialized to the 1-sum.
- **Manuscript source status:** EXTERNAL_CITED.
- **Mathematical proof plan:** Over each field, choose representations of the two regular summands. Put left and right columns into separate factors of `V × W`. Disjoint ground sets partition every indexed family, and its linear independence is equivalent to independence of both coordinate families.
- **Lean declarations / formalization source:** `Matroid.Represents.oneSum` and `Matroid.oneSum_regular` in `Sums.lean`; LOCAL_PROOF. The latter retains the field and representation-space universe parameters of `Matroid.Regular`.
- **Mathlib declarations used:** `Matroid.disjointSum_indep_iff`, `linearIndependent_sum`, `LinearIndependent.of_comp`, `linearIndependent_inl_union_inr'`, `linearIndependent_equiv'`.
- **Deviation from manuscript route:** None. The proof uses product coordinates and preserves edge indices, including repeated vector values.
- **Result / build status / notes:** COMPLETE. Pinned mathlib has no disjoint-sum representability theorem in its matroid API; a local representation construction was needed. `lake build` passed after the sum work.

## Depth-4 pass: N136 direct-sum bases

- **Ledger ID / structural depth:** N136 / 4.
- **Manuscript location / requirement:** Proof of `prop:seymour-one-sum`: every basis of the direct sum is the disjoint union of factor bases, supporting factorization of weighted basis sums.
- **Manuscript source status:** EXTERNAL_UNCITED_STANDARD.
- **Mathematical proof plan:** Restrict a whole-sum basis to each disjoint ground. Conversely, the union of factor bases is a whole-sum basis because its intersections with the two grounds recover the factors.
- **Lean declaration / formalization source:** `Matroid.oneSum_isBase_iff_exists` in `Sums.lean`; MATHLIB_BRIDGE.
- **Mathlib declarations used:** `Matroid.disjointSum_isBase_iff`, `Matroid.IsBase.eq_union_image_of_disjointSum`.
- **Deviation from manuscript route:** None; both directions and whole-matroid bases are stated.
- **Result / build status / notes:** COMPLETE. `lake build` passed after the sum work. No new direct prerequisite.

## Depth-4 pass: N176 planar graphic-cographic correspondence

- **Ledger ID / structural depth:** N176 / 4.
- **Manuscript location / requirement:** Proof of `prop:r10-proper-minors`, paragraph beginning “The graph `K_{3,3}` is minor-minimal nonplanar”: graphic matroids of planar graphs are cographic, and dually.
- **Manuscript source status:** EXTERNAL_CITED.
- **Mathematical proof plan:** A plane embedding supplies a dual graph with the same labeled edges. Minimal cycles of either graph are minimal nonempty edge cuts (bonds) of the other; circuit extensionality then gives both graphic-cographic equalities.
- **Lean declarations / formalization source:** `Graph.IsGraphCycle`, `Graph.graphic_isCircuit_iff_isGraphCycle`, `Graph.CycleBondDuality`, and `Graph.CycleBondDuality.matroid_correspondence` in `PlanarDuality.lean` prove the last combinatorial-to-matroid step; FORMALIZATION_SOURCE_UNRESOLVED for the full planar theorem.
- **Mathlib declarations used:** `Matroid.isCircuit_iff_forall_ssubset`, `Matroid.ext_isCircuit`, the project's `Matroid.graphic_indep_iff` and `Matroid.cographic_isCircuit_iff_isBond`.
- **Deviation from manuscript route:** The checked theorem is conditional on genuine cycle-bond graph duality data; it does not assert that a planar embedding produces these data. It is therefore not a proof of N176.
- **Result / build status / notes:** MISSING_PREREQUISITE. `lake build` passed for the conditional bridge. Added direct graph-theoretic prerequisite N268→N176. The exact missing step is production of an edge-corresponding dual graph with cycle-bond equivalence from a plane embedding of a finite labeled multigraph.

## Newly exposed prerequisite: N268 plane dual cycle-bond theorem

- **Ledger ID / structural depth:** N268 / 0 after DAG recomputation; split from N176 and blind M120.
- **Manuscript location / requirement:** The same proof paragraph of `prop:r10-proper-minors` invokes planar graph duality. Every finite plane-embedded labeled multigraph needs an edge-corresponding dual with cycles of each graph corresponding to bonds of the other.
- **Manuscript source status:** EXTERNAL_CITED.
- **Mathematical proof plan:** Define a plane embedding/rotation with faces for the existing `Graph α β`, build a dual graph on faces using the original edge labels, then prove both cycle-bond correspondences, including loops, bridges, and parallel edges.
- **Lean declaration / formalization source:** `Graph.CycleBondDuality` states the output interface; no plane-embedding-to-dual theorem exists. FORMALIZATION_SOURCE_UNRESOLVED.
- **Mathlib declarations used:** The pinned `Mathlib.Combinatorics.Graph` and `SimpleGraph` trees were inspected. Neither has the required plane embedding, face/dual graph construction, or cycle-cut duality; `SimpleGraph` also does not preserve this project's loop and parallel-edge semantics.
- **Deviation from manuscript route:** None in the requirement. The current interface is only conditional output data, not a definition of planarity.
- **Result / build status / notes:** BLOCKED_MATHLIB_INFRASTRUCTURE. `lake build` passes with the conditional interface. N268 is a genuine reusable mathematical prerequisite and has no direct matroid prerequisite; its structural depth is therefore 0. The new direct edge is N268→N176. Depth 5 was not attacked.

## N176 continuation — geometric statement and faces

- **Ledger ID / structural depth:** N176 / 4, with direct prerequisite N268 / 0; `prop:r10-proper-minors` is the material manuscript use.
- **Requirement / manuscript source status:** A finite planar graphic matroid is cographic, and dually; EXTERNAL_CITED. The manuscript's “planar graph” is now represented independently of any matroid conclusion by `Graph.PlaneEmbedding` and `Graph.IsPlanar`.
- **Mathematical proof plan:** Draw each labeled edge as a continuous path in `ℝ × ℝ`; require all edge interiors to be jointly injective and to avoid the drawn vertices. Form the faces as connected components of the complement. Assign each edge its two incident faces, form the face-incidence graph on the original edge labels, and prove that primal minimal cycles are dual bonds. The checked `CycleBondDuality.of_cycles_iff_bonds` derives the reverse correspondence by matroid duality, and `CycleBondDuality.matroid_correspondence` then gives N176.
- **Lean declarations / formalization source:** `Graph.PlaneEmbedding`, `Graph.IsPlanar`, `Graph.PlaneEmbedding.drawnSet`, `Graph.PlaneEmbedding.Face`, `Graph.PlaneEmbedding.faceIncidenceGraph`, `Graph.PlaneEmbedding.HasCycleBondFaceDual`, `Graph.CycleBondDuality.of_cycles_iff_bonds`, and `Graph.PlaneEmbedding.matroid_correspondence_of_faceDual` are in `PlanarDuality.lean`. LOCAL_PROOF for the auxiliary lemmas; FORMALIZATION_SOURCE_UNRESOLVED for N268 and N176.
- **Mathlib declarations used:** `Path`, `ConnectedComponents`, `Set.Finite.isClosed`, `isCompact_range`, and `isClosed_iUnion_of_finite`. The pinned mathlib source search found no graph-planarity, planar dual, or Jordan-curve theorem.
- **Checked supporting facts:** A drawn edge interior avoids all other edge endpoints; edge deletion preserves `IsPlanar` while retaining vertex positions and labels; a finite drawing has closed support and an open complement; the proposed face-incidence graph has exactly the original edge set. These statements elaborate and a full `lake build` passed.
- **Deviation / exact blocker:** `PlaneEmbedding.HasCycleBondFaceDual` is deliberately separate from `IsPlanar`; it is the unproved N268 theorem, not a hidden planarity hypothesis. Producing the two incident complementary faces of each edge, and proving that every primal minimal cycle is a dual bond and conversely, requires planar separation/Jordan-style topology absent from the pinned library. The reverse dual-cycle/primal-bond clause is now checked as a consequence of the first clause and finite matroid duality. N176 remains `MISSING_PREREQUISITE`; N268 remains `BLOCKED_MATHLIB_INFRASTRUCTURE`. No depth-5 work was done.

## N176 further continuation — genuine face incidence

- **Ledger ID / depth / location:** N176 / 4, prerequisite N268 / 0; `prop:r10-proper-minors`.
- **Requirement / source status:** Planar graphic-cographic correspondence, EXTERNAL_CITED. The independent `Graph.IsPlanar` predicate still requires only a crossing-free drawing.
- **Mathematical refinement:** For finite drawings, the complement is open and locally path connected. Two points have the same complementary face exactly when a path in the complement joins them; each face occupies an open set in the plane. `PlaneEmbedding.FaceIncident e f` now means the region of face `f` approaches an interior point of edge `e`. `HasCycleBondFaceDual` requires both chosen faces of every dual edge to satisfy this geometric incidence relation, in addition to cycle-bond duality. This prevents an arbitrary face assignment from being mistaken for a geometric dual.
- **Lean declarations / source:** `PlaneEmbedding.faceRegion_locallyPathConnected`, `sameFace_iff_joined`, `facePoints`, `isOpen_facePoints`, and `FaceIncident` in `PlanarDuality.lean`; LOCAL_PROOF for these support results, FORMALIZATION_SOURCE_UNRESOLVED for N268/N176.
- **Mathlib declarations:** `IsOpen.locallyPathConnectedSpace`, `connectedComponent_eq_iff_joined`, `ConnectedComponents.coe_eq_coe`, `isOpen_connectedComponent`, and open-subtype image lemmas.
- **Deviation / exact blocker / result:** No change to the manuscript theorem. The unproved N268 theorem must show that each edge has incident complementary faces and that, using those actual faces, primal minimal cycles are exactly dual bonds. Proving incidence existence already needs a local side theorem for an embedded arc; the cycle-bond claim needs planar separation of an embedded cycle. No compatible Jordan-curve/local separation theorem was found in pinned mathlib. N268 remains `BLOCKED_MATHLIB_INFRASTRUCTURE`, N176 `MISSING_PREREQUISITE`; `lake build` is required before any status change. No depth-5 work was done.

## N268 continuation — face boundaries and exact geometric gap

- **Ledger ID / structural depth:** N268 / 0, direct prerequisite of N176 / 4.
- **Manuscript location:** `prop:r10-proper-minors`, proof paragraph asserting that a graphic matroid represented by a planar graph is also cographic, and dually.
- **Requirement / mathematical proof plan:** For a finite crossing-free drawing, assign to each edge two complementary faces approached by its interior. For every edge set `C`, prove that `C` is a minimal graph cycle exactly when it is an inclusion-minimal nonempty boundary `{e : (leftFace(e) ∈ S) ≠ (rightFace(e) ∈ S)}` for some set `S` of faces. Local separation of embedded arcs is needed to produce the face assignment; planar separation of embedded cycles is needed for the boundary characterization.
- **Lean declarations / source:** `PlaneEmbedding.faceBoundary`, `PlaneEmbedding.faceIncidenceGraph_edgeCut_eq_faceBoundary`, `PlaneEmbedding.IsMinimalFaceBoundary`, `PlaneEmbedding.faceIncidenceGraph_isBond_iff_minimalFaceBoundary`, and `PlaneEmbedding.hasCycleBondFaceDual_iff_minimalFaceBoundary` in `PlanarDuality.lean` are checked local reductions. The final geometric existence/separation theorem remains `FORMALIZATION_SOURCE_UNRESOLVED`.
- **Mathlib declarations used:** `Graph.edgeCut`, `Graph.IsBond`, `Graph.IsLink.mem_edgeCut_iff`, `Graph.edgeCut_subset_edgeSet`, and `Minimal`.
- **Deviation from manuscript route / result:** No mathematical weakening. The checked equivalence removes graph-cut and matroid bookkeeping from the open theorem. Pinned mathlib has no compatible Jordan curve or local arc-side theorem; no proof of face assignment or minimal-boundary characterization was found. N268 stays `BLOCKED_MATHLIB_INFRASTRUCTURE`, and N176 stays `MISSING_PREREQUISITE`. No depth-5 work was attempted.

## N268 continuation — isolating a drawn subarc

- **Ledger ID / structural depth:** N268 / 0, direct prerequisite of N176 / 4.
- **Manuscript location:** `prop:r10-proper-minors`, the proof's planar graphic-cographic step.
- **Requirement / mathematical proof plan:** Before applying local plane separation, isolate an interior point of one edge from every other edge, every drawn vertex, and all distant parameter values of that same edge. Compactness of finite edge paths supplies an open plane neighborhood for any prescribed open parameter neighborhood. This works for loops, whose two endpoints may coincide.
- **Lean declarations / source:** `PlaneEmbedding.interior_unique_preimage`, `otherDrawnSet`, `isClosed_otherDrawnSet`, `interior_not_mem_otherDrawnSet`, `exists_isolated_edge_neighborhood`, `exists_edge_parameter_neighborhood`, and `exists_isolated_subarc_neighborhood` in `PlanarDuality.lean` are checked local proofs.
- **Mathlib declarations used:** `isCompact_range`, `IsClosed.isCompact`, `IsCompact.image`, `IsCompact.isClosed`, and finite union/closedness lemmas.
- **Deviation / exact blocker / result:** The isolation argument uses finite vertex and edge sets. Finiteness of edges alone is insufficient to ensure the vertex drawing is closed, so a future geometric N268 theorem should carry both finiteness hypotheses. Isolation does not establish that the complement has two local sides or that an embedded cycle separates the plane; those are the remaining topology steps. N268 remains `BLOCKED_MATHLIB_INFRASTRUCTURE`, N176 remains `MISSING_PREREQUISITE`, and depth 5 was not attacked.

## N268 continuation — conditional existence of an incident face

- **Ledger ID / structural depth:** N268 / 0, required by N176 / 4.
- **Manuscript location:** `prop:r10-proper-minors`, proof's planar graphic-cographic sentence.
- **Requirement / mathematical proof plan:** The complementary face regions cover the drawing's complement. For a finite vertex and edge drawing, if each embedded edge path has dense complement, then the drawing's complement is dense by finite nowhere-dense union. If the face type is also finite, closure of the finite union of face regions covers the plane. Every edge interior point therefore lies in the closure of at least one face region.
- **Lean declarations / source:** `PlaneEmbedding.iUnion_facePoints`, `dense_compl_of_edge_ranges_dense`, `exists_face_closure_of_dense_compl`, `exists_incident_face_of_dense_compl`, and `exists_incident_face_of_edge_ranges_dense` in `PlanarDuality.lean` are checked local implications. They do not prove their arc-density or face-finiteness hypotheses for all plane embeddings.
- **Mathlib declarations used:** `Set.Countable.dense_compl`, `IsNowhereDense.iUnion`, `isClosed_isNowhereDense_iff_compl`, and `closure_iUnion_of_finite`.
- **Deviation / exact blocker / result:** No manuscript statement was weakened. The remaining geometric work includes proving that every embedded edge path has empty interior, proving finiteness of the complementary face set, identifying the two local sides of each edge, and proving the cycle/minimal-face-boundary equivalence. The checked existence theorem yields one incident face under its stated assumptions; it does not prove distinct sides or cycle-bond duality. N268 remains `BLOCKED_MATHLIB_INFRASTRUCTURE`, N176 remains `MISSING_PREREQUISITE`; depth 5 was not attacked.

## N268 continuation — exact cycle/boundary decomposition

- **Ledger ID / structural depth:** N268 / 0, prerequisite of N176 / 4.
- **Manuscript location:** `prop:r10-proper-minors`, planar graphic-cographic step in the proof.
- **Requirement / mathematical proof plan:** For assigned incident faces of a finite plane drawing, split the cycle–bond theorem into two geometric claims: (1) each primal minimal cycle is the boundary of a partition of complementary faces; (2) every nonempty boundary of a face partition contains a primal minimal cycle. Claim (1) is the cycle-separation direction. Claim (2) rules out spurious dual bonds. Minimality of cycles and a finite minimal-boundary argument prove that these two claims are jointly equivalent to the full cycle/minimal-face-boundary condition.
- **Lean declarations / source:** `PlaneEmbedding.faceBoundary_subset_edgeSet`, `isGraphCycle_iff_minimalFaceBoundary_of_geometric_conditions`, `cycles_iff_minimalFaceBoundary_iff_geometric_conditions`, and `hasCycleBondFaceDual_iff_geometric_conditions` in `PlanarDuality.lean` are checked local reductions. They do not prove the geometric claims.
- **Mathlib declarations used:** `Set.Finite.finite_subsets`, `Set.Finite.exists_minimal`, `Minimal.eq_of_subset`, and graphic circuit nonemptiness.
- **Attempted topology route / exact blocker:** An embedded edge path should have empty interior: if an open disk lay in its image, a small punctured disk around an interior path point would connect the two sides of the locally isolated subarc. Pinned mathlib has connectedness of the whole punctured plane and of an unpunctured ball, but the searched library provides no direct local punctured-ball or arbitrary embedded-arc interior theorem. A proof of this route would still need finite-face and Jordan-style cycle separation arguments. N268 remains `BLOCKED_MATHLIB_INFRASTRUCTURE`, N176 remains `MISSING_PREREQUISITE`; no depth-5 work was attempted.

## N268 continuation — the unique exterior face

- **Ledger ID / structural depth:** N268 / 0, prerequisite of N176 / 4.
- **Manuscript location:** `prop:r10-proper-minors`, the planar graphic-cographic step.
- **Requirement / mathematical proof plan:** A finite plane drawing has compact support, hence lies inside a disk. The exterior of that disk is path connected: move each point around its radius circle and then along a radial segment. Its points therefore lie in one complementary face. Any other unbounded face would meet the exterior and coincide with that face.
- **Lean declarations / source:** `PlaneEmbedding.isCompact_drawnSet`, `exists_outer_circle`, `sameFace_on_avoiding_circle`, `exists_outer_face`, `exists_unbounded_face`, and `existsUnique_unbounded_face` in `PlanarDuality.lean` are checked local proofs. The private `plane_radialJoined` and `plane_outerRegion_pathConnected` prove the required exterior connectivity.
- **Mathlib declarations used:** `isCompact_iUnion`, compact-set boundedness, `isPathConnected_sphere`, `JoinedIn.ofLine`, `JoinedIn.mono`, `ConnectedComponents.coe_eq_coe`, and `NormedSpace.unbounded_univ`.
- **Deviation / exact blocker / result:** This identifies a genuine exterior face without assuming the face type is finite. It does not identify the local faces on each edge, prove that arbitrary embedded arcs have empty interior, or establish either cycle/face-boundary separation claim. N268 remains `BLOCKED_MATHLIB_INFRASTRUCTURE`, N176 remains `MISSING_PREREQUISITE`; depth 5 was not attempted.

## N268 continuation — faces under edge deletion

- **Ledger ID / structural depth:** N268 / 0, prerequisite of N176 / 4.
- **Manuscript location / requirement:** `prop:r10-proper-minors`, proof paragraph using planar graphic-cographic duality after taking a proper minor of `M(K_{3,3})`; current ledger provenance `EXTERNAL_CITED` is flagged for review below.
- **Mathematical proof plan:** For an inductive plane-duality proof, deleting graph edges removes their drawn paths and enlarges the plane complement. Inclusion of complements sends each old connected face into a well-defined new face. If the old complement is dense, every new face contains an old-complement point because finite-drawing face regions are open; hence this face map is surjective. Unboundedness of a face is preserved by inclusion, and a face incident with a surviving edge remains incident after deletion.
- **Lean declarations / formalization source:** `PlaneEmbedding.deleteEdges_drawnSet_subset`, `complementInclusion_deleteEdges`, `continuous_complementInclusion_deleteEdges`, `faceMap_deleteEdges`, `faceMap_deleteEdges_mk`, `facePoints_subset_deleteEdges`, `faceMap_deleteEdges_unbounded`, `faceMap_deleteEdges_surjective`, and `faceIncident_deleteEdges` in `PlanarDuality.lean`; LOCAL_PROOF for these supporting facts. N268 itself remains FORMALIZATION_SOURCE_UNRESOLVED.
- **Mathlib declarations used:** `ConnectedComponents.coe_eq_coe'`, `Continuous.mapsTo_connectedComponent`, `ConnectedComponents.surjective_coe`, `Dense.exists_mem_open`, and `Bornology.IsBounded.subset`.
- **Deviation / exact blocker / result:** Surjectivity is conditional on density of the original drawing complement; the proof does not assume or derive that every embedded edge path has empty interior. It gives no bound on how many old faces can merge after one deletion. Local edge-side separation and the primal-cycle/face-boundary equivalence are still open. N268 remains `BLOCKED_MATHLIB_INFRASTRUCTURE`, N176 remains `MISSING_PREREQUISITE`; depth 5 was not attempted. `lake build` passed.

## N268 reference audit — Oxley, Proposition 5.2.1

- **Ledger ID / structural depth / manuscript location:** N268 / 0, used by N176 / 4 in the proof of `prop:r10-proper-minors`.
- **External mathematical baseline:** Oxley, *Matroid Theory* (2nd ed.), Proposition 5.2.1 states that the cycle matroid of a geometric dual of a planar graph is isomorphic to the dual of the original cycle matroid. Lemma 2.3.7 proves the connected case and explicitly uses Jordan-curve separation to send primal circuits to dual cuts; Proposition 5.2.1 extends it to disconnected graphs by splitting components and using matroid direct sums. Section 2.3 defines the geometric dual from complementary faces, including a dual loop when an edge borders only one face. Source: <https://www.math.ens.psl.eu/~benoist/refs/Oxley.pdf>, pp. 89–91 and 140.
- **Relation to the Lean requirement:** The checked `CycleBondDuality.matroid_correspondence` already proves the matroid conclusion once an edge-corresponding cycle–bond dual pair is supplied. Oxley's proposition assumes that a geometric dual exists; its earlier geometric-dual construction and connected-case Jordan argument identify the work still needed to obtain that pair from `Graph.PlaneEmbedding`. The source confirms the standard theorem but is not a kernel-checked replacement for N268.
- **Provenance review:** The manuscript's explicit `\cite[Lem.~6.6.9]{Oxley2011}` in `prop:r10-proper-minors` attaches to the two single-element minor identities. Its later planar graphic-cographic sentence has no local citation. The ledger currently says `EXTERNAL_CITED` for N268 and N176; under the manuscript-local provenance rule, `EXTERNAL_UNCITED_STANDARD` is a candidate correction for review. The preserved ledger was not changed here.
- **Result:** No Lean theorem or status changed. N268 remains `BLOCKED_MATHLIB_INFRASTRUCTURE`; N176 remains `MISSING_PREREQUISITE`. No depth-5 work was attempted.

## N268 continuation — imported Jordan infrastructure and checked edge bridges

- **Ledger IDs / depth / manuscript evidence:** N268 / 0 is required by N176 / 4 in the proof of `prop:r10-proper-minors`. The planar graphic/cographic sentence follows the citation for the single-element `R₁₀` minor identities; that citation is not expressly attached to planar duality. Proposed mathematical provenance for both planar rows: `EXTERNAL_UNCITED_STANDARD`, pending ledger adjudication.
- **External Lean source:** Pinned `jordan_pick` revision `b3c9b7cf7358bf81a077d78ad67e6e8247869ddd` (Apache-2.0). The package's Lean 4.33.0 source builds here with Lean 4.35.0-rc3 and the project's pinned mathlib. Exact declarations and trust check are in `SOURCES.md`; the dependency is recorded in `lakefile.toml` and `lake-manifest.json`.
- **Checked local declarations:** `JordanPath.exists_jordanTrace` factors a simple closed path through `AddCircle 1` and the sphere used by the imported Jordan theorem. `Graph.jordanCurve_complement_card` and `Graph.jordanCurve_component_boundary` transport the two-component and whole-boundary theorems to `ℝ × ℝ`. `PlaneEmbedding.edgePath_injective_of_nonloop`, `edgeArcHomeomorph`, and `isConnected_compl_edgePath_of_nonloop` show that an individual nonloop edge is an arc whose complement is connected. `PlaneEmbedding.loopEdge_hasJordanTrace` and `loopEdge_complement_card` establish the Jordan trace and two complementary components for an individual loop edge. The face-boundary transport is stated conditionally for any `HasJordanTrace`.
- **Remaining exact obligations:** `Graph.IsGraphCycle` is a minimal `HasEdgeCycle` set of labeled edges. Extracting an ordered simple cyclic walk from its reachable-edge witness, concatenating the associated paths, and proving the concatenation injective modulo its endpoints is still missing for cycles of two or more edges. Even with a Jordan trace, the two components of the complement of the cycle support are not automatically the faces of the **full** drawing. N268 still needs incident-face assignment at each edge, the local-side/crosscut argument with the other drawn edges present, and both geometric clauses of `hasCycleBondFaceDual_iff_geometric_conditions` (every primal cycle is a face boundary; every nonempty face boundary contains a primal cycle). Jordan separation alone does not identify those boundaries.
- **Crosscut reconnaissance:** `schoenflies-lean` provides a general crosscut theorem, but pins Lean 4.32.2. It was inspected as a possible source, not imported or ported. Its compatibility and precise ability to discharge the full-drawing local-side step remain unverified.
- **Result:** The full `lake build` passes for the Jordan dependency and the path/edge bridges. N268 is not proved, so N176 remains dependent on it. `DEPTHS.csv` and the baseline ledger retain their unresolved statuses; the previous `BLOCKED_MATHLIB_INFRASTRUCTURE` label now describes the remaining graph-to-topology and crosscut integration, not absence of a Jordan theorem. No depth-5 work was attempted.

## N268 continuation — exact closed trace of a labeled graph cycle

- **Ledger ID / location:** N268 / depth 0, prerequisite of N176 / depth 4; the material manuscript use remains the proof of `prop:r10-proper-minors`.
- **Checked graph-to-topology bridge:** `Matroid/Internal/CycleWalkTrace.lean` converts each `Graph.LinkedOn` witness into the forward or reverse drawn edge path, retaining its edge label and image. Induction over `Graph.ReachableOn` constructs a continuous path and records exactly the traversed edge set. For `G.IsGraphCycle C`, minimality forces the traversed edge set plus the closing edge to equal `C`; `PlaneEmbedding.isGraphCycle_closedPath_exactSupport` therefore gives `∃ x p : Path x x, range p = P.edgeSupport C` without finiteness or simplicity assumptions beyond `IsGraphCycle` and `PlaneEmbedding`.
- **Minimal connecting set:** `isGraphCycle_reachableEdges_minimal` proves that the edge set of such a connecting witness cannot be reduced while still joining the closing edge's endpoints. This is the exact graph-theoretic premise needed to extract a simple labeled walk; it does not itself show that an arbitrarily concatenated parameterization is injective, since a witness may include backtracking.
- **Completed special case:** `isGraphCycle_eq_singleton_of_loop` shows that a minimal cycle containing a loop consists only of that edge. `PlaneEmbedding.graphCycle_hasJordanTrace_of_loop` then supplies the imported Jordan trace for every loop cycle, with no extra planarity or simplicity hypothesis.
- **Remaining exact gap:** For a nonloop cycle, select or normalize a labeled connecting walk from the minimal reachable edge set so that its vertices are distinct, then prove the concatenated edge path injective on `[0,1)` and apply `PlaneEmbedding.hasJordanTrace_of_simpleClosedPath`. The existing edge-interior uniqueness and vertex-avoidance axioms should handle geometric injectivity once that combinatorial order is available. Even after this trace, N268 still requires incident faces of the full drawing and the cycle/minimal-face-boundary separation theorem. N176 remains `MISSING_PREREQUISITE`.
- **Result:** Full `lake build` passed; no `sorry`, `admit`, or `axiom` was added. N268 and N176 remain unresolved at their recorded depths, so the ledger and `DEPTHS.csv` statuses were not changed. No depth-5 work was attempted.

## N268 continuation — every labeled graph cycle has a Jordan trace

- **Ledger ID / manuscript evidence:** N268 / depth 0, prerequisite of N176 / depth 4; the material use remains the planar graphic/cographic step in the proof of `prop:r10-proper-minors`.
- **Checked path bridge:** `JordanPath.trans_injective_of_intersection` proves that injective arcs meeting only at their common endpoint concatenate injectively. `JordanPath.trans_simpleClosed_of_two_arcs` handles two injective arcs meeting only at their two endpoints, giving the half-open injectivity needed for the circle quotient. `PlaneEmbedding.edgePath_intersection_endpoints` and `exists_injective_linkPath` supply the corresponding labeled-edge geometry.
- **Checked graph-cycle bridge:** `Matroid/Internal/SimpleCycleTrace.lean` uses an auxiliary `SimpleGraph` only to choose a vertex-simple walk; each adjacency retains an actual labeled edge witness. Inclusion-minimal reachability forces the chosen edge labels to equal the original connecting set. `PlaneEmbedding.exists_minimalReachable_drawnArc` proves the resulting drawn path injective with exact support. `hasJordanTrace_of_minimalClosingEdge` closes it with a fresh labeled edge, including the two-parallel-edge case. `graphCycle_hasJordanTrace` combines this with the existing loop result for every `Graph.IsGraphCycle C`.
- **Separation and full-drawing interface:** `graphCycle_complement_card` proves that the complement of each cycle's drawn support has exactly two connected components; `graphCycle_component_boundary` identifies either component's boundary when a point in the other component is supplied. `faceMap_edgeSupport` maps each face of the full drawing into a component of the cycle-support complement. These declarations are available through `Matroid/Matroid.lean`.
- **Remaining exact gap:** The two sides of an isolated cycle are not yet identified with the edge-incident faces of the **full** drawing. N268 still needs a geometric assignment of both local edge sides to faces, finiteness/density or an equivalent local crosscut argument, and the two cycle/minimal-face-boundary clauses of `hasCycleBondFaceDual_iff_geometric_conditions`. N176 still depends on N268. Neither `LEDGER.md` (the preserved blind baseline) nor `DEPTHS.csv` was changed because neither node is complete; no depth-5 work was attempted.
- **Verification:** `lake build` completed successfully after the general Jordan bridge and full-face-to-cycle-side map. `#print axioms` for `graphCycle_hasJordanTrace` and `graphCycle_complement_card` reports only `propext`, `Classical.choice`, and `Quot.sound`; no `axiom`, `sorry`, or `admit` was introduced.

## N268 continuation — conditional full-face occupancy of Jordan sides

- **Ledger ID / manuscript evidence:** N268 / depth 0, prerequisite of N176 / depth 4; the proof of `prop:r10-proper-minors` uses the planar graphic/cographic correspondence.
- **Checked result:** `PlaneEmbedding.faceMap_edgeSupport_surjective_of_dense` sends full-drawing faces onto both complementary sides of any minimal cycle when the full drawing's complement is dense. With that density and a finite face type, `exists_face_closure_on_cycleSide` shows every point in the closure of a cycle side is approached by a full face assigned to that side. Applying the Jordan whole-boundary theorem at an edge interior point gives `graphCycle_exists_incidentFace_on_side` and `graphCycle_exists_two_incidentFaces`: each edge in a minimal cycle has two distinct incident full-drawing faces, one on each side.
- **Hypotheses still open:** Density of the complement of an arbitrary finite `PlaneEmbedding` and finiteness of its face type are not yet derived from the embedding axioms. The checked theorem does not assign the two incident faces of **every** edge, including bridges, and does not prove that cycle-side partitions have boundary exactly the corresponding primal cycle or that every nonempty face boundary contains a cycle. These remain the geometric conditions required by `hasCycleBondFaceDual_iff_geometric_conditions`; N268 and N176 remain unresolved.
- **Crosscut audit:** The inspected `schoenflies-lean` `GeneralCrosscut.lean` assumes a polygonal crosscut and an arc-collar hypothesis, while `PlaneEmbedding.edgePath` permits arbitrary continuous embedded arcs. Its source cannot be applied directly to the remaining local-side theorem, so no dependency was added. See `SOURCES.md` for the exact mismatch.
- **Verification and scope:** Full `lake build` passed. `#print axioms` for `graphCycle_exists_two_incidentFaces` reports only `propext`, `Classical.choice`, and `Quot.sound`. The preserved blind `LEDGER.md` and `DEPTHS.csv` statuses were not changed. No depth-5 work was attempted.

## N268 continuation — density of every finite plane drawing

- **Ledger ID / manuscript evidence:** N268 / depth 0 remains prerequisite of N176 / depth 4 at the planar graphic/cographic step of `prop:r10-proper-minors`.
- **Checked local result:** `Matroid/Internal/PlaneArcDensity.lean` proves that no continuous injection maps the unit circle into the unit interval: antipodal values and sphere connectedness force a repeated value. If a drawn nonloop edge arc contained an open disk, a smaller circle in that disk would contradict this theorem. A loop edge has a Jordan trace; the imported whole-component-boundary theorem identifies its support with the frontier of an open complementary side, which has empty interior. Thus `PlaneEmbedding.dense_compl_edgePath` holds for every actual edge, including loops, and `dense_compl_drawnSet` holds for every finite drawing.
- **Discharged hypotheses:** `faceMap_deleteEdges_surjective_of_finite` and `faceMap_edgeSupport_surjective_of_finite` now require only finite vertex and edge sets. `graphCycle_exists_two_incidentFaces_of_finite` removes the density assumption from the preceding conditional theorem; it still assumes `Finite P.Face` and applies to edges of a minimal graph cycle.
- **Remaining exact gap:** Prove finite full-face type or replace that assumption with a local side argument; assign incident faces to bridge edges as well as cycle edges; establish both cycle/minimal-face-boundary clauses needed by `hasCycleBondFaceDual_iff_geometric_conditions`. The new density theorem alone does not establish a geometric dual, so N268 and N176 remain unresolved.
- **External source audit:** At `schoenflies-lean` revision `05a43d29cde026618777db3d4e4316204ccca237`, `Graph.face_cycles'` is proved without a crosscut premise. It is restricted to finite, two-connected, polygonal, loopless drawings and does not identify faces of this project's arbitrary original drawing. See `SOURCES.md`; no source was imported.
- **Verification:** Full `lake build` passed (8987 jobs). `#print axioms` for `dense_compl_drawnSet` and `graphCycle_exists_two_incidentFaces_of_finite` lists only `propext`, `Classical.choice`, and `Quot.sound`. No new `axiom`, `sorry`, or `admit`; no depth-5 work. The preserved blind ledger and `DEPTHS.csv` statuses remain unchanged.

## N268 continuation — relative Schoenflies and transport of the original faces

- **Ledger IDs / manuscript evidence:** N268 / structural depth 0 remains a direct prerequisite of N176 / depth 4. The material manuscript use is the planar graphic/cographic sentence in `prop:r10-proper-minors` (lines 4401–4406). Inspection confirms that the nearby explicit Oxley citation is attached to the `R₁₀` single-element minor identities. The two planar-duality rows are corrected to `EXTERNAL_UNCITED_STANDARD`; imported topology is not described as a manuscript proof.
- **External proved infrastructure:** The existing exact `jordan_pick` pin `b3c9b7cf7358bf81a077d78ad67e6e8247869ddd` was verified against the dependency checkout, license, and successful baseline build. The workspace's adapted `schoenflies-lean` dependency at upstream revision `05a43d29cde026618777db3d4e4316204ccca237` also builds with Lean/mathlib 4.35.0-rc3. Reversing `Vendor/schoenflies/COMPATIBILITY.patch` in a temporary audit copy reproduces all 128 original hashes. Its Apache-2.0 license and notices are retained. `SOURCES.md` now records the relative Schoenflies declarations actually used and corrects the earlier, historical claim that no Schoenflies source was imported.
- **Retained graph-cycle bridge:** The prior `graphCycle_hasJordanTrace` already covers every minimal labeled cycle, including loops and parallel-edge pairs. The existing `graphCycle_isJordanCurve` and `graphCycle_hasAmbientModelCurve` compose that exact-support trace with the imported `Schoenflies.jordan_schoenflies_of_homeomorph`.
- **New narrow bridges:** `Matroid/Internal/AmbientEmbedding.lean` defines `PlaneEmbedding.reembed`, proves exact transport of full support and selected edge support, and identifies full complementary face types with `reembedFaceHomeomorph`. `reembed_facePoints` and `reembed_faceIncident_iff` transport each original face region and edge-interior incidence. `reembed_faceBoundary_preimage`, `reembed_faceBoundary_image`, and `reembed_minimalFaceBoundary_iff` preserve face partitions and minimal boundaries. `reembed_hasCycleBondFaceDual_iff` reuses the existing finite graph/matroid reductions to show that an ambient homeomorphism preserves the exact N268 certificate.
- **Composition with Schoenflies:** `graphCycle_hasAmbientModelEmbedding` now moves the entire original labeled drawing while carrying its selected cycle to the standard square. `edgeInterior_has_support_neighborhood` uses compact finite support and interior disjointness to exclude all vertices and edges outside the selected support near an interior point. It establishes local equality of the full support and a selected cycle without proving general plane topology.
- **Exact remaining incompatibility / fallback:** The audited `general_crosscut_three_regions` requires polygonality and arc collars; `face_cycles'` requires a finite, two-connected, polygonal, loopless drawing. `polygonal_redrawing` supplies no ambient homeomorphism or original-face correspondence. Moving one cycle does not polygonalize all remaining edges. Complete two-face incidence (including bridges), finite faces or an equivalent local-side route, and the nonempty-face-boundary/forest argument remain unproved. These obligations are detailed in `N268_BLOCKER.md`. Explicit certificates for proper `K₃,₃` minors were considered only as a separate application fallback; they cannot close the general theorem and would enter downstream N178 / depth 8, so no such implementation was begun.
- **Ledger / depth audit:** N268 is `BLOCKED_PROOF`, replacing the stale label suggesting that Jordan infrastructure is absent; N176 remains `MISSING_PREREQUISITE`. `DEPTHS.csv` was regenerated from the corrected canonical ledger and unchanged direct-edge DAG, and every structural depth was checked against the previous CSV. Active totals remain 197 nodes / 53 complete. N268 and N176 are the only unresolved active nodes through depth 4. The active formalization is not complete through topological depth 4; no depth-5 work was performed.
- **Verification:** Full `lake build` passes with both imported developments and the new local bridges (9119 jobs). The source-hash audit passes. `#print axioms` for all four imported Jordan results, the relative Schoenflies theorem, the general graph-cycle Jordan trace, both ambient-standardization bridges, incidence transport, N268-certificate transport, and the local support-neighborhood theorem reports only `propext`, `Classical.choice`, and `Quot.sound`. No theorem is introduced as an axiom or copied as an unverified statement. `git diff --check` passes.

## N268 continuation — complete cycle-edge incidence without finite faces

- **Ledger IDs / scope:** N268 / structural depth 0, prerequisite of N176 / depth 4. Continue from the verified Jordan/Schoenflies bridges and retain the finite labeled-multigraph graph/matroid reductions. No depth-5 work.
- **Pointed relative bridge:** `PlaneEmbedding.graphCycle_hasAmbientModelCurve_at` sends an arbitrary specified cycle point to `(0,1)`, the midpoint of a model-square side. `JordanCurve.jordanCurveHomeo` identifies the trace with the circle parameter space; a translation on `AddCircle` adjusts the boundary homeomorphism before applying the imported `Schoenflies.jordan_schoenflies_of_homeomorph`. All source revisions, licenses, and actually used declarations remain recorded in `SOURCES.md`.
- **Actual local faces:** New `Matroid/Internal/CycleLocalSides.lean` combines pointed Schoenflies with `edgeInterior_has_support_neighborhood`. In a sufficiently small ball about `(0,1)`, the model square equals the line with second coordinate 1. Its two convex open half-balls pull back to connected subsets of actual complementary faces of the full drawing. `graphCycle_local_faces` proves that each local cycle point is in the closure of both faces, that no third face approaches any point of that neighborhood, and that the two faces lie on opposite Jordan sides. The last step uses the imported whole-boundary theorem for the other cycle component. No polygonality, arc collars, or global finite-face hypothesis is assumed.
- **Entire-edge consistency:** `graphCycle_edge_incidence_all_interior` makes the approach set of a fixed face both open and closed in the connected open edge-parameter interval. `graphCycle_edge_has_complete_incidentFaces` then proves exactly two incident full faces for every edge belonging to a minimal cycle. This includes one-edge loops and parallel-edge cycles. `exists_complete_incidence_of_each_edge_on_cycle` chooses a complete whole-drawing assignment under the explicit hypothesis that every edge lies in a cycle; it is an edgewise subcase, not N268.
- **Reused N268 reduction:** `faceBoundary_cycleSide_eq_of_complete_incidence_no_faceFinite` proves that the cycle-side partition has exactly the original cycle as its boundary. `graphCycles_are_faceBoundaries_of_complete_incidence_no_faceFinite` removes the prior global `Finite P.Face` requirement. `hasCycleBondFaceDual_of_complete_incidence_and_boundaryCycle` feeds this into the retained geometric reduction. `hasCycleBondFaceDual_of_complete_incidence_and_forestBoundary` further uses existing graphic-matroid circuit extraction, leaving only complete all-edge incidence and exclusion of nonempty forest boundaries as supplied geometric hypotheses. The converse dual cycle/bond direction remains the existing short matroid-duality consequence.
- **Exact remaining blocker:** Edges belonging to no primal cycle have no containing Jordan curve to standardize, and their complete repeated-face incidence is not yet proved. Every-edge-cyclic drawings still need the forest-boundary exclusion. The inspected isolated-arc complement theorem does not establish either full-drawing statement. The previously audited crosscut and polygonal redrawing declarations do not supply the missing arbitrary-arc incidence or original-face correspondence. `N268_BLOCKER.md` now removes the discharged cycle-edge and finite-face obligations and states these two inputs precisely. No general plane-topology library, downstream special-case replacement, or axiom was introduced.
- **Ledger / depth verification:** N268 remains `BLOCKED_PROOF`; N176 remains `MISSING_PREREQUISITE`. The canonical ledger notes and current frontier reflect the new checked result. `DEPTHS.csv` was regenerated/revalidated against the unchanged direct-edge DAG: all statuses and structural depths remain unchanged, with 197 active nodes / 53 complete. N268/N176 remain the only unresolved active requirements through depth 4, so no depth-4 completion claim is made.
- **Build / trust verification:** Full `lake build` passes after the pointed bridge and after the integrated local-face module (9120 jobs). `#print axioms` for `jordanCurveHomeo`, the pointed bridge, all three local/full-edge incidence theorems, both finite-face-free cycle-boundary theorems, the edgewise assignment, and both sufficient N268 reductions reports only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, or `axiom` was added. `git diff --check` passes.

## N268 continuation — complete all-edge incidence and retained-boundary separation

- **Ledger IDs / scope:** N268 / structural depth 0 remains prerequisite of N176 / depth 4. All graph semantics, imported pins, and existing finite graph/matroid reductions are retained. No depth-5 node was attempted.
- **Bridge-edge route found in existing imports:** The pinned Schoenflies closure already contains `exists_countable_dense_stronglyAccessible`, `arc_complement`, and `exists_simple_arc_of_polyAccessible`. For a nonloop edge, the checked dense-complement theorem supplies the accessibility theorem's closure hypothesis. Relative openness of parameter subintervals selects accessible points before and after any chosen interior parameter. The imported joining result supplies an auxiliary polygonal arc in the complement of that original edge. Gluing it to the intervening original subarc with `IsJordanCurve.of_two_arcs` gives an auxiliary Jordan curve. The auxiliary arc may cross other edges away from the selected point, which causes no problem: compactness excludes it from the final full-drawing neighborhood.
- **Checked local and whole-edge results:** `nonloop_edge_has_local_modelCurve` in new `Matroid/Internal/EdgeLocalSides.lean` applies pointed relative Schoenflies to that auxiliary curve and combines it with finite-support/subarc isolation. `local_faces_of_modelCurve` in `CycleLocalSides.lean` shares the local convex-half-ball argument and allows the two global faces to coincide. `edge_local_faces` combines the nonloop route with the existing one-edge loop cycle proof. `edge_incidence_all_interior` propagates any incidence through the connected open parameter interval. `edge_has_complete_incidentFaces` and `exists_complete_incidence` now give a complete pair for every actual edge, including bridges, without a cycle or finite-face hypothesis. They do not separately assert that a bridge's pair must repeat a face before forest exclusion is established.
- **Discharged geometric conditions:** `exists_incidence_with_cycle_boundaries` composes the new assignment with the already checked cycle-side boundary theorem. Both actual incidence and the forward cycle-boundary clause of `hasCycleBondFaceDual_iff_geometric_conditions` now follow from the finite drawing alone.
- **New boundary bridge:** `Matroid/Internal/ForestBoundary.lean` extends the partition color across every edge outside the selected face boundary. A colored union of full faces has closure locally constant away from the retained boundary support and vertices: complementary points use openness of their face, and edge-interior points use the two local faces and equality of their colors. A nonempty boundary supplies complementary color witnesses. `faceBoundary_complement_not_isPreconnected` concludes that the complement of the retained boundary support plus original vertices is not preconnected. No connectivity theorem for forests is re-proved in this bridge.
- **Single sufficient remaining input:** `hasCycleBondFaceDual_of_forest_complement` closes the existing N268 reduction given `∀ D ⊆ G.edgeSet, G.IsForestIn D → IsPreconnected (P.vertexPoint '' G.vertexSet ∪ P.edgeSupport D)ᶜ`. This is an explicit supplied hypothesis, not a new axiom or an unconditional theorem. The audited isolated-arc complement declaration proves the one-arc case, but does not give nonseparation for arbitrary branches meeting at vertices or multiple disjoint tree components. Forest-boundary exclusion, N268, and therefore N176 remain unproved.
- **Additional source audit / fallback:** Inspected the public `lowrank/gromov-filling-lower-bound` checkout `880e76637f728ed0b44ba2daf8777ffd9a579ded`. Its Apache-2.0 classification source includes `Moise.PlaneComplex.exists_graph_PL_approximation`, which returns a close PL replacement embedding fixing original vertices. It does not supply an ambient plane homeomorphism or original-face/complement connectivity correspondence. The package is adapted to Lean/mathlib 4.29.0 and was not imported. `SOURCES.md` records the exact inspected revision, license, declaration, and conclusion mismatch. `N268_BLOCKER.md` now removes the discharged all-edge incidence obligation and gives the remaining forest statement exactly. The downstream special-case certificate fallback remains distinct and unimplemented; no depth-5 or depth-8 application work was begun.
- **Ledger / depth verification:** N268 remains `BLOCKED_PROOF`; N176 remains `MISSING_PREREQUISITE`, with `EXTERNAL_UNCITED_STANDARD` provenance. Updated canonical notes and current frontier. Regenerated/revalidated `DEPTHS.csv` from the ledger and unchanged direct-edge DAG; statuses and depths remain unchanged, with 197 active nodes / 53 complete. No depth-4 completion claim is made.
- **Build / trust verification:** Full `lake build` passes after the integrated all-edge module (9121 jobs) and after the retained-boundary bridge (9122 jobs). `#print axioms` for the four newly used imported topology theorems, the shared local model, all-edge local model and incidence results, the complete assignment with cycle boundaries, retained-boundary separation, and the sufficient N268 forest reduction lists only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, or `axiom` was added. `git diff --check` passes.

## N268 geometric-gap attack — unconditional primal cycle to dual bond

- **Scope / provenance:** Continue N268 at depth 0 as the outstanding prerequisite of N176 at depth 4. Preserve original finite labeled multigraphs, their arbitrary continuous edge paths, loops, and parallel edges. Existing imported revisions and graph/matroid reductions are unchanged. Standard external topology is distinguished from manuscript provenance (`EXTERNAL_UNCITED_STANDARD`). No depth-5 or downstream special-case application work.
- **Finite original vertices:** New `Matroid/Internal/ArcBoundary.lean` uses mathlib's `OpenPartialHomeomorph.univBall` to transport imported connectedness of the punctured plane to a punctured ball. A hypothetical open partition of an open connected region minus a point extends across that point, contradicting connectedness of the original region. Finite induction gives `plane_open_preconnected_sdiff_finite`. No punctured-disk paths, new Jordan separation, or arc-density proof is developed. `retained_complement_preconnected_iff_edge_complement` proves that retaining all original vertex points is immaterial for connectivity outside a selected compact edge support. `hasCycleBondFaceDual_of_forest_edge_complement` therefore requires only nonseparation of forest edge supports, with that remaining hypothesis explicit.
- **Arc-supported boundary exclusion:** Exported the existing interval obstruction as `plane_dense_compl_of_arc`, without changing its proof. Imported `JordanCurve.arc_not_separates` plus the finite-vertex bridge gives a dense preconnected complement of an arc together with the original vertices. Any retained boundary support contained in that arc has a larger complement lying between this connected set and its closure. This contradicts the existing `faceBoundary_complement_not_isPreconnected` for a nonempty boundary. The checked result is `faceBoundary_eq_empty_of_subset_arc`, not nonseparation of arbitrary forests.
- **Proper cycle subsets:** `proper_cycle_subset_is_contained_in_arc` chooses an actual missing edge label and its midpoint. Joint interior injectivity guarantees that this point really lies outside the selected smaller support, including for loops and parallel pairs. The exact graph-cycle Jordan trace pulls the compact smaller support back to a proper closed circle subset. Newly used imported `JordanCurve.Arcs.exists_proper_arc` contains it in a proper interval arc; the compact-to-Hausdorff homeomorphism API transports that arc back into the original drawing. No walk or graph model is replaced.
- **Completed correspondence direction:** `graphCycle_isMinimalFaceBoundary` combines the already checked exact cycle boundary with exclusion of all its proper boundary subsets. `graphCycle_isBond_faceIncidenceGraph` reuses the existing graph-cut/bond API. `exists_incidence_with_cycle_bonds` constructs a complete actual incidence assignment with every primal graph cycle a dual bond, without supplied forest-connectivity, endpoint-collar, polygonality, or finite-face hypotheses.
- **Remaining gap / investigated endpoint route:** N268 still needs the converse: every nonempty face boundary must contain a primal cycle. Forest-boundary exclusion is proved only when the entire support fits inside one arc. A finite forest may branch or have several components. A possible leaf induction would need local nonseparation at a free arc endpoint in the presence of the other retained edges; the audited global isolated-arc theorem does not provide that local result. No endpoint collar or finite-union nonseparation theorem is inferred without proof. No new external package or unverified statement is introduced.
- **Ledger / depth verification:** Updated `SOURCES.md`, `N268_BLOCKER.md`, the canonical ledger note, and current frontier. N268 remains `BLOCKED_PROOF`, and N176 remains `MISSING_PREREQUISITE`. Revalidated `DEPTHS.csv` against the unchanged active DAG: 197 active nodes / 53 complete, with no status or depth changes. N268 and N176 remain the only unresolved requirements through depth 4; no depth-4 completion claim is made.
- **Build / trust verification:** Full `lake build` passes after the integrated cycle-to-bond bridge and again after the simpler forest-complement reduction (9123 jobs). All 13 imported/local declarations in `/tmp/n268-cycle-bonds-axiom-audit.lean` report only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`. The new module has no unresolved proof placeholder or axiom declaration. `git diff --check` passes.

## N268 / N176 completion — forest lifts and imported no-retraction (2026-10-10)

- **Scope and source checks:** Retained the existing exact Jordan and adapted Schoenflies pins and Lean/mathlib 4.35.0-rc3. The entry `lake build` passed (9123 jobs). Directly rechecked the original classification-of-surfaces source at `e3c7230fe78d7b056a415d9ecae6f77887046b32` and Schoenflies at `05a43d29cde026618777db3d4e4316204ccca237`; no new package was needed. The PL approximation conclusion still supplies no original-complement transport. See `SOURCES.md` for license and declaration provenance.
- **Graph-specific forest bridge:** Repaired and integrated the previously unbuilt `Internal/ForestLift.lean` potential lemma (explicit edge-index binder and explicit cut set). `forest_exists_vertex_potential` integrates additive edge increments via the existing forest isolating-cut criterion. `forest_exists_compatible_lifts` uses imported real-line covering path lifts, then integer vertex potentials to align all endpoint values. `PlaneEmbedding.forest_circle_lift` descends to the actual forest support using a compact finite union of edge intervals and the embedding’s joint interior injectivity. `forest_sphere_extension` applies imported Tietze extension to the real lift. No degree, connectedness, collar, polygonality, or finite-face premise is supplied.
- **Final geometric obstruction:** New `Internal/ForestComplement.lean` applies the pinned `JordanCurve.Brouwer.no_retraction` directly. A hypothetical bounded component has frontier in the forest; the sphere extension pastes with radial projection outside it to give a forbidden disk retraction. `forest_component_not_bounded` and the imported `JordanCurve.isConnected_compl_closedBall` give `forest_edge_complement_preconnected`. This is the narrow graph bridge needed by the existing reduction; no general Jordan/crosscut/endpoint topology was re-proved.
- **N268 complete:** `PlaneEmbedding.hasCycleBondFaceDual` discharges `hasCycleBondFaceDual_of_forest_edge_complement`. Complete all-edge incidence, exact primal cycle boundaries, finite circuit extraction, and the converse matroid-duality reduction are reused. The dual uses the original full-drawing faces and original labels, including loops and parallel edges; no planarity definition or theorem scope was weakened.
- **N176 complete:** `PlaneEmbedding.matroid_correspondence` is a direct consequence of N268 and `matroid_correspondence_of_faceDual`. `IsPlanar.matroid_correspondence` exposes the manuscript interface from existence of an actual plane drawing, with both graphic/cographic equalities on the same edge labels. Provenance remains `EXTERNAL_UNCITED_STANDARD`; the local bridge is not a manuscript proof.
- **Build and trust:** Full `lake build` passed after the lift/extension bridge (9124 jobs), after N268 (9125 jobs), and after N176 (9125 jobs). `#print axioms` for `no_retraction`, `cover`, `acToSphere`, all seven new graph bridge/end-point declarations plus the potential and compatible-lift lemmas (12 declarations total) reports only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`. The audit was run with `lake env lean /tmp/n268-n176-final-audit.lean`. Both final signatures have only the intended embedding/planarity and graph-finiteness assumptions.
- **Ledger, DAG, and stop:** Marked N268 and N176 `COMPLETE` with `LOCAL_PROOF` bridge provenance. Regenerated `DEPTHS.csv` from the canonical ledger and unchanged direct-edge DAG, checked every previous structural depth and prerequisite list, and verified that all active requirements through depth 4 are complete. Totals: 197 active, 55 complete, 142 unresolved. Identified the 14 unresolved nodes at depth 5 in `FRONTIER.md` and stopped; no depth-5 or downstream application proof was started. Updated the old blocker report to a resolution report.

The active Matroid formalization is complete through topological depth 4.

## One depth-5 pass — 2026-10-11

Preflight: the full `lake build` passed; N268/N176 source declarations were left unchanged; a project source scan found no `sorry`, `admit`, or `axiom`. The active direct-edge graph recomputation agreed with `DEPTHS.csv`: 197 active nodes, all complete through depth 4, and exactly the 14 initial depth-5 targets frozen in `FRONTIER.md`. The plans below were fixed against the manuscript and ledger before the local library search. No direct dependency edge was changed. `PROOF_STATUS.csv` separates mathematical provenance from kernel trust, and `PROOF_BUDGET.md` carries cumulative external-theorem accounting.

| ID | Manuscript evidence and mathematical plan | Lean declaration, direct formal dependencies, route | Result / resource / audit |
| --- | --- | --- | --- |
| N026 | `def:matroid-minors`: minor means a sequence of deletion/contraction operations. Normalize the sequence to one contraction then one deletion. | `Matroid.minor_iff_contract_delete`, `deletion_isMinor`, `contraction_isMinor`, `minor_trans`; mathlib `Matroid.IsMinor`, `contract_delete_isMinor`, `IsMinor.trans`. | KERNEL_PROVED; no external budget. Axiom audit: foundational axioms only. |
| N028 | Repeated contraction in the minor discussion: rank subtraction or dualized deletion composes by union, without requiring disjointness. | `Matroid.contraction_composition`; mathlib `Matroid.contract_contract`. | KERNEL_PROVED; budget N028. Axiom audit: foundational only. |
| N029 | Mixed minor operations in `thm:regular-matroid-energy`: disjoint deletion and contraction commute on the same labels. | `Matroid.deletion_contraction_commutation`; mathlib `Matroid.contract_delete_comm`, using the disjointness hypothesis. | KERNEL_PROVED; budget N029. Axiom audit: foundational only. |
| N041 | Proof of `prop:target-extension-criterion`: if `M` restricts to `N`, then `A` and `cl_N(A)` have equal rank in `M` and span the new target simultaneously. Prove old closure is `cl_M(A)∩N.E`, then compare closures and restricted ranks. | `Matroid.IsSingleElementExtension.closure_rank_and_target`; `IsSingleElementExtension`, mathlib `restrict_closure_eq`, `restrict_eRk_eq`, `eRk_closure_eq`. | KERNEL_PROVED; budget N041. Axiom audit: foundational only. |
| N045 | Prose after `def:vector-matroid`: for a ground element, matroid closure is indexed vector span. Choose a basis of `A`, prove its vector span equals that of `A`, then use linear independence after insertion. | `Matroid.Represents.mem_closure_iff_mem_span`; `Represents`, `exists_isBasis`, `linearIndepOn_insert`, `Indep.mem_closure_iff'`. Ground membership is explicit. | KERNEL_PROVED; budget N045. Axiom audit: foundational only. |
| N049 | Actual proof of `prop:represented-minors`: quotient by the span of **all** contracted columns, including a dependent set. Choose a basis of that set, identify spans, and compare independent survivors using the quotient independence lemma. | `Matroid.Represents.contract`; `Represents`, `IsBasis.contract_indep_iff_of_disjoint`, `linearIndepOn_union_iff_quotient`, `Submodule.Quotient.mk`. The quotient uses the original indexed labels. | KERNEL_PROVED manuscript proof; no admission. Axiom audit: foundational only. |
| N053 | Remark after `def:regular-matroid`: every TU integer matrix has the same indexed column matroid over every field, including characteristic 2. Plan: independent columns iff a square minor is nonzero, then transfer each minor via the existing sign-valued bridge. | Existing `Matrix.IsTotallyUnimodular.intCast_minor_ne_zero_iff` proves nonvanishing transfer, but no exact rectangular indexed independence/minor criterion was found in the pinned matrix API. No full declaration. | UNRESOLVED; budget N053. No admission; the earlier reconnaissance is retained. |
| N125 | Weighted-energy subsection cites Cauchy–Binet plus TU. Plan: prove a finite-index rectangular weighted Cauchy–Binet identity, filter nonzero squared TU minors locally, and identify maximal independent columns with bases. The source's rank and column-count hypotheses were checked. | Existing `Matrix.IsTotallyUnimodular.det_submatrix_sq_of_ne_zero` proves the TU filter. Pinned mathlib's `det_mul` handles square products; no rectangular weighted identity was found. No full declaration. | UNRESOLVED; budget N125. No admission. Source: Choe–Oxley–Sokal–Wagner, Theorem 8.1 and Corollary 8.2, plus the Cauchy–Binet statement in their footnote 12. |
| N131 | Uniform-matroid notation used for the Grover source: a target in `U_{1,n+1}` is a nonloop and every nonempty other set spans it. Choose one available element; the two-element set is dependent while each singleton is independent. | `Matroid.uniformOn_one_target_closure`; `uniformOn_indep_iff`, `Indep.mem_closure_iff'`. | KERNEL_PROVED; budget N131. Axiom audit: foundational only. |
| N134 | Dual minor interpretation used at `def:graphic-cographic`: deletion and contraction exchange in both directions. | `Matroid.deletion_dual_eq_contraction`, `contraction_dual_eq_deletion`; mathlib `Matroid.dual_delete`, `dual_contract`. | KERNEL_PROVED; budget N134. Both declarations audited. |
| N137 | The proof of `prop:seymour-one-sum` factors bases of a target-containing direct sum, then cancels the target-free weighted basis factor. A full statement must use `weightedBasesIn`/`weightedBasesOut`, prove both finite-sum product identities, and justify cancellation with the manuscript's positive-weight and zero-denominator conventions. | `Matroid.oneSum_isBase_iff_exists` (N136) supplies the exact basis bijection. The new checked `Matroid.sum_powerset_union_of_disjoint` in `WeightedBases.lean` supplies the finite-index Fubini/bijection step. The matroid-basis indicators, target-omitting product factorization, positivity of the target-free factor, and denominator-zero ratio semantics remain unformalized. | UNRESOLVED manuscript proof with a proved intermediate. No `sorry` or external substitute. |
| N143 | In the proof of `prop:seymour-two-sum-input-minors`, a nonspanning target is precisely a coloop in the restriction to available elements plus target, so the target-omitting weighted basis sum is zero. Prove the restriction equivalence, then use every-basis membership. | `Matroid.nonspanned_target_iff_isColoop_restrict`, `nonspanned_target_weightedBasesOut_eq_zero`; `restrict_isColoop_iff`, `weightedBasesOut_eq_zero_of_isColoop`. | KERNEL_PROVED manuscript zero case. Axiom audit: foundational only. |
| N262 | Proof of `thm:regular-matroid-energy`: delete dependent rows **after restricting columns**, retaining all weighted target reconstruction equations. Plan: choose a row-space basis, express deleted rows as linear combinations of retained rows on the restricted matrix, and prove both directions of every equation before proving the indexed column matroid equality. | Existing N044 represented rank covers only rank. No exact matrix/reconstruction signature or full declaration was added; a rank-only statement would miss the canonical requirement. | UNRESOLVED; budget N262. No source-checked admission. |
| N264 | Graphic double-star use: an actual labeled edge closes an edge set exactly when its endpoints are connected through selected edges. A loop has identical endpoints and is closed by the reflexive path; parallel labels remain distinct. | `Matroid.graphic_mem_closure_iff_reachableOn`; project `IsLiftedEdgeCut`, `not_reachable_iff_separating_cut`, `edgeCutMatroid`, and mathlib `map_closure_eq`. | KERNEL_PROVED; budget N264. Axiom audit: foundational only. |

The ten proved nodes were marked `COMPLETE` in the ledger, while the four open nodes retained their initial ledger statuses. The DAG was unchanged; `DEPTHS.csv` was recomputed with 65/197 active nodes complete. Unconditional and citation-relative certified depths are both 4. No depth-6 proof was attempted.

Final verification: full `lake build` passed (9125 jobs). `lake env lean /tmp/matroid-depth5-axioms.lean` checked every new project-facing depth-5 declaration, both N143 zero-case helpers, and the unchanged N268/N176 final declarations. Each printed only `propext`, `Classical.choice`, and `Quot.sound`; none printed `sorryAx`. The Lean-source scan found no `sorry`, `admit`, or `axiom` declaration, and `git diff --check` passed. The depth/status cross-check against all active ledger rows and direct edges passed; the only unresolved depth-5 nodes are N053, N125, N137, and N262.
