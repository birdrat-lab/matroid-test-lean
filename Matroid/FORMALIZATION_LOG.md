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
- **Notes:** Finite M and A⊆E ensure candidate cardinalities are finite; hspan supplies a candidate.

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
