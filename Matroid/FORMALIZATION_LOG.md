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
