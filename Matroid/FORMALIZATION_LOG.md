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
