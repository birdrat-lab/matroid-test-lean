import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Combinatorics.Matroid.Closure
import Mathlib.Combinatorics.Matroid.Rank.ENat

/-!
# The manuscript's first matroid boundary

Manuscript: `def:matroid` (N001), `def:matroid-basis` (N002), and
`def:matroid-circuit` (N015).

We use mathlib's `Matroid α`, with `Matroid.Finite M` for the manuscript's finite
ground set. Its `M.Indep` predicate gives the independent sets; `M.IsBasis I X`
is a maximal independent subset of `X ⊆ M.E`, and `M.IsCircuit C` is a minimal
dependent set. In the finite setting, `Matroid.Indep.augment` realizes the
manuscript's cardinality augmentation axiom. No additional foundational
matroid structure or aliases for these exact predicates are introduced.
-/

open Set

namespace Matroid

variable {α : Type*} {M : Matroid α} {I J X A C : Set α} {e : α}

/-- Manuscript: `def:matroid-basis` (N003), prose immediately following the
definition. Proof source: MANUSCRIPT_SKETCH. Exchange forbids two maximal
independent subsets of the same set from having different finite sizes. -/
theorem isBasis_ncard_eq [M.Finite] (hI : M.IsBasis I X) (hJ : M.IsBasis J X) :
    I.ncard = J.ncard := by
  simpa only [Set.ncard_def] using congrArg ENat.toNat (hI.encard_eq_encard hJ)

/-- Manuscript: `def:matroid-rank` (N006). The finite rank of `X` is the
cardinality of any basis of `X`; mathlib's `eRk` records that natural number
inside `ℕ∞`. -/
theorem isBasis_eRk_eq_ncard [M.Finite] (hI : M.IsBasis I X) :
    M.eRk X = (I.ncard : ℕ∞) := by
  rw [← hI.encard_eq_eRk]
  simpa only [Set.ncard_def] using hI.Finite.encard_eq_coe

/-- Manuscript: `def:matroid-rank` (N006). A basis attains the maximal
cardinality among independent subsets of the specified set. -/
theorem indep_ncard_le_isBasis_ncard [M.Finite] (hI : M.Indep I)
    (hIX : I ⊆ X) (hB : M.IsBasis J X) : I.ncard ≤ J.ncard := by
  have hencard : I.encard ≤ J.encard := by
    rw [hB.encard_eq_eRk]
    exact hI.encard_le_eRk_of_subset hIX
  have hJfinite : J.Finite := hB.Finite
  have hJcard : J.encard = (J.ncard : ℕ∞) := by
    simpa only [Set.ncard_def] using hJfinite.encard_eq_coe
  rw [hJcard] at hencard
  exact (Set.encard_le_coe_iff_finite_ncard_le.mp hencard).2

/-- Manuscript: `def:matroid-closure` (N007). On the finite ground set,
membership in closure is exactly preservation of rank after insertion. -/
theorem mem_closure_iff_eRk_insert_eq [M.Finite] (hA : A ⊆ M.E) (he : e ∈ M.E) :
    e ∈ M.closure A ↔ M.eRk (insert e A) = M.eRk A := by
  constructor
  · intro hcl
    calc
      M.eRk (insert e A) = M.eRk (M.closure (insert e A)) :=
        (M.eRk_closure_eq _).symm
      _ = M.eRk (M.closure A) := by rw [M.closure_insert_eq_of_mem_closure hcl]
      _ = M.eRk A := M.eRk_closure_eq _
  · intro hr
    have hfin : M.IsRkFinite A := M.isRkFinite_of_finite (M.set_finite A hA)
    have hcl : M.closure A = M.closure (insert e A) :=
      hfin.closure_eq_closure_of_subset_of_eRk_ge_eRk (subset_insert e A) hr.le
    rw [hcl]
    exact M.mem_closure_of_mem (mem_insert e A)
      (by
        intro x hx
        rcases hx with rfl | hxA
        · exact he
        · exact hA hxA)

/-- Manuscript: `prop:closure-circuit` (N016).
Proof source: MANUSCRIPT_STATEMENT_ONLY. -/
theorem mem_closure_iff_exists_circuit_sdiff [M.Finite]
    (_hA : A ⊆ M.E) (heA : e ∉ A) :
    e ∈ M.closure A ↔
      ∃ C, M.IsCircuit C ∧ e ∈ C ∧ C \ {e} ⊆ A := by
  rw [M.mem_closure_iff_exists_isCircuit heA]
  constructor
  · rintro ⟨C, hCsub, hC, heC⟩
    refine ⟨C, hC, heC, ?_⟩
    intro x hx
    rcases (hCsub hx.1) with rfl | hxA
    · exact (hx.2 rfl).elim
    · exact hxA
  · rintro ⟨C, hC, heC, hCsub⟩
    refine ⟨C, ?_, hC, heC⟩
    intro x hxC
    by_cases hxe : x = e
    · exact hxe ▸ mem_insert e A
    · exact mem_insert_of_mem e (hCsub ⟨hxC, by simpa using hxe⟩)

end Matroid
