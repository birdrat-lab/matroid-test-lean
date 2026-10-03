import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Combinatorics.Matroid.Circuit

/-! # Uniform -/

open Set

namespace Matroid

/-- Manuscript: uniform-matroid notation at `prop:grover-source-value` (N129).
The independent sets are exactly the subsets of `E` of size at most `r`. -/
noncomputable def uniformOn {α : Type*} (E : Set α) (hE : E.Finite) (r : ℕ) : Matroid α :=
  (IndepMatroid.ofFinite hE (fun I : Set α => I ⊆ E ∧ I.ncard ≤ r)
    (by simp)
    (by
      intro I J hJ hIJ
      exact ⟨hIJ.trans hJ.1, (Set.ncard_le_ncard hIJ (hE.subset hJ.1)).trans hJ.2⟩)
    (by
      intro I J hI hJ hcard
      obtain ⟨e, heJ, heI⟩ :=
        Set.exists_mem_notMem_of_ncard_lt_ncard hcard (hE.subset hI.1)
      refine ⟨e, heJ, heI, ?_⟩
      refine ⟨insert_subset (hJ.1 heJ) hI.1, ?_⟩
      have hlt : I.ncard < r := lt_of_lt_of_le hcard hJ.2
      rw [Set.ncard_insert_of_notMem heI (hE.subset hI.1)]
      exact Nat.succ_le_of_lt hlt)
    (fun _ hI => hI.1)).matroid

/-- Manuscript: uniform-matroid notation at `prop:grover-source-value` (N129).
This is the manuscript's independent-set characterization of `U_{r,n}`. -/
theorem uniformOn_indep_iff {α : Type*} (E : Set α) (hE : E.Finite)
    (r : ℕ) (I : Set α) : (uniformOn E hE r).Indep I ↔ I ⊆ E ∧ I.ncard ≤ r := by
  rfl

/-- Manuscript ledger N130, used at `prop:grover-source-value`. In a
corank-one uniform matroid the full ground is the only circuit. -/
theorem uniformOn_isCircuit_iff_eq_ground {α : Type*} (E : Set α)
    (hE : E.Finite) (r : ℕ) (hcard : E.ncard = r + 1) (C : Set α) :
    (uniformOn E hE r).IsCircuit C ↔ C = E := by
  let M := uniformOn E hE r
  have hproper : ∀ I : Set α, I ⊂ E → M.Indep I := by
    intro I hIE
    rw [uniformOn_indep_iff]
    exact ⟨hIE.subset, by
      have hlt := Set.ncard_lt_ncard hIE hE
      omega⟩
  constructor
  · intro hC
    have hCE : C ⊆ E := hC.subset_ground
    by_contra hne
    exact hC.not_indep (hproper C (Set.ssubset_iff_subset_ne.2 ⟨hCE, hne⟩))
  · rintro rfl
    apply (Matroid.isCircuit_iff_forall_ssubset).2
    constructor
    · rw [Matroid.dep_iff]
      constructor
      · rw [uniformOn_indep_iff]
        simp [hcard]
      · change C ⊆ C
        exact Subset.rfl
    · intro I hIE
      exact hproper I hIE

/-- Manuscript ledger N130. A chosen target in `U_{r,r+1}` lies in its
unique circuit, the full ground set. -/
theorem uniformOn_unique_target_circuit {α : Type*} (E : Set α)
    (hE : E.Finite) (r : ℕ) (hcard : E.ncard = r + 1)
    (τ : α) (hτ : τ ∈ E) :
    ∃! C : Set α, (uniformOn E hE r).IsCircuit C ∧ τ ∈ C := by
  refine ⟨E, ⟨(uniformOn_isCircuit_iff_eq_ground E hE r hcard E).2 rfl, hτ⟩, ?_⟩
  intro C hC
  exact (uniformOn_isCircuit_iff_eq_ground E hE r hcard C).1 hC.1

end Matroid
