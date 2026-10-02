import Mathlib.Combinatorics.Matroid.IndepAxioms

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

end Matroid
