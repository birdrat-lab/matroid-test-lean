import Matroid.FlatsAndCocircuits

/-! Manuscript `prop:cocircuit-separates-closure` (N032). -/

namespace Matroid

private theorem hyperplane_of_maximal_nonspanning {α : Type*}
    (M : Matroid α) (H : Set α) (hHE : H ⊆ M.E)
    (hnot : ¬ M.Spanning H)
    (hmax : ∀ F : Set α, H ⊆ F → F ⊆ M.E →
      ¬ M.Spanning F → F = H) : M.IsHyperplane H := by
  have hclH : M.closure H = H := by
    apply hmax (M.closure H) (M.subset_closure H hHE)
      (M.closure_subset_ground H)
    intro hsp
    exact hnot ((M.closure_spanning_iff hHE).mp hsp)
  have hflat : M.IsFlat H := M.isFlat_iff_closure_eq.mpr hclH
  refine ⟨hflat, ?_, ?_⟩
  · intro hHEq
    apply hnot
    rw [hHEq]
    exact M.ground_spanning
  · intro F hF hHF
    by_cases hFE : F = M.E
    · exact Or.inr hFE
    · apply Or.inl
      exact hmax F hHF hF.subset_ground (by
        intro hsp
        exact hFE (hF.closure.symm.trans
          ((M.spanning_iff_closure_eq hF.subset_ground).mp hsp)))

theorem hyperplane_compl_of_isCocircuit {α : Type*}
    (M : Matroid α) {D : Set α} (hD : M.IsCocircuit D) :
    M.IsHyperplane (M.E \ D) := by
  have hmin := (M.isCocircuit_iff_minimal_compl_nonspanning).mp hD
  apply hyperplane_of_maximal_nonspanning M (M.E \ D)
    Set.sdiff_subset hmin.1
  intro F hHF hFE hFnot
  let K := M.E \ F
  have hKsubD : K ⊆ D := by
    intro x hxK
    by_contra hxD
    exact hxK.2 (hHF ⟨hxK.1, hxD⟩)
  have hEK : M.E \ K = F := by
    ext x
    constructor
    · rintro ⟨hxE, hxK⟩
      by_contra hxF
      exact hxK ⟨hxE, hxF⟩
    · intro hxF
      exact ⟨hFE hxF, fun hxK => hxK.2 hxF⟩
  have hKnot : ¬ M.Spanning (M.E \ K) := by rwa [hEK]
  have hDsubK : D ⊆ K := hmin.2 hKnot hKsubD
  apply Set.Subset.antisymm
  · intro x hxF
    exact ⟨hFE hxF, fun hxD => (hDsubK hxD).2 hxF⟩
  · exact hHF

/-- A mathlib cocircuit has exactly the manuscript's hyperplane-complement
form on the same ground set. -/
theorem IsCocircuit.isHyperplaneCocircuit {α : Type*}
    {M : Matroid α} {D : Set α} (hD : M.IsCocircuit D) :
    M.IsHyperplaneCocircuit D := by
  refine ⟨M.E \ D, hyperplane_compl_of_isCocircuit M hD, ?_⟩
  exact (Set.sdiff_sdiff_cancel_left hD.subset_ground).symm

/-- A ground element outside the closure of a ground subset is separated
from it by a cocircuit. The ground-membership hypothesis makes explicit
the manuscript's implicit `e ∈ E`. -/
theorem cocircuit_separates_closure {α : Type*} (M : Matroid α)
    (A : Set α) (e : α) (hA : A ⊆ M.E) (heE : e ∈ M.E)
    (hnot : e ∉ M.closure A) :
    ∃ D : Set α, M.IsCocircuit D ∧ e ∈ D ∧ Disjoint D A := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' A
  have hcl : M.closure I = M.closure A := hI.closure_eq_closure
  have heI : e ∉ I := by
    intro he
    exact hnot (hcl ▸ (M.subset_closure I hI.indep.subset_ground he))
  have hIns : M.Indep (insert e I) := by
    apply hI.indep.insert_indep_iff.mpr
    exact Or.inl ⟨heE, by rwa [hcl]⟩
  obtain ⟨B, hB, hIB⟩ := hIns.exists_isBase_superset
  have heB : e ∈ B := hIB (Set.mem_insert e I)
  have hIsub : I ⊆ B \ {e} := by
    intro x hx
    exact ⟨hIB (Set.mem_insert_of_mem e hx), by
      simpa [Set.mem_singleton_iff] using (fun hxe : x = e => heI (hxe ▸ hx))⟩
  have hAcl : A ⊆ M.closure (B \ {e}) := by
    have hA_clI : A ⊆ M.closure I := by
      rw [hcl]
      exact M.subset_closure A hA
    exact hA_clI.trans (M.closure_subset_closure hIsub)
  refine ⟨M.E \ M.closure (B \ {e}),
    hB.compl_closure_sdiff_singleton_isCocircuit heB, ?_, ?_⟩
  · exact ⟨heE, hB.indep.notMem_closure_sdiff_of_mem heB⟩
  · exact Set.disjoint_left.mpr (fun x hxD hxA => hxD.2 (hAcl hxA))

/-- N032 stated using the manuscript's explicit cocircuit predicate. -/
theorem cocircuit_separates_closure_manuscript {α : Type*}
    (M : Matroid α) (A : Set α) (e : α)
    (hA : A ⊆ M.E) (heE : e ∈ M.E)
    (hnot : e ∉ M.closure A) :
    ∃ D : Set α, M.IsHyperplaneCocircuit D ∧ e ∈ D ∧ Disjoint D A := by
  obtain ⟨D, hD, heD, hDA⟩ :=
    M.cocircuit_separates_closure A e hA heE hnot
  exact ⟨D, hD.isHyperplaneCocircuit, heD, hDA⟩

end Matroid
