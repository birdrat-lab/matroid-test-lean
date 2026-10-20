import Matroid.SeymourDecomposition
import Matroid.R10CircuitParity

/-! N179: an intact R₁₀ copy has no proper three-sum triangle. -/

namespace Matroid

private theorem isCircuit_preimage_mapEmbedding {α β : Type*}
    (M : Matroid α) (f : α ↪ β) {C : Set β}
    (hC : (M.mapEmbedding f).IsCircuit C) :
    M.IsCircuit (f ⁻¹' C) := by
  have hCsub : C ⊆ Set.range f := by
    intro x hx
    have hxE := hC.subset_ground hx
    rw [Matroid.mapEmbedding_ground_eq] at hxE
    exact Set.image_subset_range _ _ hxE
  have hpreE : f ⁻¹' C ⊆ M.E := by
    intro x hx
    have hxE := hC.subset_ground hx
    rw [Matroid.mapEmbedding_ground_eq] at hxE
    obtain ⟨y, hy, hxy⟩ := hxE
    exact (f.injective (hxy.trans rfl)).symm ▸ hy
  apply (M.isCircuit_iff_forall_ssubset).2
  refine ⟨?_, ?_⟩
  · apply (M.not_indep_iff hpreE).1
    intro hpre
    have himage : f '' (f ⁻¹' C) = C :=
      Set.image_preimage_eq_iff.mpr hCsub
    have hmap := hpre.mapEmbedding f
    rw [himage] at hmap
    exact hC.not_indep hmap
  · intro D hD
    have hDsub : f '' D ⊆ C := by
      rintro x ⟨y, hy, rfl⟩
      exact hD.subset hy
    have hDproper : f '' D ⊂ C := by
      apply Set.ssubset_iff_subset_ne.mpr
      refine ⟨hDsub, ?_⟩
      intro heq
      have hpre : f ⁻¹' (f '' D) = f ⁻¹' C := congrArg (f ⁻¹' ·) heq
      rw [Set.preimage_image_eq _ f.injective] at hpre
      exact hD.ne hpre
    have hInd := hC.ssubset_indep hDproper
    simpa only [Set.preimage_image_eq _ f.injective] using
      (Matroid.mapEmbedding_indep_iff.mp hInd).1

/-- A labeled R₁₀ copy has no three-element circuit. -/
theorem IsR10Copy.circuit_card_ne_three {α : Type*} {M : Matroid α}
    (hCopy : IsR10Copy M) {C : Set α} (hC : M.IsCircuit C) :
    C.ncard ≠ 3 := by
  obtain ⟨f, rfl⟩ := hCopy
  have hpre := isCircuit_preimage_mapEmbedding r10 f hC
  have hsub : C ⊆ Set.range f := by
    intro x hx
    have hxE := hC.subset_ground hx
    rw [Matroid.mapEmbedding_ground_eq] at hxE
    exact Set.image_subset_range _ _ hxE
  rw [← Set.ncard_preimage_of_injective_subset_range f.injective hsub]
  exact r10_circuit_card_ne_three hpre

/-- The first assertion of `prop:r10-no-three-sum`, for an R₁₀ copy on
the left side of a labeled proper 3-sum. -/
theorem IsR10Copy.not_properThreeSum_left {α : Type*}
    {M N P : Matroid α} {T : Set α} (hCopy : IsR10Copy M) :
    ¬ IsProperThreeSum M N P T := by
  intro h
  exact hCopy.circuit_card_ne_three h.2.2.1 h.2.1

/-- The corresponding assertion when the R₁₀ leaf is the right child. -/
theorem IsR10Copy.not_properThreeSum_right {α : Type*}
    {M N P : Matroid α} {T : Set α} (hCopy : IsR10Copy N) :
    ¬ IsProperThreeSum M N P T := by
  intro h
  exact hCopy.circuit_card_ne_three h.2.2.2.1 h.2.1

end Matroid
