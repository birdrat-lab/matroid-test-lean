import Matroid.CocircuitSeparation

/-! Dual-circuit interface for the manuscript's hyperplane-complement
cocircuit predicate. -/

namespace Matroid

/-- The manuscript's complement-of-hyperplane cocircuits are exactly
mathlib's dual-matroid circuits on the same ground set. -/
theorem isHyperplaneCocircuit_iff_dual_isCircuit {α : Type*}
    (M : Matroid α) (D : Set α) :
    M.IsHyperplaneCocircuit D ↔ M✶.IsCircuit D := by
  constructor
  · rintro ⟨H, hH, rfl⟩
    apply (M.isCocircuit_iff_minimal_compl_nonspanning).2
    have hHE : H ⊆ M.E := hH.1.subset_ground
    have hnot : ¬ M.Spanning H := by
      intro hsp
      exact hH.2.1 (hH.1.closure.symm.trans
        ((M.spanning_iff_closure_eq hHE).mp hsp))
    refine ⟨?_, ?_⟩
    · simpa [Set.sdiff_sdiff_cancel_left hHE] using hnot
    · intro K hKnot hKsub
      have hHK : H ⊆ M.E \ K := by
        intro x hxH
        refine ⟨hHE hxH, ?_⟩
        intro hxK
        exact (hKsub hxK).2 hxH
      have hHsub : H ⊆ M.closure (M.E \ K) :=
        hHK.trans (M.subset_closure _ Set.sdiff_subset)
      have hFflat : M.IsFlat (M.closure (M.E \ K)) := M.isFlat_closure _
      have hFproper : M.closure (M.E \ K) ≠ M.E := by
        intro hEq
        exact hKnot ((M.spanning_iff_closure_eq Set.sdiff_subset).2 hEq)
      have hFEq : M.closure (M.E \ K) = H := by
        rcases hH.2.2 _ hFflat hHsub with hEq | hEq
        · exact hEq
        · exact False.elim (hFproper hEq)
      intro x hxD
      by_contra hxK
      exact hxD.2 (hFEq ▸ (M.subset_closure _ Set.sdiff_subset) ⟨hxD.1, hxK⟩)
  · exact fun hD => IsCocircuit.isHyperplaneCocircuit (show M.IsCocircuit D from hD)

/-- A hyperplane avoiding a ground target is maximal among non-target
sets which do not span that target. -/
theorem IsHyperplane.maximal_target_nonspanning {α : Type*}
    {M : Matroid α} {H : Set α} (hH : M.IsHyperplane H)
    (τ : α) (hτ : τ ∈ M.E \ H) :
    τ ∉ M.closure H ∧
      ∀ B : Set α, H ⊂ B → B ⊆ M.E \ {τ} → τ ∈ M.closure B := by
  constructor
  · rw [hH.1.closure]
    exact hτ.2
  · intro B hHB hB
    have hHcl : H ⊆ M.closure B :=
      hHB.subset.trans (M.subset_closure B (hB.trans Set.sdiff_subset))
    have hflat : M.IsFlat (M.closure B) := M.isFlat_closure B
    rcases hH.2.2 (M.closure B) hflat hHcl with hEq | hEq
    · have hBcl : B ⊆ H := by
        rw [← hEq]
        exact M.subset_closure B (hB.trans Set.sdiff_subset)
      exact False.elim (hHB.not_subset hBcl)
    · rw [hEq]
      exact hτ.1

end Matroid
