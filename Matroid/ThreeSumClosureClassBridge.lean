import Matroid.External.ThreeSumBases

/-! Checked local pieces of the manuscript's N159 closure-class translation.
The full three-family compatibility equivalence is still open. -/

namespace Matroid

/-- The proper three-sum cocircuit exclusion is exactly coindependence of
the common triangle on the first side. -/
theorem IsProperThreeSum.left_coindep {α : Type*}
    {M N P : Matroid α} {T : Set α}
    (h : IsProperThreeSum M N P T) : M.Coindep T := by
  have hTE : T ⊆ M.E := by
    intro e he
    exact (h.1.symm ▸ he).1
  refine M.coindep_iff_forall_subset_not_isCocircuit.mpr ⟨?_, hTE⟩
  intro K hKT hK
  exact (h.2.2.2.2.1 K hK) hKT

/-- The same coindependence is available on the second labeled side. -/
theorem IsProperThreeSum.right_coindep {α : Type*}
    {M N P : Matroid α} {T : Set α}
    (h : IsProperThreeSum M N P T) : N.Coindep T := by
  have hTE : T ⊆ N.E := by
    intro e he
    exact (h.1.symm ▸ he).2
  refine N.coindep_iff_forall_subset_not_isCocircuit.mpr ⟨?_, hTE⟩
  intro K hKT hK
  exact (h.2.2.2.2.2.1 K hK) hKT

/-- The deletion-base family in the cited 3-sum formula is precisely the
all-triangle closure class under the manuscript's side-independence and
`S ∪ T` spanning conditions. -/
theorem coindep_delete_isBase_iff_closure_all {α : Type*}
    (M : Matroid α) (T S : Set α)
    (hT : M.Coindep T) (hS : S ⊆ M.E \ T)
    (hspan : M.closure (S ∪ T) = M.E) :
    (M ＼ T).IsBase S ↔ M.Indep S ∧ M.closure S ∩ T = T := by
  constructor
  · intro hB
    have hB' := (hT.delete_isBase_iff).mp hB
    refine ⟨hB'.1.indep, ?_⟩
    rw [hB'.1.closure_eq]
    exact Set.inter_eq_self_of_subset_right hT.subset_ground
  · rintro ⟨hI, hclass⟩
    have hTcl : T ⊆ M.closure S := by
      intro e he
      exact (hclass.symm ▸ he).1
    have hUnion : S ∪ T ⊆ M.closure S :=
      Set.union_subset (M.subset_closure S hI.subset_ground) hTcl
    have hEcl : M.E ⊆ M.closure S := by
      rw [← hspan]
      exact M.closure_subset_closure_of_subset_closure hUnion
    apply (hT.delete_isBase_iff).mpr
    exact ⟨hI.isBase_of_ground_subset_closure hEcl,
      Set.disjoint_left.mpr (fun e heS heT => (hS heS).2 heT)⟩

end Matroid
