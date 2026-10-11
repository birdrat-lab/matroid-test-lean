import Mathlib.Combinatorics.Matroid.Minor.Restrict
import Mathlib.Combinatorics.Matroid.Rank.ENat

/-! # Single-element extensions -/

namespace Matroid

/-- Manuscript: `def:single-element-extension` (N036). -/
def IsSingleElementExtension {α : Type*} (N M : Matroid α) (τ : α) : Prop :=
  τ ∉ N.E ∧ M.E = insert τ N.E ∧ M ↾ N.E = N

/-- Manuscript `prop:target-extension-criterion` (N041): closing a set in
the old matroid preserves its rank in the extension and whether it spans
the added target. This holds even when the set is dependent. -/
theorem IsSingleElementExtension.closure_rank_and_target
    {α : Type*} {N M : Matroid α} {τ : α}
    (h : IsSingleElementExtension N M τ) {A : Set α} (hA : A ⊆ N.E) :
    M.eRk A = M.eRk (N.closure A) ∧
      (τ ∈ M.closure A ↔ τ ∈ M.closure (N.closure A)) := by
  have hNE : N.E ⊆ M.E := by
    rw [h.2.1]
    exact Set.subset_insert τ N.E
  have hcl : N.closure A = M.closure A ∩ N.E := by
    calc
      N.closure A = (M ↾ N.E).closure A := by rw [h.2.2]
      _ = M.closure A ∩ N.E := M.restrict_closure_eq hA hNE
  have hAcl : A ⊆ N.closure A := N.subset_closure A hA
  have hclM : N.closure A ⊆ M.closure A := by
    rw [hcl]
    exact Set.inter_subset_left
  have hclosure : M.closure A = M.closure (N.closure A) := by
    apply Set.Subset.antisymm
    · exact M.closure_subset_closure hAcl
    · simpa only [M.closure_closure] using M.closure_subset_closure hclM
  have hrA : N.eRk A = M.eRk A := by
    simpa only [h.2.2] using (M.restrict_eRk_eq hA)
  have hrC : N.eRk (N.closure A) = M.eRk (N.closure A) := by
    simpa only [h.2.2] using (M.restrict_eRk_eq (N.closure_subset_ground A))
  constructor
  · rw [← hrA, ← hrC]
    exact (N.eRk_closure_eq A).symm
  · rw [hclosure]

end Matroid
