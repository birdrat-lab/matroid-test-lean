import Matroid.NegativeSupport
import Matroid.FlatsAndCocircuits

/-! The maximal-negative-set step of `lem:r10-boundary-inputs` (N263). -/

namespace Matroid

/-- N263: a maximal set of non-target elements that does not span a
ground target is a hyperplane avoiding that target, and its complement
is a target cocircuit. -/
theorem maximal_nonspanning_isHyperplane {α : Type*}
    (M : Matroid α) (τ : α) (A : Set α)
    (hτ : τ ∈ M.E) (hA : A ⊆ M.E \ {τ})
    (hnot : τ ∉ M.closure A)
    (hmax : ∀ B : Set α, A ⊂ B → B ⊆ M.E \ {τ} →
      τ ∈ M.closure B) :
    M.IsHyperplane A ∧
      M.IsCocircuit (M.E \ A) ∧ τ ∈ M.E \ A := by
  obtain ⟨D, hD, hτD, hDA⟩ :=
    M.cocircuit_separates_closure A τ
      (hA.trans Set.sdiff_subset) hτ hnot
  have hAD : A ⊆ M.E \ D := by
    intro x hxA
    exact ⟨(hA hxA).1, fun hxD =>
      (Set.disjoint_left.mp hDA) hxD hxA⟩
  have hτcl : τ ∉ M.closure (M.E \ D) := by
    have hH := hyperplane_compl_of_isCocircuit M hD
    rw [hH.1.closure]
    exact fun h => h.2 hτD
  have hEq : A = M.E \ D := by
    by_contra hne
    have hproper : A ⊂ M.E \ D := Set.ssubset_iff_subset_ne.mpr ⟨hAD, hne⟩
    exact hτcl (hmax (M.E \ D) hproper (by
      intro x hx
      exact ⟨hx.1, fun hτx => hx.2 (hτx ▸ hτD)⟩))
  subst A
  have hH := hyperplane_compl_of_isCocircuit M hD
  have hcompl : M.E \ (M.E \ D) = D := by
    ext x
    simp [hD.subset_ground]
  refine ⟨hH, ?_, ?_⟩
  · rwa [hcompl]
  · exact ⟨hτ, fun h => h.2 hτD⟩

/-- The same maximal-negative conclusion in the manuscript's N018
hyperplane-complement cocircuit predicate. -/
theorem maximal_nonspanning_isHyperplaneCocircuit {α : Type*}
    (M : Matroid α) (τ : α) (A : Set α)
    (hτ : τ ∈ M.E) (hA : A ⊆ M.E \ {τ})
    (hnot : τ ∉ M.closure A)
    (hmax : ∀ B : Set α, A ⊂ B → B ⊆ M.E \ {τ} →
      τ ∈ M.closure B) :
    M.IsHyperplaneCocircuit (M.E \ A) := by
  refine ⟨A, (M.maximal_nonspanning_isHyperplane τ A hτ hA hnot hmax).1, rfl⟩

end Matroid
