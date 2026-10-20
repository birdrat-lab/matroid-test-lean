import Matroid.External.TwoSumCocircuits
import Matroid.DualCocircuit

/-! The target-facing cocircuit classification in the manuscript's
hyperplane-complement convention. -/

namespace Matroid

universe u w

theorem regularTwoSum_targetCocircuit_iff {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p τ : α) (hinter : M.E ∩ N.E = {p})
    (hτ : τ ∈ M.E \ {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard)
    (D : Set α) :
    (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN).IsHyperplaneCocircuit D ∧
      τ ∈ D ↔
      (M.IsHyperplaneCocircuit D ∧ p ∉ D ∧ τ ∈ D) ∨
      ∃ D₁ D₂ : Set α,
        M.IsHyperplaneCocircuit D₁ ∧ N.IsHyperplaneCocircuit D₂ ∧
        p ∈ D₁ ∧ p ∈ D₂ ∧ τ ∈ D₁ ∧ D = (D₁ ∪ D₂) \ {p} := by
  have hτN : τ ∉ N.E := by
    intro hNτ
    have hpt : τ = p := by
      have : τ ∈ M.E ∩ N.E := ⟨hτ.1, hNτ⟩
      simpa [hinter] using this
    exact hτ.2 (by simpa [hpt])
  simp only [isHyperplaneCocircuit_iff_dual_isCircuit] 
  change (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN).IsCocircuit D ∧
      τ ∈ D ↔
      (M.IsCocircuit D ∧ p ∉ D ∧ τ ∈ D) ∨
      ∃ D₁ D₂ : Set α,
        M.IsCocircuit D₁ ∧ N.IsCocircuit D₂ ∧
        p ∈ D₁ ∧ p ∈ D₂ ∧ τ ∈ D₁ ∧ D = (D₁ ∪ D₂) \ {p}
  rw [External.regularTwoSum_isCocircuit_iff M N hM hN p hinter
    hlM hlN hcM hcN hnM hnN D]
  constructor
  · rintro ⟨hD, hτD⟩
    rcases hD with hD | hD | ⟨D₁, D₂, hD₁, hD₂, hp₁, hp₂, rfl⟩
    · exact Or.inl ⟨hD.1, hD.2, hτD⟩
    · exact False.elim (hτN (hD.1.subset_ground hτD))
    · have hτunion : τ ∈ D₁ ∪ D₂ := hτD.1
      have hτD₁ : τ ∈ D₁ := by
        rcases hτunion with h | h
        · exact h
        · exact False.elim (hτN (hD₂.subset_ground h))
      exact Or.inr ⟨D₁, D₂, hD₁, hD₂, hp₁, hp₂, hτD₁, rfl⟩
  · intro h
    rcases h with ⟨hD, hp, hτD⟩ | ⟨D₁, D₂, hD₁, hD₂, hp₁, hp₂, hτD₁, rfl⟩
    · exact ⟨Or.inl ⟨hD, hp⟩, hτD⟩
    · refine ⟨Or.inr (Or.inr ⟨D₁, D₂, hD₁, hD₂, hp₁, hp₂, rfl⟩), ?_⟩
      exact ⟨Or.inl hτD₁, hτ.2⟩

end Matroid
