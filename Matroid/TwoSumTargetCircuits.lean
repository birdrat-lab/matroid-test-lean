import Matroid.External.TwoSumCircuits

/-! The target-facing circuit classification used by the recursive closure
proof. This local specialization is complete relative to Oxley's cited
two-sum circuit theorem. -/

namespace Matroid

universe u w

theorem regularTwoSum_targetCircuit_iff {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p τ : α) (hinter : M.E ∩ N.E = {p})
    (hτ : τ ∈ M.E \ {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard)
    (C : Set α) :
    (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN).IsCircuit C ∧ τ ∈ C ↔
      (M.IsCircuit C ∧ p ∉ C ∧ τ ∈ C) ∨
      ∃ C₁ C₂ : Set α, M.IsCircuit C₁ ∧ N.IsCircuit C₂ ∧
        p ∈ C₁ ∧ p ∈ C₂ ∧ τ ∈ C₁ ∧ C = (C₁ ∪ C₂) \ {p} := by
  have hτN : τ ∉ N.E := by
    intro hNτ
    have hpt : τ = p := by
      have : τ ∈ M.E ∩ N.E := ⟨hτ.1, hNτ⟩
      simpa [hinter] using this
    exact hτ.2 (by simpa [hpt])
  rw [External.regularTwoSum_isCircuit_iff M N hM hN p hinter
    hlM hlN hcM hcN hnM hnN C]
  constructor
  · rintro ⟨hC, hτC⟩
    rcases hC with hC | hC | ⟨C₁, C₂, hC₁, hC₂, hp₁, hp₂, rfl⟩
    · exact Or.inl ⟨hC.1, hC.2, hτC⟩
    · exact False.elim (hτN (hC.1.subset_ground hτC))
    · have hτunion : τ ∈ C₁ ∪ C₂ := hτC.1
      have hτC₁ : τ ∈ C₁ := by
        rcases hτunion with h | h
        · exact h
        · exact False.elim (hτN (hC₂.subset_ground h))
      exact Or.inr ⟨C₁, C₂, hC₁, hC₂, hp₁, hp₂, hτC₁, rfl⟩
  · intro h
    rcases h with ⟨hC, hp, hτC⟩ | ⟨C₁, C₂, hC₁, hC₂, hp₁, hp₂, hτC₁, rfl⟩
    · exact ⟨Or.inl ⟨hC, hp⟩, hτC⟩
    · refine ⟨Or.inr (Or.inr ⟨C₁, C₂, hC₁, hC₂, hp₁, hp₂, rfl⟩), ?_⟩
      exact ⟨Or.inl hτC₁, hτ.2⟩

end Matroid
