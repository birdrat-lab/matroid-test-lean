import Matroid.FlatsAndCocircuits

/-! The generated modular cut (N035). -/

namespace Matroid

variable {α : Type*} (M : Matroid α) [M.Finite]

/-- An arbitrary intersection of modular cuts is a modular cut. -/
theorem isModularCut_sInter {𝒮 : Set (Set (Set α))}
    (hne : 𝒮.Nonempty) (h𝒮 : ∀ 𝒞 ∈ 𝒮, M.IsModularCut 𝒞) :
    M.IsModularCut (⋂₀ 𝒮) := by
  refine ⟨?_, ?_, ?_⟩
  · intro F hF
    obtain ⟨𝒞, h𝒞⟩ := hne
    exact (h𝒮 𝒞 h𝒞).1 F (Set.mem_sInter.mp hF 𝒞 h𝒞)
  · intro F G hF hFG hG 𝒞 h𝒞
    exact (h𝒮 𝒞 h𝒞).2.1 (Set.mem_sInter.mp hF 𝒞 h𝒞) hFG hG
  · intro F G hF hG hmod 𝒞 h𝒞
    exact (h𝒮 𝒞 h𝒞).2.2 (Set.mem_sInter.mp hF 𝒞 h𝒞)
      (Set.mem_sInter.mp hG 𝒞 h𝒞) hmod

/-- The collection of all flats is a modular cut. -/
theorem allFlats_isModularCut : M.IsModularCut {F | M.IsFlat F} := by
  refine ⟨?_, ?_, ?_⟩
  · intro F hF
    exact hF
  · intro F G _ _ hG
    exact hG
  · intro F G hF hG _
    rw [Set.inter_eq_iInter]
    exact
      (Matroid.IsFlat.iInter (M := M) (Fs := fun b : Bool => cond b F G)
        (by intro b; cases b <;> assumption))

/-- The smallest modular cut containing a given collection of flats. -/
def generatedModularCut (𝒜 : Set (Set α)) : Set (Set α) :=
  ⋂₀ {𝒞 | M.IsModularCut 𝒞 ∧ 𝒜 ⊆ 𝒞}

theorem generatedModularCut_isModularCut (𝒜 : Set (Set α))
    (h𝒜 : ∀ F ∈ 𝒜, M.IsFlat F) :
    M.IsModularCut (M.generatedModularCut 𝒜) := by
  apply M.isModularCut_sInter
  · exact ⟨{F | M.IsFlat F}, M.allFlats_isModularCut, h𝒜⟩
  intro 𝒞 h𝒞
  exact h𝒞.1

theorem subset_generatedModularCut {𝒜 : Set (Set α)}
    (_h𝒜 : ∀ F ∈ 𝒜, M.IsFlat F) : 𝒜 ⊆ M.generatedModularCut 𝒜 := by
  intro F hF 𝒞 h𝒞
  exact h𝒞.2 hF

theorem generatedModularCut_least {𝒜 𝒞 : Set (Set α)}
    (h𝒞 : M.IsModularCut 𝒞) (hsub : 𝒜 ⊆ 𝒞) :
    M.generatedModularCut 𝒜 ⊆ 𝒞 := by
  intro F hF
  exact Set.mem_sInter.mp hF 𝒞 ⟨h𝒞, hsub⟩

end Matroid
