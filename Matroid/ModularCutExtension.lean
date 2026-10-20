import Matroid.External.CrapoExtension

/-! The manuscript's labeled modular-cut extension correspondence (N037). -/

namespace Matroid

variable {α : Type*} (N : Matroid α) [N.Finite] (τ : α)

/-- For every labeled extension, the flats spanning the new element form a
modular cut. This applies to loops and coloops. -/
theorem extension_modularCut {M : Matroid α}
    (h : IsSingleElementExtension N M τ) :
    N.IsModularCut {F | N.IsFlat F ∧ τ ∈ M.closure F} :=
  External.extensionCut_isModularCut N τ h

/-- Every modular cut determines exactly one extension on the specified
ground set, with the specified fresh label. -/
theorem modularCut_extension_unique (hτ : τ ∉ N.E)
    {𝒞 : Set (Set α)} (h𝒞 : N.IsModularCut 𝒞) :
    ∃! M : Matroid α,
      IsSingleElementExtension N M τ ∧
        {F | N.IsFlat F ∧ τ ∈ M.closure F} = 𝒞 :=
  External.modularCut_unique_extension N τ hτ h𝒞

end Matroid
