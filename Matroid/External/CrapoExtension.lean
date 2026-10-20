import Matroid.Extensions
import Matroid.FlatsAndCocircuits

/-! Oxley, *Matroid Theory*, 2nd ed., Lemma 7.2.2 and Theorem 7.2.3,
printed pp. 266–268. The cited result classifies extensions on the fixed
ground set `N.E ∪ {τ}`. On a flat `F` of `N`, Oxley's criterion that
`F ∪ {τ}` is a flat of the extension of the same rank is equivalent to
`τ ∈ M.closure F`; restriction gives `M.closure F ∩ N.E = F`.
The empty and full cuts are allowed. No representability or simplicity
condition is imposed. -/

namespace Matroid.External

variable {α : Type*} (N : Matroid α) [N.Finite] (τ : α)

/-- The modular cut associated to a labeled single-element extension. -/
def extensionCut (M : Matroid α) : Set (Set α) :=
  {F | N.IsFlat F ∧ τ ∈ M.closure F}

/-- Oxley, Lemma 7.2.2: an extension gives a modular cut. -/
theorem extensionCut_isModularCut {M : Matroid α}
    (h : IsSingleElementExtension N M τ) :
    N.IsModularCut (extensionCut N τ M) := by
  sorry

/-- Oxley, Theorem 7.2.3: every modular cut determines a unique
extension with the same fixed labels. -/
theorem modularCut_unique_extension (hτ : τ ∉ N.E)
    {𝒞 : Set (Set α)} (h𝒞 : N.IsModularCut 𝒞) :
    ∃! M : Matroid α,
      IsSingleElementExtension N M τ ∧ extensionCut N τ M = 𝒞 := by
  sorry

end Matroid.External
