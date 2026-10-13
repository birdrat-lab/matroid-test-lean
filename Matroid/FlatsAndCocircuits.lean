import Matroid.Depth6Basics

/-! Manuscript definitions of cocircuits through hyperplanes and modular cuts. -/

namespace Matroid

variable {α : Type*} (M : Matroid α)

/-- N018: a cocircuit in the manuscript is the complement, within the
actual ground set, of a maximal proper flat. -/
def IsHyperplaneCocircuit (C : Set α) : Prop :=
  ∃ H : Set α, M.IsHyperplane H ∧ C = M.E \ H

theorem isHyperplaneCocircuit_iff (C : Set α) :
    M.IsHyperplaneCocircuit C ↔
      ∃ H : Set α, M.IsHyperplane H ∧ C = M.E \ H :=
  Iff.rfl

/-- N034: exactly the two modular-cut axioms on a collection of flats.
The first field records that every member is a flat; the other two record
upward closure among flats and modular-pair intersection closure. -/
def IsModularCut [M.Finite] (𝒞 : Set (Set α)) : Prop :=
  (∀ F ∈ 𝒞, M.IsFlat F) ∧
  (∀ ⦃F G : Set α⦄, F ∈ 𝒞 → F ⊆ G → M.IsFlat G → G ∈ 𝒞) ∧
  (∀ ⦃F G : Set α⦄, F ∈ 𝒞 → G ∈ 𝒞 → M.IsModularPair F G → F ∩ G ∈ 𝒞)

end Matroid
