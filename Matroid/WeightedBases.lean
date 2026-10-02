import Mathlib.Combinatorics.Matroid.Basic

/-! # WeightedBases -/

open Set

namespace Matroid

/-- Manuscript: prose before `thm:regular-matroid-energy` (N122).
The product omits the distinguished element even for bases containing it. -/
noncomputable def weightedBasesIn {α R : Type*} [CommSemiring R]
    (M : Matroid α) (hE : M.E.Finite) (τ : α) (w : α → R) : R := by
  classical
  exact ∑ B ∈ hE.toFinset.powerset,
    if M.IsBase (B : Set α) ∧ τ ∈ B then ∏ e ∈ B.erase τ, w e else 0

/-- Manuscript: prose before `thm:regular-matroid-energy` (N122).
This is the target-omitting part of the same finite weighted basis sum. -/
noncomputable def weightedBasesOut {α R : Type*} [CommSemiring R]
    (M : Matroid α) (hE : M.E.Finite) (τ : α) (w : α → R) : R := by
  classical
  exact ∑ B ∈ hE.toFinset.powerset,
    if M.IsBase (B : Set α) ∧ τ ∉ B then ∏ e ∈ B.erase τ, w e else 0

end Matroid
