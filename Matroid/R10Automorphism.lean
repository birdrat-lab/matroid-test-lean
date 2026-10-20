import Matroid.R10Transitivity
import Mathlib.Combinatorics.Matroid.Map

/-! Exact finite type whose cardinality is the N185 manuscript claim.
The 720-element certificate is still missing; these declarations provide
the faithful proof target and preserve the original ten labels. -/

namespace Matroid

/-- A permutation is an R10 automorphism exactly when it preserves the
entire labeled matroid, not merely a chosen collection of generators. -/
def IsR10Automorphism (σ : Equiv.Perm (Fin 10)) : Prop :=
  r10.mapEquiv σ = r10

/-- The exact finite automorphism type underlying the order-720 claim. -/
def R10Automorphism := {σ : Equiv.Perm (Fin 10) // IsR10Automorphism σ}

/-- The manuscript's order-720 assertion is `r10AutomorphismCount = 720`.
No numerical value is asserted by this definition. -/
noncomputable def r10AutomorphismCount : ℕ := Nat.card R10Automorphism

theorem isR10Automorphism_refl : IsR10Automorphism (Equiv.refl (Fin 10)) := by
  simp [IsR10Automorphism, mapEquiv_eq_map]

end Matroid
