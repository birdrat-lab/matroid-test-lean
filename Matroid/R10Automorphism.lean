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

/-- An exact basis-level acceptance criterion for a prospective finite
automorphism certificate. It checks all bases on the original ten labels. -/
theorem isR10Automorphism_iff_preserves_bases
    (σ : Equiv.Perm (Fin 10)) :
    IsR10Automorphism σ ↔
      ∀ B : Set (Fin 10), r10.IsBase B ↔ r10.IsBase (σ.symm '' B) := by
  constructor
  · intro h B
    have hB : (r10.mapEquiv σ).IsBase B ↔ r10.IsBase B := by
      rw [h]
    simpa only [mapEquiv_isBase_iff] using hB.symm
  · intro h
    apply ext_isBase
    · simp [r10_ground]
    · intro B _
      simpa only [mapEquiv_isBase_iff] using (h B).symm

/-- The same exact criterion indexed by the finite collection of subsets of
the displayed ten-element ground. This is the finite-checker interface. -/
theorem isR10Automorphism_iff_finset_bases
    (σ : Equiv.Perm (Fin 10)) :
    IsR10Automorphism σ ↔
      ∀ B : Finset (Fin 10),
        r10.IsBase (B : Set (Fin 10)) ↔
          r10.IsBase (σ.symm '' (B : Set (Fin 10))) := by
  rw [isR10Automorphism_iff_preserves_bases]
  constructor
  · intro h B
    exact h B
  · intro h B
    have hfin : B.Finite := Set.toFinite B
    simpa only [Set.Finite.coe_toFinset] using h hfin.toFinset

end Matroid
