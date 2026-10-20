import Matroid.EffectiveWeightHomogeneity

/-!
Source: Choe and Wagner, *Rayleigh Matroids*, Theorem 5.2 (Choe),
arXiv:math/0307096, pp. 15–16. The theorem gives nonnegativity of the
Rayleigh difference for sixth-root-of-unity matroids at arbitrary real
weights. Proposition 5.1 and Theorem 5.5 include regular matroids.
The four classes below are the coefficients of the basis-generating
polynomial according to membership of two distinct labels. The source
inequality is `A₁₀*A₀₁ ≥ A₁₁*A₀₀` at nonnegative weights (a specialization
of its arbitrary-real assertion). No ratio monotonicity is assumed here.
-/

namespace Matroid

open scoped NNReal

/-- Weighted basis coefficient with fixed membership of two labels;
both distinguished weights are omitted from each product. -/
noncomputable def weightedPairClass {α : Type*} (M : Matroid α)
    (hE : M.E.Finite) (p e : α) (bp be : Bool)
    (w : α → ℝ≥0) : ℝ≥0 := by
  classical
  exact ∑ B ∈ hE.toFinset.powerset,
    if M.IsBase (B : Set α) ∧ (p ∈ B) = bp ∧ (e ∈ B) = be
      then ∏ x ∈ (B.erase p).erase e, w x else 0

namespace External

universe u w

/-- The regular-matroid Rayleigh difference, specialized to nonnegative
weights on a finite ground. The cited theorem applies to arbitrary real
weights and therefore includes this specialization. -/
theorem regular_rayleigh_pair {α : Type u} (M : Matroid α)
    [M.Finite] (hM : Regular.{u, 0, w} M)
    (p e : α) (hpE : p ∈ M.E) (heE : e ∈ M.E)
    (hne : p ≠ e) (weights : α → ℝ≥0) :
    weightedPairClass M M.ground_finite p e true false weights *
        weightedPairClass M M.ground_finite p e false true weights ≥
      weightedPairClass M M.ground_finite p e true true weights *
        weightedPairClass M M.ground_finite p e false false weights := by
  sorry

end External
end Matroid
