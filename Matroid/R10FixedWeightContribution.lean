import Matroid.R10PointedSupports
import Matroid.TwoSumWeights

/-! The two intact-R10 contribution clauses of the manuscript's fixed
weight evaluation. The pointed polynomials are the checked 81-monomial
supports, on every original R10 label. -/

namespace Matroid

open scoped NNReal ENNReal

noncomputable def r10P0 (e : Fin 10) (w : Fin 10 → ℝ≥0) : ℝ≥0 :=
  ∑ B ∈ r10PointedOutSupport e, ∏ x ∈ B, w x

noncomputable def r10P1 (e : Fin 10) (w : Fin 10 → ℝ≥0) : ℝ≥0 :=
  ∑ B ∈ r10PointedInSupport e, ∏ x ∈ B, w x

/-- N215: an intact target-free R10 side contributes its exact pointed
`P₀/P₁` as the port's finite effective weight in N139's two-sum formula.
The identity also holds algebraically when one support sum vanishes. -/
theorem r10_targetFree_effectiveWeight_eq (e : Fin 10)
    (w : Fin 10 → ℝ≥0) :
    twoSumEffectiveWeight r10 r10.ground_finite e w =
      r10P0 e w / r10P1 e w := by
  rw [twoSumEffectiveWeight, r10P0, r10P1,
    r10_weightedBasesOut_eq_support_sum,
    r10_weightedBasesIn_eq_support_sum]

/-- N216: if the intact R10 contains the target, its extended pointed
basis ratio is `P₁/P₀`, with the same checked support polynomials. -/
theorem r10_targetBasisRatio_eq (e : Fin 10)
    (w : Fin 10 → ℝ≥0) :
    (((weightedBasesIn r10 r10.ground_finite e w : ℝ≥0) : ℝ≥0∞) /
      ((weightedBasesOut r10 r10.ground_finite e w : ℝ≥0) : ℝ≥0∞)) =
    ((r10P1 e w : ℝ≥0∞) / (r10P0 e w : ℝ≥0∞)) := by
  rw [r10P0, r10P1,
    r10_weightedBasesOut_eq_support_sum,
    r10_weightedBasesIn_eq_support_sum]

end Matroid
