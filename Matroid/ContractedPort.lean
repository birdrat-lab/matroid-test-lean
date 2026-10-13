import Matroid.Depth6Basics
import Matroid.OneSumWeights

/-! Spanned ports become loops after contraction, with the extended ratio. -/

open scoped NNReal ENNReal

namespace Matroid

/-- N144, matroidal core: a target outside the contracted set that was
spanned before contraction is a loop afterward. -/
theorem contractedPort_isLoop {α : Type*} (M : Matroid α)
    {A : Set α} {p : α} (hp : p ∈ M.closure A) (hpA : p ∉ A) :
    (M ／ A).IsLoop p :=
  M.isLoop_contract_of_mem_closure hp hpA

/-- N144's extended-weight convention. Positive weights on the surviving
non-target ground elements make the `P₀/P₁` port ratio infinite. -/
theorem contractedPort_ratio_eq_top {α : Type*} (M : Matroid α)
    {A : Set α} {p : α} (hE' : (M ／ A).E.Finite)
    (hp : p ∈ M.closure A) (hpA : p ∉ A)
    (w : α → ℝ≥0)
    (hw : ∀ e ∈ (M ／ A).E, e ≠ p → 0 < w e) :
    ((weightedBasesOut (M ／ A) hE' p w : ℝ≥0) : ℝ≥0∞) /
      ((weightedBasesIn (M ／ A) hE' p w : ℝ≥0) : ℝ≥0∞) = ∞ := by
  exact twoSumPortRatio_eq_top_of_isLoop (M ／ A) hE' p w hw
    (M.contractedPort_isLoop hp hpA)

end Matroid
