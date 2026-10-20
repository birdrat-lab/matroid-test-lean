import Matroid.Depth6TriangleWeights
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! The final polynomial step of the manuscript's triangle identity.
The determinant and weighted-basis coefficient comparison remain open. -/

namespace Matroid

/-- Once the determinant coefficients have been identified, their five
classes satisfy the triangle relation by polynomial algebra. -/
theorem triangle_identity_of_det_coefficients
    (a p₁ p₂ p₃ c A B s : ℝ)
    (hp₁ : p₁ = a * (B + s))
    (hp₂ : p₂ = a * (A + s))
    (hp₃ : p₃ = -a * s)
    (hc : c = a * (A * B - s ^ 2)) :
    a * c = p₁ * p₂ + p₁ * p₃ + p₂ * p₃ := by
  rw [hp₁, hp₂, hp₃, hc]
  ring

/-- Coefficient extraction from the rank-two determinant update. The
remaining representation step must prove this polynomial equality for the
actual weighted TU matrix and identify its coefficients with the five
closure-class sums; this lemma does not assume that identification. -/
theorem triangle_identity_of_rank_two_polynomial
    (a p₁ p₂ p₃ c A B s : ℝ)
    (hpoly : ∀ x₁ x₂ x₃ : ℝ,
      a + (p₂ + p₃) * x₁ + (p₁ + p₃) * x₂ +
          (p₁ + p₂) * x₃ + c * (x₁ * x₂ + x₁ * x₃ + x₂ * x₃) =
        a * (1 + A * x₁ + B * x₂ + (A + B + 2 * s) * x₃ +
          (A * B - s ^ 2) * (x₁ * x₂ + x₁ * x₃ + x₂ * x₃))) :
    a * c = p₁ * p₂ + p₁ * p₃ + p₂ * p₃ := by
  have h100 := hpoly 1 0 0
  have h010 := hpoly 0 1 0
  have h001 := hpoly 0 0 1
  have h110 := hpoly 1 1 0
  have hp₃ : p₃ = -a * s := by nlinarith [h100, h010, h001]
  have hp₁ : p₁ = a * (B + s) := by nlinarith [h010, hp₃]
  have hp₂ : p₂ = a * (A + s) := by nlinarith [h100, hp₃]
  have hc : c = a * (A * B - s ^ 2) := by nlinarith [h100, h010, h110]
  exact triangle_identity_of_det_coefficients a p₁ p₂ p₃ c A B s hp₁ hp₂ hp₃ hc

end Matroid
