import Matroid.External.RegularRayleigh

/-! Elementary ratio algebra for N154. The remaining bridge expands the
actual weighted basis sums into the four Rayleigh coefficient classes. -/

namespace Matroid

open scoped NNReal

/-- A Rayleigh cross inequality makes the ratio of two affine,
nonnegative coefficient polynomials nondecreasing, when both denominators
are positive. -/
theorem rayleigh_affine_ratio_mono
    (a b c d x y : ℝ≥0)
    (hray : d * a ≤ c * b) (hxy : x ≤ y)
    (hx : 0 < c + x * d) (hy : 0 < c + y * d) :
    (a + x * b) / (c + x * d) ≤
      (a + y * b) / (c + y * d) := by
  apply (div_le_div_iff₀ hx hy).2
  have hprod : ((0 : ℝ) ≤ ((y : ℝ) - x) *
      ((c : ℝ) * b - d * a)) := by
    apply mul_nonneg
    · exact sub_nonneg.mpr (by exact_mod_cast hxy)
    · exact sub_nonneg.mpr (by exact_mod_cast hray)
  have hcross :
      (a + x * b) * (c + y * d) ≤
        (a + y * b) * (c + x * d) := by
    apply NNReal.coe_le_coe.mp
    push_cast
    nlinarith [hprod]
  exact hcross

end Matroid
