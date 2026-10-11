import Matroid.WeightedCauchyBinet
import Mathlib.Basic.Real.Basic

/-! Real specialization of the locally proved weighted Cauchy--Binet theorem. -/

namespace Matrix

/-- Real specialization of Choe–Oxley–Sokal–Wagner,
*Homogeneous multivariate polynomials with the half-plane property* (2004),
§8.1, Theorem 8.1(b), with the rectangular Cauchy–Binet formula stated in
footnote 12. Their complex `r × n` matrix and `A*` specialize to this real
`Fin k × Fin n` matrix and transpose. The subset is enumerated increasingly;
its determinant square is independent of that enumeration. The proof is the
finite-index grouping in `Matrix.weightedCauchyBinet`. -/
theorem weightedCauchyBinet_real
    {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (w : Fin n → ℝ) :
    (A * diagonal w * Aᵀ).det =
      ∑ s : {S : Finset (Fin n) // S.card = k},
        (A.submatrix id (orderedColumnIndex s)).det ^ 2 *
          ∏ j ∈ s.1, w j := by
  exact weightedCauchyBinet A w

end Matrix
