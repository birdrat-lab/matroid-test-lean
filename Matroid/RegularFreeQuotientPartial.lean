import Matroid.TotallyUnimodular

/-! The matrix-kernel step of `thm:regular-quotient-form` (N059).
The indexed matroid contraction and free-deletion construction remain open. -/

namespace Matroid

/-- The manuscript's block `K = (-D; I)` lies in the kernel of the
standard-form matrix `A = (I D)`, with the row and column labels explicit. -/
theorem standardForm_mul_kernelBlock
    {r c : Type*} [Fintype r] [Fintype c]
    [DecidableEq r] [DecidableEq c] (D : Matrix r c ℝ) :
    Matrix.fromCols (1 : Matrix r r ℝ) D *
      Matrix.fromRows (-D) (1 : Matrix c c ℝ) = 0 := by
  rw [Matrix.fromCols_mul_fromRows]
  simp

end Matroid
