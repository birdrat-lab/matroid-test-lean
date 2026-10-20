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

/-- The lower identity block makes the kernel-block column map injective. -/
theorem standardForm_kernelBlock_injective
    {r c : Type*} [Fintype r] [Fintype c]
    [DecidableEq r] [DecidableEq c] (D : Matrix r c ℝ) :
    Function.Injective
      (Matrix.fromRows (-D) (1 : Matrix c c ℝ)).mulVec := by
  intro v w h
  funext j
  have hj := congrFun h (Sum.inr j)
  simpa [Matrix.fromRows_mulVec] using hj

/-- In standard form, every vector in the kernel of `(I D)` is uniquely
represented by the displayed block `(-D; I)`. This is the manuscript's
unlabeled linear-algebra step; the labeled matroid extension remains open. -/
theorem standardForm_kernelBlock_surjOn_kernel
    {r c : Type*} [Fintype r] [Fintype c]
    [DecidableEq r] [DecidableEq c] (D : Matrix r c ℝ)
    (z : r ⊕ c → ℝ)
    (hz : (Matrix.fromCols (1 : Matrix r r ℝ) D).mulVec z = 0) :
    ∃ v : c → ℝ,
      (Matrix.fromRows (-D) (1 : Matrix c c ℝ)).mulVec v = z := by
  let v : c → ℝ := z ∘ Sum.inr
  have hleft : z ∘ Sum.inl = -D.mulVec v := by
    have h := hz
    rw [Matrix.fromCols_mulVec] at h
    simpa [v, Matrix.neg_mulVec] using eq_neg_of_add_eq_zero_left h
  refine ⟨v, ?_⟩
  funext x
  rcases x with i | j
  · have hi := congrFun hleft i
    simpa [Matrix.fromRows_mulVec, Matrix.neg_mulVec] using hi.symm
  · simp [Matrix.fromRows_mulVec, v]

/-- The displayed augmentation `Â = (I K)` maps through the standard-form
quotient exactly as its original-coordinate block. Thus added relation
coordinates disappear under the proposed quotient map; this is the
linear-algebra identity needed before the labeled matroid contraction. -/
theorem standardForm_augmented_mulVec_quotient
    {r c : Type*} [Fintype r] [Fintype c]
    [DecidableEq r] [DecidableEq c] (D : Matrix r c ℝ)
    (v : r ⊕ c → ℝ) (w : c → ℝ) :
    (Matrix.fromCols (1 : Matrix r r ℝ) D).mulVec
      ((Matrix.fromCols (1 : Matrix (r ⊕ c) (r ⊕ c) ℝ)
        (Matrix.fromRows (-D) (1 : Matrix c c ℝ))).mulVec
          (Sum.elim v w)) =
      (Matrix.fromCols (1 : Matrix r r ℝ) D).mulVec v := by
  rw [Matrix.fromCols_mulVec_sumElim]
  simp only [Matrix.one_mulVec]
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
  rw [standardForm_mul_kernelBlock]
  simp

end Matroid
