import Matroid.Representation
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Basic.Real.Basic

/-! # The exceptional ten-element matroid R10 -/

namespace Matroid

/-- Manuscript `def:r10` and `fig:r10-k33` (N070). Rows are indexed
`0,...,4` and columns `0,...,9` in the manuscript's displayed order. -/
def r10IntegerMatrix : Matrix (Fin 5) (Fin 10) ℤ :=
  !![1, 0, 0, 0, 0, -1, 1, 0, 0, 1;
     0, 1, 0, 0, 0, 1, -1, 1, 0, 0;
     0, 0, 1, 0, 0, 0, 1, -1, 1, 0;
     0, 0, 0, 1, 0, 0, 0, 1, -1, 1;
     0, 0, 0, 0, 1, 1, 0, 0, 1, -1]

/-- Manuscript `def:r10` (N070): the exact real coordinate matrix. -/
def r10Matrix : Matrix (Fin 5) (Fin 10) ℝ :=
  r10IntegerMatrix.map (Int.castRingHom ℝ)

/-- The first five displayed columns are the identity block. -/
theorem r10IntegerMatrix_left :
    r10IntegerMatrix.submatrix id (Fin.castAdd 5) = 1 := by
  decide

/-- The real coordinate matrix has the same identity block. -/
theorem r10Matrix_left : r10Matrix.submatrix id (Fin.castAdd 5) = 1 := by
  ext i j
  have h := congrArg (fun X : Matrix (Fin 5) (Fin 5) ℤ => X i j)
    r10IntegerMatrix_left
  simpa [r10Matrix, Matrix.submatrix_apply, Matrix.one_apply] using
    congrArg (fun z : ℤ => (z : ℝ)) h

/-- Manuscript `def:r10` (N070): the represented matroid has the column
labels `0,...,9` exactly as displayed. -/
noncomputable def r10 : Matroid (Fin 10) :=
  vectorMatroid (K := ℝ) Set.univ Set.finite_univ r10Matrix.col

@[simp] theorem r10_ground : r10.E = Set.univ := by
  simp [r10]

/-- The ten manuscript labels are distinct elements of the ground set. -/
theorem r10_ground_card : r10.E.ncard = 10 := by
  rw [r10_ground]
  simp

end Matroid
