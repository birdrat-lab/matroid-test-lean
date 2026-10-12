import Matroid.Representation
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Rank
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

/-- N070: the displayed matrix has rank exactly five. The identity left
block gives the lower bound, and its five rows give the upper bound. -/
theorem r10Matrix_rank : r10Matrix.rank = 5 := by
  apply le_antisymm
  · simpa using Matrix.rank_le_card_height r10Matrix
  · have h := Matrix.rank_submatrix_le r10Matrix id (Fin.castAdd 5)
    rw [r10Matrix_left, Matrix.rank_one] at h
    simpa using h

/-- The represented ten-element matroid has rank five. -/
theorem r10_eRank : r10.eRank = (5 : ℕ∞) := by
  have hrep := vectorMatroid_represents (K := ℝ) Set.univ
    Set.finite_univ r10Matrix.col
  have h := hrep.eRk_eq_finrank_span Set.univ (by simp)
  rw [← r10.eRk_univ_eq]
  change (vectorMatroid (K := ℝ) Set.univ Set.finite_univ
    r10Matrix.col).eRk Set.univ = _
  rw [h]
  have hcast := congrArg (fun n : ℕ => (n : ℕ∞)) r10Matrix_rank
  rw [Matrix.rank_eq_finrank_span_cols] at hcast
  rw [Set.image_univ]
  simpa using hcast

end Matroid
