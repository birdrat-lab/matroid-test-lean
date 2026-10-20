import Matroid.R10Certificate
import Matroid.TUWeightedBasisDeterminant

/-! The pointed R10 determinant, with target label zero. -/

namespace Matroid

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Weights for the non-target labels; target zero is suppressed. -/
def r10ZeroedWeight (w : Fin 10 → ℝ) (e : Fin 10) : ℝ :=
  if e = 0 then 0 else w e

/-- The manuscript's `L(x)` in the exact displayed row coordinates. -/
noncomputable def r10PointedL (w : Fin 10 → ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => ∑ e ∈ (Finset.univ : Finset (Fin 10)).erase 0,
    w e * r10Matrix i e * r10Matrix j e

/-- The Gram form of the nine-term rank-one sum. -/
theorem r10PointedL_eq_gram (w : Fin 10 → ℝ) :
    r10PointedL w =
      r10Matrix * Matrix.diagonal (r10ZeroedWeight w) * r10Matrix.transpose := by
  ext i j
  have hsum (f : Fin 10 → ℝ) :
      (∑ e ∈ (Finset.univ : Finset (Fin 10)).erase 0, f e) =
        ∑ e : Fin 10, if e = 0 then 0 else f e := by
    calc
      _ = ∑ e ∈ (Finset.univ : Finset (Fin 10)).filter (· ≠ 0), f e := by
        congr 1
      _ = ∑ e : Fin 10, if e ≠ 0 then f e else 0 := Finset.sum_filter _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro e _
        by_cases he : e = 0 <;> simp [he]
  rw [r10PointedL, hsum]
  simp [Matrix.mul_apply, Matrix.diagonal_apply, r10ZeroedWeight,
    mul_assoc, mul_comm]

private theorem r10Matrix_rows_independent :
    LinearIndependent ℝ r10Matrix.row := by
  apply (linearIndependent_iff_card_eq_finrank_span).2
  rw [Set.finrank, ← Matrix.rank_eq_finrank_span_row, r10Matrix_rank]
  simp

private theorem weightedBasesTotal_zeroed_eq_out (w : Fin 10 → ℝ) :
    weightedBasesTotal r10 r10.ground_finite (r10ZeroedWeight w) =
      weightedBasesOut r10 r10.ground_finite 0 w := by
  classical
  unfold weightedBasesTotal weightedBasesOut
  apply Finset.sum_congr rfl
  intro B hB
  by_cases hbase : r10.IsBase (B : Set (Fin 10))
  · by_cases h0 : (0 : Fin 10) ∈ B
    · simp only [hbase, h0, not_true_eq_false, and_false, ↓reduceIte]
      exact Finset.prod_eq_zero h0 (by simp [r10ZeroedWeight])
    · simp only [hbase, h0, not_false_eq_true, and_true, ↓reduceIte]
      change B.prod (r10ZeroedWeight w) =
        (@Finset.erase (Fin 10) (fun a b => Classical.propDecidable (a = b)) B 0).prod w
      have herase :
          @Finset.erase (Fin 10) (fun a b => Classical.propDecidable (a = b)) B 0 = B :=
        (@Finset.erase_eq_self (Fin 10)
          (fun a b => Classical.propDecidable (a = b)) B 0).2 h0
      have hprod : (∏ e ∈ B, r10ZeroedWeight w e) = ∏ e ∈ B, w e := by
        apply Finset.prod_congr rfl
        intro e he
        have he0 : e ≠ 0 := fun h => h0 (h ▸ he)
        simp [r10ZeroedWeight, he0]
      simpa only [herase] using hprod
  · simp [hbase]

/-- N193: the target-omitting weighted basis sum equals the determinant
of the manuscript's nine-term pointed Gram matrix. -/
theorem r10_weightedBasesOut_eq_det_pointedL (w : Fin 10 → ℝ) :
    weightedBasesOut r10 r10.ground_finite 0 w = (r10PointedL w).det := by
  rw [r10PointedL_eq_gram]
  rw [weightedGram_det_eq_weightedBasesTotal_of_tu r10Matrix
    r10Matrix_isTotallyUnimodular r10Matrix_rows_independent]
  simpa [r10] using (weightedBasesTotal_zeroed_eq_out w).symm

/-- The projected four-row matrix used by the principal cofactor. -/
def r10ProjectedNonTargetMatrix : Matrix (Fin 4) (Fin 10) ℝ :=
  r10Matrix.submatrix Fin.succ id

/-- The `(0,0)` principal cofactor is the determinant of the projected
non-target Gram matrix. This is the matrix-side bridge toward N194. -/
theorem r10PointedL_principalCofactor_eq_projectedGram
    (w : Fin 10 → ℝ) :
    (r10PointedL w).adjugate 0 0 =
      (r10ProjectedNonTargetMatrix *
        Matrix.diagonal (r10ZeroedWeight w) *
        r10ProjectedNonTargetMatrix.transpose).det := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [Fin.val_zero, zero_add, pow_zero, one_mul]
  congr 1
  ext i j
  simp [r10PointedL_eq_gram, r10ProjectedNonTargetMatrix,
    Matrix.mul_apply, Matrix.diagonal_apply, r10ZeroedWeight,
    mul_assoc, mul_comm]

end Matroid
