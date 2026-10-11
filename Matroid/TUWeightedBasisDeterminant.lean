import Matroid.External.WeightedCauchyBinet
import Matroid.WeightedBases
import Matroid.Representation
import Mathlib.Combinatorics.Matroid.Rank.ENat

/-! Filtering weighted maximal minors into the represented basis sum. -/

namespace Matroid

attribute [local instance] Classical.propDecidable

private theorem vectorMatroid_eRank_eq_rowCount
    {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (hrow : LinearIndependent ℝ A.row) :
    (vectorMatroid (K := ℝ) (Set.univ : Set (Fin n)) Set.finite_univ A.col).eRank =
      (k : ℕ∞) := by
  let M := vectorMatroid (K := ℝ) (Set.univ : Set (Fin n)) Set.finite_univ A.col
  have hrep : M.Represents (K := ℝ) A.col :=
    vectorMatroid_represents _ _ _
  have h := hrep.eRk_eq_finrank_span Set.univ (by simp [M])
  rw [M.eRk_univ_eq] at h
  have hrange : A.col '' (Set.univ : Set (Fin n)) = Set.range A.col := by
    ext v
    simp
  rw [hrange, ← Matrix.rank_eq_finrank_span_cols, hrow.rank_matrix] at h
  simpa [M] using h

private theorem vectorMatroid_indep_ordered_iff
    {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (s : {S : Finset (Fin n) // S.card = k}) :
    (vectorMatroid (K := ℝ) (Set.univ : Set (Fin n)) Set.finite_univ A.col).Indep
        (s.1 : Set (Fin n)) ↔
      LinearIndependent ℝ (A.col ∘ Matrix.orderedColumnIndex s) := by
  let e : Fin k ≃ (s.1 : Set (Fin n)) := (s.1.orderIsoOfFin s.2).toEquiv
  have hcomp : (fun x : (s.1 : Set (Fin n)) => A.col x.1) ∘ e =
      A.col ∘ Matrix.orderedColumnIndex s := rfl
  have hLI := (linearIndependent_equiv' (R := ℝ) e hcomp).symm
  rw [vectorMatroid_indep_iff]
  simpa using hLI

private theorem vectorMatroid_isBase_ordered_iff_det_ne_zero
    {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (hrow : LinearIndependent ℝ A.row)
    (s : {S : Finset (Fin n) // S.card = k}) :
    (vectorMatroid (K := ℝ) (Set.univ : Set (Fin n)) Set.finite_univ A.col).IsBase
        (s.1 : Set (Fin n)) ↔
      (A.submatrix id (Matrix.orderedColumnIndex s)).det ≠ 0 := by
  let M := vectorMatroid (K := ℝ) (Set.univ : Set (Fin n)) Set.finite_univ A.col
  let B := A.submatrix id (Matrix.orderedColumnIndex s)
  have hLI : M.Indep (s.1 : Set (Fin n)) ↔
      LinearIndependent ℝ B.col := by
    change M.Indep (s.1 : Set (Fin n)) ↔
      LinearIndependent ℝ (A.col ∘ Matrix.orderedColumnIndex s)
    exact vectorMatroid_indep_ordered_iff A s
  have hdet : LinearIndependent ℝ B.col ↔ B.det ≠ 0 := by
    rw [Matrix.linearIndependent_cols_iff_isUnit,
      Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  constructor
  · intro hBase
    exact hdet.mp (hLI.mp hBase.indep)
  · intro hMinor
    have hIndep : M.Indep (s.1 : Set (Fin n)) := hLI.mpr (hdet.mpr hMinor)
    apply hIndep.isBase_of_eRk_ge (by simp)
    rw [vectorMatroid_eRank_eq_rowCount A hrow, hIndep.eRk_eq_encard]
    simp [s.2]

private theorem tu_minor_sq_weight_eq_basisIndicator
    {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (hTU : A.IsTotallyUnimodular)
    (hrow : LinearIndependent ℝ A.row)
    (w : Fin n → ℝ)
    (s : {S : Finset (Fin n) // S.card = k}) :
    (A.submatrix id (Matrix.orderedColumnIndex s)).det ^ 2 *
        ∏ j ∈ s.1, w j =
      if (vectorMatroid (K := ℝ) (Set.univ : Set (Fin n)) Set.finite_univ A.col).IsBase
          (s.1 : Set (Fin n)) then ∏ j ∈ s.1, w j else 0 := by
  classical
  by_cases hBase : (vectorMatroid (K := ℝ) (Set.univ : Set (Fin n))
      Set.finite_univ A.col).IsBase (s.1 : Set (Fin n))
  · have hdet := (vectorMatroid_isBase_ordered_iff_det_ne_zero A hrow s).mp hBase
    rw [hTU.det_submatrix_sq_of_ne_zero k id (Matrix.orderedColumnIndex s) hdet]
    simp [hBase]
  · have hdet : (A.submatrix id (Matrix.orderedColumnIndex s)).det = 0 :=
      not_ne_iff.mp ((vectorMatroid_isBase_ordered_iff_det_ne_zero A hrow s).not.mp hBase)
    simp [hdet, hBase]

/-- N125: for a full-row-rank real TU matrix, the weighted Gram determinant
is the target-free weighted basis sum of its indexed column matroid. This
derivation uses only the narrow rectangular Cauchy--Binet premise. -/
theorem weightedGram_det_eq_weightedBasesTotal_of_tu
    {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (hTU : A.IsTotallyUnimodular)
    (hrow : LinearIndependent ℝ A.row) (w : Fin n → ℝ) :
    (A * Matrix.diagonal w * A.transpose).det =
      weightedBasesTotal
        (vectorMatroid (K := ℝ) (Set.univ : Set (Fin n)) Set.finite_univ A.col)
        Set.finite_univ w := by
  classical
  let M := vectorMatroid (K := ℝ) (Set.univ : Set (Fin n)) Set.finite_univ A.col
  let f : Finset (Fin n) → ℝ := fun B =>
    if M.IsBase (B : Set (Fin n)) then ∏ j ∈ B, w j else 0
  have hcard (B : Finset (Fin n)) (hB : M.IsBase (B : Set (Fin n))) :
      B.card = k := by
    have h := hB.encard_eq_eRank
    rw [vectorMatroid_eRank_eq_rowCount A hrow] at h
    simpa [M] using h
  rw [Matrix.weightedCauchyBinet_real A w]
  simp_rw [tu_minor_sq_weight_eq_basisIndicator A hTU hrow w]
  change (∑ s : {S : Finset (Fin n) // S.card = k}, f s.1) = _
  have hpow : (Finset.univ : Finset (Fin n)).powerset = Finset.univ := by
    ext B
    simp
  have hsub :
      (∑ s : {S : Finset (Fin n) // S.card = k}, f s.1) =
        ∑ B ∈ (Finset.univ : Finset (Finset (Fin n))).filter
          (fun B => B.card = k), f B := by
    symm
    apply Finset.sum_subtype
    intro B
    simp
  rw [hsub]
  unfold weightedBasesTotal
  simp only [vectorMatroid_ground, Set.Finite.toFinset_univ]
  change (∑ B ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun B => B.card = k), f B) =
    (∑ B ∈ (Finset.univ : Finset (Fin n)).powerset, f B)
  rw [hpow, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro B _
  by_cases hB : M.IsBase (B : Set (Fin n))
  · simp [f, hB, hcard B hB]
  · simp [f, hB]

end Matroid
