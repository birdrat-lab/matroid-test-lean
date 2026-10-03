import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Matroid.Representation

/-! # Totally unimodular matrix operations used by quotient constructions -/

namespace Matrix

private theorem signRange_of_mul_sign {K : Type*} [Field K] {a b : K}
    (ha : a ∈ Set.range (SignType.cast : SignType → K))
    (hunit : IsUnit a)
    (hab : a * b ∈ Set.range (SignType.cast : SignType → K)) :
    b ∈ Set.range (SignType.cast : SignType → K) := by
  rcases ha with ⟨s, hs⟩
  have hs2 : (s : K) * (s : K) = 1 := by
    have hsn : s ≠ 0 := by
      intro hz
      subst s
      exact hunit.ne_zero (by simpa using hs.symm)
    cases s with
    | zero => exact (hsn rfl).elim
    | pos => simp
    | neg => simp
  rcases hab with ⟨t, ht⟩
  refine ⟨s * t, ?_⟩
  calc
    ((s * t : SignType) : K) = (s : K) * (t : K) := by simp
    _ = (s : K) * (a * b) := by rw [← ht]
    _ = ((s : K) * (s : K)) * b := by rw [← hs, mul_assoc]
    _ = b := by rw [hs2, one_mul]

/-- Manuscript ledger N056; column and row relabeling preserve total
unimodularity in the standard-form step of `thm:regular-quotient-form`. -/
theorem isTotallyUnimodular_reindex_iff {m m' n n' R : Type*} [CommRing R]
    (A : Matrix m n R) (em : m ≃ m') (en : n ≃ n') :
    (A.reindex em en).IsTotallyUnimodular ↔ A.IsTotallyUnimodular :=
  Matrix.reindex_isTotallyUnimodular A em en

/-- Manuscript `thm:regular-quotient-form` (N056): once a chosen square
basis block is nonsingular, multiplying by its inverse puts those columns
into the identity block. TU preservation of the other block is separate. -/
theorem basisNormalize_eq_fromCols {r c K : Type*} [Field K]
    [Fintype r] [DecidableEq r] (A : Matrix r (r ⊕ c) K)
    (hB : IsUnit (A.submatrix id Sum.inl).det) :
    (A.submatrix id Sum.inl)⁻¹ * A =
      Matrix.fromCols (1 : Matrix r r K)
        ((A.submatrix id Sum.inl)⁻¹ * A.submatrix id Sum.inr) := by
  have hdecomp : A = Matrix.fromCols
      (A.submatrix id Sum.inl) (A.submatrix id Sum.inr) := by
    ext i j
    cases j <;> rfl
  calc
    (A.submatrix id Sum.inl)⁻¹ * A =
        (A.submatrix id Sum.inl)⁻¹ *
          Matrix.fromCols (A.submatrix id Sum.inl) (A.submatrix id Sum.inr) :=
            congrArg (fun X => (A.submatrix id Sum.inl)⁻¹ * X) hdecomp
    _ = Matrix.fromCols
          ((A.submatrix id Sum.inl)⁻¹ * A.submatrix id Sum.inl)
          ((A.submatrix id Sum.inl)⁻¹ * A.submatrix id Sum.inr) :=
        Matrix.mul_fromCols ..
    _ = _ := by rw [Matrix.nonsing_inv_mul (A.submatrix id Sum.inl) hB]

/-- The invertible row operation used in N056 preserves the indexed column
matroid, including repeated and zero columns. -/
theorem basisNormalize_vectorMatroid_eq {r n K : Type*} [Field K]
    [Fintype r] [DecidableEq r] (B : Matrix r r K) (hB : IsUnit B.det)
    (A : Matrix r n K) (E : Set n) (hE : E.Finite) :
    Matroid.vectorMatroid (K := K) E hE (B⁻¹ * A).col =
      Matroid.vectorMatroid (K := K) E hE A.col := by
  let T : (r → K) ≃ₗ[K] (r → K) :=
    (B⁻¹).toLinearEquiv (Pi.basisFun K r) (B.isUnit_nonsing_inv_det hB)
  have hcols : (B⁻¹ * A).col = T ∘ A.col := by
    funext j
    simp [T, Matrix.toLin_eq_toLin', Matrix.col_mul_eq_mulVec_col]
  rw [hcols]
  exact Matroid.vectorMatroid_map_linearEquiv_eq E hE A.col T

/-- The N056 TU obligation reduces exactly to the nonbasis block after
basis normalization. The remaining implication from TU of `A` to TU of
this block requires the pivot-minor determinant identity. -/
theorem basisNormalize_isTotallyUnimodular_iff {r c K : Type*} [Field K]
    [Fintype r] [DecidableEq r] (A : Matrix r (r ⊕ c) K)
    (hB : IsUnit (A.submatrix id Sum.inl).det) :
    ((A.submatrix id Sum.inl)⁻¹ * A).IsTotallyUnimodular ↔
      ((A.submatrix id Sum.inl)⁻¹ * A.submatrix id Sum.inr).IsTotallyUnimodular := by
  rw [basisNormalize_eq_fromCols A hB,
    Matrix.one_fromCols_isTotallyUnimodular_iff]

/-- The one-column Cramer minor in N056: each entry of the normalized
nonbasis block is a signed maximal minor of the original TU matrix. -/
theorem IsTotallyUnimodular.basisNormalize_entry {r c K : Type*} [Field K]
    [Fintype r] [DecidableEq r] (A : Matrix r (r ⊕ c) K)
    (hA : A.IsTotallyUnimodular)
    (hB : IsUnit (A.submatrix id Sum.inl).det) (i : r) (j : c) :
    ((A.submatrix id Sum.inl)⁻¹ * A.submatrix id Sum.inr) i j ∈
      Set.range (SignType.cast : SignType → K) := by
  let B : Matrix r r K := A.submatrix id Sum.inl
  let C : Matrix r c K := A.submatrix id Sum.inr
  have hdetB : B.det ∈ Set.range (SignType.cast : SignType → K) :=
    (Matrix.isTotallyUnimodular_iff_fintype A).1 hA r id Sum.inl
  have hdetR : (B.updateCol i (C.col j)).det ∈
      Set.range (SignType.cast : SignType → K) := by
    have hrep : B.updateCol i (C.col j) =
        A.submatrix id (fun k => if k = i then Sum.inr j else Sum.inl k) := by
      ext p q
      by_cases hqi : q = i <;>
        simp [B, C, Matrix.submatrix_apply, hqi]
    rw [hrep]
    exact (Matrix.isTotallyUnimodular_iff_fintype A).1 hA r id _
  have hcramer : B.det * (B⁻¹ * C) i j = (B.updateCol i (C.col j)).det := by
    have h := congrFun (B.det_smul_inv_mulVec_eq_cramer (C.col j) hB) i
    simpa only [Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply,
      ← Matrix.col_mul_eq_mulVec_col, Matrix.col_apply] using h
  have hab : B.det * (B⁻¹ * C) i j ∈
      Set.range (SignType.cast : SignType → K) := by
    rw [hcramer]
    exact hdetR
  exact signRange_of_mul_sign hdetB hB hab

/-- A rowwise sign reversal preserves total unimodularity. This supplies
the `-D` block in manuscript `thm:regular-quotient-form` (N057). -/
theorem IsTotallyUnimodular.neg {m n R : Type*} [CommRing R]
    {A : Matrix m n R} (hA : A.IsTotallyUnimodular) :
    (-A).IsTotallyUnimodular := by
  rw [Matrix.isTotallyUnimodular_iff] at hA ⊢
  intro k f g
  obtain ⟨s, hs⟩ := hA k f g
  refine ⟨(-1 : SignType) ^ k * s, ?_⟩
  change _ = (-(A.submatrix f g)).det
  rw [Matrix.det_neg, ← hs]
  simp [SignType.coe_mul, SignType.coe_pow]

/-- Basis normalization preserves total unimodularity. The block determinant
argument adds unit rows to a submatrix of the original TU representation,
then takes its Schur complement; it does not require indexing complementary
minors. This is the remaining TU step of manuscript `thm:regular-quotient-form`
(N056). -/
theorem IsTotallyUnimodular.basisNormalize_nonbasis {r c K : Type*} [Field K]
    [Fintype r] [DecidableEq r] (A : Matrix r (r ⊕ c) K)
    (hA : A.IsTotallyUnimodular)
    (hB : IsUnit (A.submatrix id Sum.inl).det) :
    ((A.submatrix id Sum.inl)⁻¹ * A.submatrix id Sum.inr).IsTotallyUnimodular := by
  classical
  let B : Matrix r r K := A.submatrix id Sum.inl
  let C : Matrix r c K := A.submatrix id Sum.inr
  have hdetB : B.det ∈ Set.range (SignType.cast : SignType → K) :=
    (Matrix.isTotallyUnimodular_iff_fintype A).1 hA r id Sum.inl
  have hneg : (-(B⁻¹ * C)).IsTotallyUnimodular := by
    rw [Matrix.isTotallyUnimodular_iff]
    intro k f g
    let Cg : Matrix r (Fin k) K := C.submatrix id g
    let F : Matrix (Fin k) r K := (1 : Matrix r r K).submatrix f id
    have htop : (Matrix.fromCols B Cg).IsTotallyUnimodular := by
      have heq : Matrix.fromCols B Cg =
          A.submatrix id (Sum.elim Sum.inl (Sum.inr ∘ g)) := by
        ext i j
        cases j <;> rfl
      rw [heq]
      exact hA.submatrix _ _
    have hbottom : Nonempty (r ⊕ Fin k) → ∀ p : Fin k,
        ∃ q : r ⊕ Fin k, ∃ s : SignType,
          (Matrix.fromCols F (0 : Matrix (Fin k) (Fin k) K)) p =
            Pi.single q (s : K) := by
      intro _ p
      refine ⟨Sum.inl (f p), 1, ?_⟩
      funext q
      cases q with
      | inl i => simp [F, Matrix.submatrix_apply, Matrix.one_apply, Pi.single_apply,
          eq_comm]
      | inr j => simp
    have hblockTU : (Matrix.fromBlocks B Cg F 0).IsTotallyUnimodular := by
      rw [← Matrix.fromRows_fromCols_eq_fromBlocks]
      exact htop.fromRows_unitlike hbottom
    have hblockdet : (Matrix.fromBlocks B Cg F 0).det ∈
        Set.range (SignType.cast : SignType → K) :=
      (Matrix.isTotallyUnimodular_iff_fintype _).1 hblockTU (r ⊕ Fin k) id id
    have : Invertible B :=
      ((B.isUnit_iff_isUnit_det).2 hB).nonempty_invertible.some
    have hproduct : F * B⁻¹ * Cg = (B⁻¹ * C).submatrix f g := by
      calc
        F * B⁻¹ * Cg = F * (B⁻¹ * Cg) := Matrix.mul_assoc ..
        _ = (B⁻¹ * Cg).submatrix f id := by
          simpa [F] using
            (Matrix.one_submatrix_mul f (Equiv.refl r) (B⁻¹ * Cg))
        _ = (B⁻¹ * C).submatrix f g := by rfl
    have hschur : (Matrix.fromBlocks B Cg F 0).det =
        B.det * (-(B⁻¹ * C).submatrix f g).det := by
      rw [Matrix.det_fromBlocks₁₁]
      rw [Matrix.invOf_eq_nonsing_inv B, ← hproduct]
      simp
    have hsign : (-(B⁻¹ * C).submatrix f g).det ∈
        Set.range (SignType.cast : SignType → K) := by
      apply signRange_of_mul_sign hdetB hB
      rw [← hschur]
      exact hblockdet
    change (-(B⁻¹ * C).submatrix f g).det ∈
      Set.range (SignType.cast : SignType → K)
    exact hsign
  simpa only [neg_neg] using hneg.neg

/-- The full N056 standard-form implication: a TU matrix with a nonsingular
basis block normalizes to another TU matrix. -/
theorem IsTotallyUnimodular.basisNormalize {r c K : Type*} [Field K]
    [Fintype r] [DecidableEq r] (A : Matrix r (r ⊕ c) K)
    (hA : A.IsTotallyUnimodular)
    (hB : IsUnit (A.submatrix id Sum.inl).det) :
    ((A.submatrix id Sum.inl)⁻¹ * A).IsTotallyUnimodular :=
  (basisNormalize_isTotallyUnimodular_iff A hB).2
    (hA.basisNormalize_nonbasis A hB)

/-- Manuscript N056 in standard-form language. Choosing linearly independent
basis columns of a TU matrix yields `[I D]` with `D` TU and preserves the
indexed column matroid. Column relabeling is covered separately by
`isTotallyUnimodular_reindex_iff`. -/
theorem IsTotallyUnimodular.basisStandardForm {r c K : Type*} [Field K]
    [Fintype r] [DecidableEq r] (A : Matrix r (r ⊕ c) K)
    (hA : A.IsTotallyUnimodular)
    (hLI : LinearIndependent K (A.submatrix id Sum.inl).col)
    (E : Set (r ⊕ c)) (hE : E.Finite) :
    ∃ D : Matrix r c K,
      (A.submatrix id Sum.inl)⁻¹ * A = Matrix.fromCols 1 D ∧
      D.IsTotallyUnimodular ∧
      Matroid.vectorMatroid (K := K) E hE
        ((A.submatrix id Sum.inl)⁻¹ * A).col =
        Matroid.vectorMatroid (K := K) E hE A.col := by
  let B : Matrix r r K := A.submatrix id Sum.inl
  let D : Matrix r c K := B⁻¹ * A.submatrix id Sum.inr
  have hB : IsUnit B.det :=
    (B.isUnit_iff_isUnit_det).1
      (Matrix.linearIndependent_cols_iff_isUnit.1 hLI)
  refine ⟨D, ?_, ?_, ?_⟩
  · exact basisNormalize_eq_fromCols A hB
  · exact hA.basisNormalize_nonbasis A hB
  · exact basisNormalize_vectorMatroid_eq B hB A E hE

/-- Manuscript `thm:regular-quotient-form` (N057): the concrete kernel
block `K = (-D; I)` is totally unimodular when `D` is. -/
theorem IsTotallyUnimodular.kernelBlock {r c R : Type*} [CommRing R]
    [DecidableEq c] {D : Matrix r c R} (hD : D.IsTotallyUnimodular) :
    (Matrix.fromRows (-D) (1 : Matrix c c R)).IsTotallyUnimodular :=
  (Matrix.fromRows_one_isTotallyUnimodular_iff (-D)).2 hD.neg

/-- Manuscript `thm:regular-quotient-form` (N057): after building `K`,
the concrete augmented matrix `Â = (I K)` is totally unimodular. -/
theorem IsTotallyUnimodular.augmentedKernelBlock {r c R : Type*} [CommRing R]
    [DecidableEq c] [DecidableEq (r ⊕ c)]
    {D : Matrix r c R} (hD : D.IsTotallyUnimodular) :
    (Matrix.fromCols (1 : Matrix (r ⊕ c) (r ⊕ c) R)
      (Matrix.fromRows (-D) (1 : Matrix c c R))).IsTotallyUnimodular :=
  (Matrix.one_fromCols_isTotallyUnimodular_iff _).2 hD.kernelBlock

end Matrix
