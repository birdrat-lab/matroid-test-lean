import Matroid.External.ProjectiveUniqueness

/-! N055: every real representation of a finite regular matroid is
projectively equivalent to a fixed labeled TU representation. -/

namespace Matroid

universe u v w

/-- All real representations of a finite regular matroid are projectively
equivalent. The local specialization obtains binary representability from
regularity; the uniqueness assertion is the cited external premise. -/
theorem Regular.real_representations_projectivelyEquivalent
    {α : Type u} {V : Type v} {W : Type w}
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    {M : Matroid α} [M.Finite] (hM : Regular.{u, 0, 0} M)
    {φ : α → V} {ψ : α → W}
    (hφ : M.Represents (K := ℝ) φ)
    (hψ : M.Represents (K := ℝ) ψ) :
    M.ProjectivelyEquivalent (K := ℝ) φ ψ :=
  External.binary_real_projective_uniqueness (hM (ZMod 2)) hφ hψ

/-- The fixed matrix is totally unimodular on the original ground labels.
Its existence is relative to the separately cited N052 Tutte converse;
projective uniqueness is relative to the N055 cited premise. -/
theorem Regular.exists_tu_projectivelyEquivalent
    {α : Type u} {V : Type v}
    [AddCommGroup V] [Module ℝ V]
    {M : Matroid α} [M.Finite] (hM : Regular.{u, 0, 0} M)
    {φ : α → V} (hφ : M.Represents (K := ℝ) φ) :
    ∃ (r : Type) (_ : Fintype r) (A : Matrix r α ℝ),
      A.IsTotallyUnimodular ∧
      M = vectorMatroid (K := ℝ) M.E M.ground_finite A.col ∧
      M.ProjectivelyEquivalent (K := ℝ) A.col φ := by
  obtain ⟨r, hr, A, hTU, hEq⟩ := hM.hasLabeledRealTU
  letI : Fintype r := hr
  have hA : M.Represents (K := ℝ) A.col := by
    rw [hEq]
    exact vectorMatroid_represents M.E M.ground_finite A.col
  exact ⟨r, hr, A, hTU, hEq,
    hM.real_representations_projectivelyEquivalent hA hφ⟩

end Matroid
