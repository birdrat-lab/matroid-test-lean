import Matroid.R10Automorphism
import Matroid.WeightedBases

/-! The manuscript's pointed basis-polynomial equivariance under a labeled
R10 automorphism. -/

namespace Matroid

attribute [local instance] Classical.propDecidable Classical.decEq

private theorem erase_decidable_eq (B : Finset (Fin 10)) (e : Fin 10) :
    B.erase e = @Finset.erase (Fin 10) (Classical.decEq _) B e := by
  ext x
  simp

private theorem r10_base_image_iff (σ : Equiv.Perm (Fin 10))
    (hσ : IsR10Automorphism σ) (B : Finset (Fin 10)) :
    r10.IsBase ((B.image σ : Finset (Fin 10)) : Set (Fin 10)) ↔
      r10.IsBase (B : Set (Fin 10)) := by
  have h := (mapEquiv_isBase_iff (M := r10) (f := σ)
    (B := (B.image σ : Set (Fin 10))))
  rw [hσ] at h
  simpa [Finset.coe_image] using h

private theorem prod_erase_image (σ : Equiv.Perm (Fin 10))
    (B : Finset (Fin 10)) (e : Fin 10) {R : Type*} [CommMonoid R]
    (w : Fin 10 → R) :
    (∏ x ∈ (B.image σ).erase (σ e), w (σ.symm x)) =
      ∏ x ∈ B.erase e, w x := by
  rw [← Finset.image_erase σ.injective B e]
  rw [Finset.prod_image σ.injective.injOn]
  apply Finset.prod_congr rfl
  intro x _
  simp

private theorem r10_pointed_sum_equiv (σ : Equiv.Perm (Fin 10))
    (hσ : IsR10Automorphism σ) (e : Fin 10)
    {R : Type*} [CommSemiring R] (w : Fin 10 → R) (b : Bool) :
    (∑ B : Finset (Fin 10),
      if r10.IsBase (B : Set (Fin 10)) ∧
          (if b then σ e ∈ B else σ e ∉ B) then
        ∏ x ∈ B.erase (σ e), w (σ.symm x) else 0) =
    ∑ B : Finset (Fin 10),
      if r10.IsBase (B : Set (Fin 10)) ∧
          (if b then e ∈ B else e ∉ B) then
        ∏ x ∈ B.erase e, w x else 0 := by
  classical
  refine (Fintype.sum_equiv (Equiv.finsetCongr σ) _ _ ?_).symm
  intro B
  simp only [Equiv.finsetCongr_apply, Finset.map_eq_image]
  have hmem : σ e ∈ B.image σ ↔ e ∈ B := by simp
  have hbase : r10.IsBase (σ '' (B : Set (Fin 10))) ↔
      r10.IsBase (B : Set (Fin 10)) := by
    simpa only [Finset.coe_image] using r10_base_image_iff σ hσ B
  simp [hbase, hmem, prod_erase_image σ B e w]

/-- N188, `eq:r10-P01-equivariance`: both pointed basis polynomials are
carried exactly by every automorphism of the ten labeled R10 elements. -/
theorem r10_pointed_basis_polynomials_equivariant
    (σ : Equiv.Perm (Fin 10)) (hσ : IsR10Automorphism σ)
    (e : Fin 10) {R : Type*} [CommSemiring R] (w : Fin 10 → R) :
    weightedBasesOut r10 r10.ground_finite (σ e) (w ∘ σ.symm) =
        weightedBasesOut r10 r10.ground_finite e w ∧
      weightedBasesIn r10 r10.ground_finite (σ e) (w ∘ σ.symm) =
        weightedBasesIn r10 r10.ground_finite e w := by
  constructor
  · have hground : r10.ground_finite.toFinset = (Finset.univ : Finset (Fin 10)) := by
      ext x
      simp [r10_ground]
    have hpow : (Finset.univ : Finset (Fin 10)).powerset = Finset.univ := by
      ext B
      simp
    have h := r10_pointed_sum_equiv σ hσ e w false
    simp only [erase_decidable_eq] at h
    simp only [weightedBasesOut, hground, hpow]
    convert h using 1
    all_goals simp
    all_goals
      apply Finset.sum_congr rfl
      intro B _
      by_cases hb : r10.IsBase (B : Set (Fin 10)) ∧ e ∉ B <;> simp [hb]
  · have hground : r10.ground_finite.toFinset = (Finset.univ : Finset (Fin 10)) := by
      ext x
      simp [r10_ground]
    have hpow : (Finset.univ : Finset (Fin 10)).powerset = Finset.univ := by
      ext B
      simp
    have h := r10_pointed_sum_equiv σ hσ e w true
    simp only [erase_decidable_eq] at h
    simp only [weightedBasesIn, hground, hpow]
    convert h using 1
    all_goals simp
    all_goals
      apply Finset.sum_congr rfl
      intro B _
      by_cases hb : r10.IsBase (B : Set (Fin 10)) ∧ e ∈ B <;> simp [hb]

end Matroid
