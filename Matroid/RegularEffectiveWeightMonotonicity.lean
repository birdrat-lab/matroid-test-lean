import Matroid.RayleighRatioAlgebra

namespace Matroid

open scoped NNReal
attribute [local instance] Classical.decEq Classical.propDecidable

private theorem pairClass_in_update {α : Type*}
    (M : Matroid α) (hE : M.E.Finite) (p e : α)
    (hne : p ≠ e) (w : α → ℝ≥0) (x : ℝ≥0) :
    weightedBasesIn M hE p (Function.update w e x) =
      weightedPairClass M hE p e true false w +
        x * weightedPairClass M hE p e true true w := by
  unfold weightedBasesIn weightedPairClass
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro B hB
  by_cases hb : M.IsBase (B : Set α)
  · by_cases hp : p ∈ B
    · by_cases he : e ∈ B
      · simp only [hb, hp, he, and_self, ↓reduceIte, if_true, if_false,
          mul_zero, zero_add, add_zero]
        have he' : e ∈ B.erase p := Finset.mem_erase.mpr ⟨Ne.symm hne, he⟩
        simp [Finset.prod_update_of_mem he', Finset.sdiff_singleton_eq_erase]
      · simp only [hb, hp, he, and_self, ↓reduceIte, if_true, if_false,
          mul_zero, zero_add, add_zero]
        have he' : e ∉ B.erase p := by simp [he]
        simp [Finset.prod_update_of_notMem he', Finset.erase_eq_self.mpr he']
    · simp [weightedBasesIn, weightedPairClass, hb, hp]
  · simp [weightedBasesIn, weightedPairClass, hb]

private theorem pairClass_out_update {α : Type*}
    (M : Matroid α) (hE : M.E.Finite) (p e : α)
    (hne : p ≠ e) (w : α → ℝ≥0) (x : ℝ≥0) :
    weightedBasesOut M hE p (Function.update w e x) =
      weightedPairClass M hE p e false false w +
        x * weightedPairClass M hE p e false true w := by
  unfold weightedBasesOut weightedPairClass
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro B hB
  by_cases hb : M.IsBase (B : Set α)
  · by_cases hp : p ∈ B
    · simp [hb, hp]
    · by_cases he : e ∈ B
      · simp only [hb, hp, he, and_self, ↓reduceIte,
          mul_zero, zero_add, add_zero]
        have he' : e ∈ B.erase p := Finset.mem_erase.mpr ⟨Ne.symm hne, he⟩
        simp [Finset.prod_update_of_mem he', Finset.sdiff_singleton_eq_erase]
      · simp only [hb, hp, he, and_self, ↓reduceIte,
          mul_zero, zero_add, add_zero]
        have he' : e ∉ B.erase p := by simp [he]
        simp [Finset.prod_update_of_notMem he', Finset.erase_eq_self.mpr he']
  · simp [hb]

universe u w

/-- N154: increasing one finite non-target weight increases the pointed
effective ratio. The local proof uses the exact regular Rayleigh
difference premise and the checked four-class expansion. -/
theorem regularEffectiveWeight_update_mono {α : Type u}
    (M : Matroid α) [M.Finite] (hM : Regular.{u, 0, w} M)
    (p e : α) (hpE : p ∈ M.E) (heE : e ∈ M.E)
    (hne : p ≠ e) (weights : α → ℝ≥0)
    (x y : ℝ≥0) (hxy : x ≤ y)
    (hx : 0 < weightedBasesIn M M.ground_finite p
      (Function.update weights e x))
    (hy : 0 < weightedBasesIn M M.ground_finite p
      (Function.update weights e y)) :
    twoSumEffectiveWeight M M.ground_finite p
        (Function.update weights e x) ≤
      twoSumEffectiveWeight M M.ground_finite p
        (Function.update weights e y) := by
  let a := weightedPairClass M M.ground_finite p e false false weights
  let b := weightedPairClass M M.ground_finite p e false true weights
  let c := weightedPairClass M M.ground_finite p e true false weights
  let d := weightedPairClass M M.ground_finite p e true true weights
  have hray : d * a ≤ c * b :=
    External.regular_rayleigh_pair M hM p e hpE heE hne weights
  have hx' : 0 < c + x * d := by
    rw [← pairClass_in_update M M.ground_finite p e hne weights x]
    exact hx
  have hy' : 0 < c + y * d := by
    rw [← pairClass_in_update M M.ground_finite p e hne weights y]
    exact hy
  have hmono := rayleigh_affine_ratio_mono a b c d x y hray hxy hx' hy'
  change weightedBasesOut M M.ground_finite p (Function.update weights e x) /
      weightedBasesIn M M.ground_finite p (Function.update weights e x) ≤
    weightedBasesOut M M.ground_finite p (Function.update weights e y) /
      weightedBasesIn M M.ground_finite p (Function.update weights e y)
  rw [pairClass_out_update M M.ground_finite p e hne weights x,
    pairClass_in_update M M.ground_finite p e hne weights x,
    pairClass_out_update M M.ground_finite p e hne weights y,
    pairClass_in_update M M.ground_finite p e hne weights y]
  exact hmono

/-- Manuscript-facing positive-weight form for finite regular pointed
minors: a nonloop target and strictly positive non-target weights make the
effective ratio finite throughout the increase. -/
theorem regularEffectiveWeight_mono_of_positive {α : Type u}
    (M : Matroid α) [M.Finite] (hM : Regular.{u, 0, w} M)
    (p e : α) (hpE : p ∈ M.E) (heE : e ∈ M.E)
    (hp : ¬ M.IsLoop p)
    (hne : p ≠ e) (weights : α → ℝ≥0)
    (x y : ℝ≥0) (hx0 : 0 < x) (hxy : x ≤ y)
    (hw : ∀ z ∈ M.E, z ≠ p → z ≠ e → 0 < weights z) :
    twoSumEffectiveWeight M M.ground_finite p
        (Function.update weights e x) ≤
      twoSumEffectiveWeight M M.ground_finite p
        (Function.update weights e y) := by
  have hpos (t : ℝ≥0) (ht : 0 < t) :
      ∀ z ∈ M.E, z ≠ p → 0 < Function.update weights e t z := by
    intro z hz hzp
    by_cases hze : z = e
    · subst z
      simpa using ht
    · simpa [Function.update, hze] using hw z hz hzp hze
  have hx := weightedBasesIn_pos_of_not_isLoop M M.ground_finite p hpE hp
    (Function.update weights e x) (hpos x hx0)
  have hy := weightedBasesIn_pos_of_not_isLoop M M.ground_finite p hpE hp
    (Function.update weights e y) (hpos y (lt_of_lt_of_le hx0 hxy))
  exact regularEffectiveWeight_update_mono M hM p e hpE heE hne
    weights x y hxy hx hy

end Matroid
