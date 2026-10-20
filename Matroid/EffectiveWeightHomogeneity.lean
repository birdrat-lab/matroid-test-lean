import Matroid.TwoSumWeights

/-! Homogeneity of the two pointed basis sums and effective port weight. -/

namespace Matroid

open scoped NNReal

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Scale exactly the non-port weights, leaving the irrelevant port weight fixed. -/
noncomputable def scaleNonPortWeight {α : Type*} (p : α) (c : ℝ≥0)
    (w : α → ℝ≥0) (e : α) : ℝ≥0 :=
  if e = p then w e else c * w e

private theorem prod_scaleNonPortWeight {α : Type*} (p : α) (c : ℝ≥0)
    (w : α → ℝ≥0) (B : Finset α) :
    (∏ e ∈ B.erase p, scaleNonPortWeight p c w e) =
      c ^ (B.erase p).card * ∏ e ∈ B.erase p, w e := by
  classical
  simp only [scaleNonPortWeight]
  have h : ∀ e ∈ B.erase p, (if e = p then w e else c * w e) = c * w e := by
    intro e he
    simp [Finset.ne_of_mem_erase he]
  simp_rw [Finset.prod_congr rfl h]
  rw [Finset.prod_mul_distrib]
  simp

/-- Every target-containing basis term has degree one below the common
basis cardinality. The witness is a target-containing base, available for
the proper nonloop port in the manuscript. -/
private theorem basis_erase_card {α : Type*} (M : Matroid α)
    (p : α) (B₁ B : Finset α)
    (hB₁ : M.IsBase (B₁ : Set α)) (hp₁ : p ∈ B₁)
    (hB : M.IsBase (B : Set α)) :
    (B.erase p).card = (B₁.erase p).card + (if p ∈ B then 0 else 1) := by
  have hcard : B.card = B₁.card := by
    simpa using hB.ncard_eq_ncard_of_isBase hB₁
  by_cases hp : p ∈ B
  · simp only [hp, ↓reduceIte]
    have h₁ := Finset.card_erase_add_one hp
    have h₂ := Finset.card_erase_add_one hp₁
    omega
  · simp only [hp, ↓reduceIte, Finset.erase_eq_self.mpr hp]
    have h₂ := Finset.card_erase_add_one hp₁
    omega

/-- The target-containing sum has degree `r-1`, including the zero sum. -/
theorem weightedBasesIn_scaleNonPortWeight {α : Type*}
    (M : Matroid α) (hE : M.E.Finite) (p : α)
    (B₁ : Finset α) (hB₁ : M.IsBase (B₁ : Set α)) (hp₁ : p ∈ B₁)
    (c : ℝ≥0) (w : α → ℝ≥0) :
    weightedBasesIn M hE p (scaleNonPortWeight p c w) =
      c ^ (B₁.erase p).card * weightedBasesIn M hE p w := by
  classical
  unfold weightedBasesIn
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  by_cases h : M.IsBase (B : Set α) ∧ p ∈ B
  · simp only [h]
    rw [prod_scaleNonPortWeight,
      show (B.erase p).card = (B₁.erase p).card by
        simpa [h.2] using basis_erase_card M p B₁ B hB₁ hp₁ h.1]
    simp
  · simp [h]

/-- The target-omitting sum has degree `r`, including the zero sum. -/
theorem weightedBasesOut_scaleNonPortWeight {α : Type*}
    (M : Matroid α) (hE : M.E.Finite) (p : α)
    (B₁ : Finset α) (hB₁ : M.IsBase (B₁ : Set α)) (hp₁ : p ∈ B₁)
    (c : ℝ≥0) (w : α → ℝ≥0) :
    weightedBasesOut M hE p (scaleNonPortWeight p c w) =
      c ^ ((B₁.erase p).card + 1) * weightedBasesOut M hE p w := by
  classical
  unfold weightedBasesOut
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  by_cases h : M.IsBase (B : Set α) ∧ p ∉ B
  · simp only [h]
    rw [prod_scaleNonPortWeight,
      show (B.erase p).card = (B₁.erase p).card + 1 by
        simpa [h.2] using basis_erase_card M p B₁ B hB₁ hp₁ h.1]
    simp [h]
  · simp [h]

/-- Manuscript `eq:two-sum-homogeneity` (N153): scaling all non-port
weights by a positive factor scales the effective `P₀/P₁` weight by that
factor. The nonloop witness follows from the proper-port hypotheses. -/
theorem twoSumEffectiveWeight_scaleNonPortWeight {α : Type*}
    (M : Matroid α) (hE : M.E.Finite) (p : α)
    (B₁ : Finset α) (hB₁ : M.IsBase (B₁ : Set α)) (hp₁ : p ∈ B₁)
    (c : ℝ≥0) (hc : 0 < c) (w : α → ℝ≥0) :
    twoSumEffectiveWeight M hE p (scaleNonPortWeight p c w) =
      c * twoSumEffectiveWeight M hE p w := by
  rw [twoSumEffectiveWeight, twoSumEffectiveWeight,
    weightedBasesOut_scaleNonPortWeight M hE p B₁ hB₁ hp₁,
    weightedBasesIn_scaleNonPortWeight M hE p B₁ hB₁ hp₁]
  rw [pow_succ, mul_assoc]
  rw [mul_div_mul_left _ _ (pow_pos hc _).ne']
  rw [mul_div_assoc]

/-- The manuscript interface: proper ports are nonloops, so a basis
containing the port exists. This formulation covers every finite matroid
with a nonloop port, and does not assume representability or regularity. -/
theorem twoSumEffectiveWeight_scale_of_not_isLoop {α : Type*}
    (M : Matroid α) (hE : M.E.Finite) (p : α)
    (hport : p ∈ M.E) (hp : ¬ M.IsLoop p) (c : ℝ≥0) (hc : 0 < c)
    (w : α → ℝ≥0) :
    twoSumEffectiveWeight M hE p (scaleNonPortWeight p c w) =
      c * twoSumEffectiveWeight M hE p w := by
  classical
  have hbase : ∃ B : Set α, M.IsBase B ∧ p ∈ B := by
    by_contra hn
    apply hp
    apply (M.isLoop_iff_forall_notMem_isBase hport).mpr
    intro B hB
    exact fun hpB => hn ⟨B, hB, hpB⟩
  obtain ⟨B, hB, hpB⟩ := hbase
  let b := (hE.subset hB.subset_ground).toFinset
  have hb : M.IsBase (b : Set α) := by
    simpa [b] using hB
  have hpb : p ∈ b := by
    simpa [b] using hpB
  exact twoSumEffectiveWeight_scaleNonPortWeight M hE p b hb hpb c hc w

end Matroid
