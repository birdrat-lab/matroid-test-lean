import Matroid.External.TwoSumBases
import Matroid.OneSumWeights

/-! Weighted basis sums for a proper two-sum. -/

open Set
open scoped NNReal ENNReal

namespace Matroid

universe u w

attribute [local instance] Classical.propDecidable Classical.decEq

private def gluePair {α : Type*} (p : α) (B₁ B₂ : Set α) : Set α :=
  (B₁ ∪ B₂) \ {p}

private theorem gluePair_mem_left_iff {α : Type*}
    {M N : Matroid α} {p : α} (hinter : M.E ∩ N.E = {p})
    {B₁ B₂ : Set α} (_hB₁ : B₁ ⊆ M.E) (hB₂ : B₂ ⊆ N.E)
    {x : α} (hxM : x ∈ M.E) (hxp : x ≠ p) :
    x ∈ gluePair p B₁ B₂ ↔ x ∈ B₁ := by
  have hxN : x ∉ N.E := by
    intro h
    exact hxp (by simpa [hinter] using (show x ∈ M.E ∩ N.E from ⟨hxM, h⟩))
  simp only [gluePair, mem_sdiff, mem_union, mem_singleton_iff]
  exact ⟨fun h => h.1.resolve_right (fun h₂ => hxN (hB₂ h₂)),
    fun h => ⟨Or.inl h, hxp⟩⟩

private theorem gluePair_mem_right_iff {α : Type*}
    {M N : Matroid α} {p : α} (hinter : M.E ∩ N.E = {p})
    {B₁ B₂ : Set α} (hB₁ : B₁ ⊆ M.E) (_hB₂ : B₂ ⊆ N.E)
    {x : α} (hxN : x ∈ N.E) (hxp : x ≠ p) :
    x ∈ gluePair p B₁ B₂ ↔ x ∈ B₂ := by
  have hxM : x ∉ M.E := by
    intro h
    exact hxp (by simpa [hinter] using (show x ∈ M.E ∩ N.E from ⟨h, hxN⟩))
  simp only [gluePair, mem_sdiff, mem_union, mem_singleton_iff]
  exact ⟨fun h => h.1.resolve_left (fun h₁ => hxM (hB₁ h₁)),
    fun h => ⟨Or.inr h, hxp⟩⟩

/-- The labeled 2-sum basis pair is unique. This elementary part is proved
locally, so the cited N138 premise only asserts the basis characterization. -/
theorem regularTwoSum_basisPair_unique {α : Type u}
    (M N : Matroid α) (p : α) (hinter : M.E ∩ N.E = {p})
    {B₁ B₂ C₁ C₂ : Set α}
    (hB₁ : M.IsBase B₁) (hB₂ : N.IsBase B₂)
    (hC₁ : M.IsBase C₁) (hC₂ : N.IsBase C₂)
    (hpB : p ∈ B₁ ↔ p ∉ B₂)
    (hpC : p ∈ C₁ ↔ p ∉ C₂)
    (hEq : gluePair p B₁ B₂ = gluePair p C₁ C₂) :
    B₁ = C₁ ∧ B₂ = C₂ := by
  have hleft : B₁ \ {p} = C₁ \ {p} := by
    ext x
    simp only [mem_sdiff, mem_singleton_iff]
    constructor
    · rintro ⟨hx, hxp⟩
      have h := (gluePair_mem_left_iff hinter hB₁.subset_ground
        hB₂.subset_ground (hB₁.subset_ground hx) hxp).2 hx
      rw [hEq] at h
      exact ⟨(gluePair_mem_left_iff hinter hC₁.subset_ground
        hC₂.subset_ground (hB₁.subset_ground hx) hxp).1 h, hxp⟩
    · rintro ⟨hx, hxp⟩
      have h := (gluePair_mem_left_iff hinter hC₁.subset_ground
        hC₂.subset_ground (hC₁.subset_ground hx) hxp).2 hx
      rw [← hEq] at h
      exact ⟨(gluePair_mem_left_iff hinter hB₁.subset_ground
        hB₂.subset_ground (hC₁.subset_ground hx) hxp).1 h, hxp⟩
  have hright : B₂ \ {p} = C₂ \ {p} := by
    ext x
    simp only [mem_sdiff, mem_singleton_iff]
    constructor
    · rintro ⟨hx, hxp⟩
      have h := (gluePair_mem_right_iff hinter hB₁.subset_ground
        hB₂.subset_ground (hB₂.subset_ground hx) hxp).2 hx
      rw [hEq] at h
      exact ⟨(gluePair_mem_right_iff hinter hC₁.subset_ground
        hC₂.subset_ground (hB₂.subset_ground hx) hxp).1 h, hxp⟩
    · rintro ⟨hx, hxp⟩
      have h := (gluePair_mem_right_iff hinter hC₁.subset_ground
        hC₂.subset_ground (hC₂.subset_ground hx) hxp).2 hx
      rw [← hEq] at h
      exact ⟨(gluePair_mem_right_iff hinter hB₁.subset_ground
        hB₂.subset_ground (hC₂.subset_ground hx) hxp).1 h, hxp⟩
  have hp : p ∈ B₁ ↔ p ∈ C₁ := by
    by_cases hpB₁ : p ∈ B₁ <;> by_cases hpC₁ : p ∈ C₁
    · simp [hpB₁, hpC₁]
    · have hsub : C₁ ⊆ B₁ := by
        intro x hx
        by_cases hxp : x = p
        · exact (hpC₁ (hxp ▸ hx)).elim
        · exact ((Set.ext_iff.mp hleft x).2 ⟨hx, hxp⟩).1
      have heq := hC₁.eq_of_subset_isBase hB₁ hsub
      exact False.elim (hpC₁ (heq ▸ hpB₁))
    · have hsub : B₁ ⊆ C₁ := by
        intro x hx
        by_cases hxp : x = p
        · exact (hpB₁ (hxp ▸ hx)).elim
        · exact ((Set.ext_iff.mp hleft x).1 ⟨hx, hxp⟩).1
      have heq := hB₁.eq_of_subset_isBase hC₁ hsub
      exact False.elim (hpB₁ (heq ▸ hpC₁))
    · simp [hpB₁, hpC₁]
  have hp₂ : p ∈ B₂ ↔ p ∈ C₂ := by tauto
  constructor
  · ext x
    by_cases hxp : x = p
    · simpa [hxp] using hp
    · have h := Set.ext_iff.mp hleft x
      simpa [hxp] using h
  · ext x
    by_cases hxp : x = p
    · simpa [hxp] using hp₂
    · have h := Set.ext_iff.mp hright x
      simpa [hxp] using h

private noncomputable def basisFinset {α : Type*} (M : Matroid α)
    (hE : M.E.Finite) : Finset (Finset α) :=
  hE.toFinset.powerset.filter (fun B => M.IsBase (B : Set α))

private theorem mem_basisFinset {α : Type*} (M : Matroid α)
    (hE : M.E.Finite) (B : Finset α) :
    B ∈ basisFinset M hE ↔ M.IsBase (B : Set α) := by
  classical
  simp only [basisFinset, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · exact And.right
  · intro hB
    exact ⟨by intro x hx; simpa using hB.subset_ground hx, hB⟩

private noncomputable def twoSumBasisPairs {α : Type*}
    (M N : Matroid α) (hME : M.E.Finite) (hNE : N.E.Finite)
    (p : α) : Finset (Finset α × Finset α) :=
  ((basisFinset M hME) ×ˢ (basisFinset N hNE)).filter
    (fun q => p ∈ q.1 ↔ p ∉ q.2)

private theorem mem_twoSumBasisPairs {α : Type*}
    (M N : Matroid α) (hME : M.E.Finite) (hNE : N.E.Finite)
    (p : α) (q : Finset α × Finset α) :
    q ∈ twoSumBasisPairs M N hME hNE p ↔
      M.IsBase (q.1 : Set α) ∧ N.IsBase (q.2 : Set α) ∧
        (p ∈ q.1 ↔ p ∉ q.2) := by
  classical
  simp [twoSumBasisPairs, mem_basisFinset, and_assoc]

/-- Summation along the labeled, unique basis-pair correspondence. -/
theorem sum_twoSumBases {α : Type u} {R : Type*} [AddCommMonoid R]
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p : α) (hinter : M.E ∩ N.E = {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard)
    (f : Finset α → R) :
    (∑ q ∈ twoSumBasisPairs M N M.ground_finite N.ground_finite p,
       f ((q.1 ∪ q.2).erase p)) =
      ∑ B ∈ basisFinset
        (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN)
        (by rw [regularTwoSum_ground]; exact M.ground_finite.symmDiff N.ground_finite),
        f B := by
  classical
  let P := regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN
  let hPE : P.E.Finite := by
    rw [regularTwoSum_ground]
    exact M.ground_finite.symmDiff N.ground_finite
  change (∑ q ∈ twoSumBasisPairs M N M.ground_finite N.ground_finite p,
      f ((q.1 ∪ q.2).erase p)) = ∑ B ∈ basisFinset P hPE, f B
  apply Finset.sum_bij (fun q _ => (q.1 ∪ q.2).erase p)
  · intro q hq
    obtain ⟨hB₁, hB₂, hp⟩ := (mem_twoSumBasisPairs M N _ _ p q).1 hq
    apply (mem_basisFinset P hPE _).2
    apply (External.regularTwoSum_isBase_iff M N hM hN p hinter
      hlM hlN hcM hcN hnM hnN _).2
    refine ⟨q.1, q.2, hB₁, hB₂, hp, ?_⟩
    simp only [Finset.coe_erase, Finset.coe_union]
  · intro q hq r hr heq
    obtain ⟨hB₁, hB₂, hpB⟩ := (mem_twoSumBasisPairs M N _ _ p q).1 hq
    obtain ⟨hC₁, hC₂, hpC⟩ := (mem_twoSumBasisPairs M N _ _ p r).1 hr
    have hset : gluePair p (q.1 : Set α) (q.2 : Set α) =
        gluePair p (r.1 : Set α) (r.2 : Set α) := by
      simpa only [gluePair, Finset.coe_erase, Finset.coe_union] using
        congrArg (fun B : Finset α => (B : Set α)) heq
    obtain ⟨h₁, h₂⟩ := regularTwoSum_basisPair_unique M N p hinter
      hB₁ hB₂ hC₁ hC₂ hpB hpC hset
    exact Prod.ext (Finset.coe_injective h₁) (Finset.coe_injective h₂)
  · intro B hB
    have hPB := (mem_basisFinset P hPE B).1 hB
    obtain ⟨B₁, B₂, hB₁, hB₂, hp, hEq⟩ :=
      (External.regularTwoSum_isBase_iff M N hM hN p hinter
        hlM hlN hcM hcN hnM hnN _).1 hPB
    let b₁ := (M.ground_finite.subset hB₁.subset_ground).toFinset
    let b₂ := (N.ground_finite.subset hB₂.subset_ground).toFinset
    have hb₁ : (b₁ : Set α) = B₁ := by simp [b₁]
    have hb₂ : (b₂ : Set α) = B₂ := by simp [b₂]
    refine ⟨(b₁, b₂), ?_, ?_⟩
    · apply (mem_twoSumBasisPairs M N _ _ p _).2
      have hp' : p ∈ b₁ ↔ p ∉ b₂ := by
        simpa only [← Finset.mem_coe, hb₁, hb₂] using hp
      exact ⟨by simpa only [hb₁] using hB₁,
        by simpa only [hb₂] using hB₂, hp'⟩
    · apply Finset.coe_injective
      simpa only [Finset.coe_erase, Finset.coe_union, hb₁, hb₂] using hEq.symm
  · intro q hq
    rfl

private theorem prod_gluePair_erase_target {α R : Type*} [CommMonoid R]
    (M N : Matroid α) (p τ : α) (hinter : M.E ∩ N.E = {p})
    (hτ : τ ∈ M.E) (hτp : τ ≠ p) (w : α → R)
    (B₁ B₂ : Finset α) (hB₁ : (B₁ : Set α) ⊆ M.E)
    (hB₂ : (B₂ : Set α) ⊆ N.E) :
    (∏ e ∈ ((B₁ ∪ B₂).erase p).erase τ, w e) =
      (∏ e ∈ (B₁.erase p).erase τ, w e) *
        (∏ e ∈ B₂.erase p, w e) := by
  classical
  have hτB₂ : τ ∉ B₂ := by
    intro h
    have hp : τ = p := by
      simpa [hinter] using (show τ ∈ M.E ∩ N.E from ⟨hτ, hB₂ h⟩)
    exact hτp hp
  have hdisj : Disjoint (B₁.erase p) (B₂.erase p) := by
    apply Finset.disjoint_left.mpr
    intro x hx₁ hx₂
    have hp : x = p := by
      simpa [hinter] using (show x ∈ M.E ∩ N.E from
        ⟨hB₁ (Finset.erase_subset p B₁ hx₁),
         hB₂ (Finset.erase_subset p B₂ hx₂)⟩)
    exact (Finset.ne_of_mem_erase hx₁) hp
  rw [Finset.erase_union_distrib, Finset.erase_union_distrib,
    Finset.erase_eq_self.mpr (fun h => hτB₂ (Finset.erase_subset p B₂ h))]
  exact Finset.prod_union (hdisj.mono_left (Finset.erase_subset τ _))

private theorem target_mem_gluePair_iff {α : Type*}
    (M N : Matroid α) (p τ : α) (hinter : M.E ∩ N.E = {p})
    (hτ : τ ∈ M.E) (hτp : τ ≠ p)
    (B₁ B₂ : Finset α) (_hB₁ : (B₁ : Set α) ⊆ M.E)
    (hB₂ : (B₂ : Set α) ⊆ N.E) :
    τ ∈ (B₁ ∪ B₂).erase p ↔ τ ∈ B₁ := by
  have hτB₂ : τ ∉ B₂ := by
    intro h
    exact hτp (by simpa [hinter] using
      (show τ ∈ M.E ∩ N.E from ⟨hτ, hB₂ h⟩))
  simp [hτp, hτB₂]

private theorem sum_xor_mul {α R : Type*} [CommSemiring R]
    (s t : Finset (Finset α)) (p : α)
    (A B : Finset α → R) :
    (∑ q ∈ (s ×ˢ t).filter (fun q => p ∈ q.1 ↔ p ∉ q.2),
      A q.1 * B q.2) =
    (∑ x ∈ s, if p ∈ x then 0 else A x) *
        (∑ y ∈ t, if p ∈ y then B y else 0) +
      (∑ x ∈ s, if p ∈ x then A x else 0) *
        (∑ y ∈ t, if p ∈ y then 0 else B y) := by
  classical
  rw [Finset.sum_filter, Finset.sum_product]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hpx : p ∈ x <;> by_cases hpy : p ∈ y <;>
    simp [hpx, hpy]

private noncomputable def weightedBasesSigma {α R : Type*} [CommSemiring R]
    (M : Matroid α) (hE : M.E.Finite) (τ : α) (σ : Bool)
    (w : α → R) : R :=
  ∑ B ∈ basisFinset M hE,
    if (τ ∈ B) = σ then ∏ e ∈ B.erase τ, w e else 0

private theorem weightedBasesSigma_true {α R : Type*} [CommSemiring R]
    (M : Matroid α) (hE : M.E.Finite) (τ : α) (w : α → R) :
    weightedBasesSigma M hE τ true w = weightedBasesIn M hE τ w := by
  classical
  unfold weightedBasesSigma weightedBasesIn basisFinset
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro B hB
  by_cases hbase : M.IsBase (B : Set α) <;>
    by_cases ht : τ ∈ B <;> simp [hbase, ht]

private theorem weightedBasesSigma_false {α R : Type*} [CommSemiring R]
    (M : Matroid α) (hE : M.E.Finite) (τ : α) (w : α → R) :
    weightedBasesSigma M hE τ false w = weightedBasesOut M hE τ w := by
  classical
  unfold weightedBasesSigma weightedBasesOut basisFinset
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro B hB
  by_cases hbase : M.IsBase (B : Set α) <;>
    by_cases ht : τ ∈ B <;> simp [hbase, ht]

private noncomputable def sectorMass {α R : Type*} [CommSemiring R]
    (M : Matroid α) (hE : M.E.Finite) (τ p : α) (σ : Bool)
    (port : Bool) (w : α → R) : R :=
  ∑ B ∈ basisFinset M hE,
    if (τ ∈ B) = σ ∧ (p ∈ B) = port then
      ∏ e ∈ (B.erase p).erase τ, w e else 0

/-- Each weighted two-sum target class is bilinear in the two pointed
basis classes. This is the combinatorial content of the manuscript proof. -/
theorem weightedBasesSigma_twoSum_bilinear {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p : α) (hinter : M.E ∩ N.E = {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard)
    (τ : α) (hτ : τ ∈ M.E) (hτp : τ ≠ p)
    (σ : Bool) (weight : α → ℝ≥0) :
    weightedBasesSigma
      (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN)
      (by rw [regularTwoSum_ground]; exact M.ground_finite.symmDiff N.ground_finite)
      τ σ weight =
    sectorMass M M.ground_finite τ p σ false weight *
        weightedBasesIn N N.ground_finite p weight +
      sectorMass M M.ground_finite τ p σ true weight *
        weightedBasesOut N N.ground_finite p weight := by
  classical
  let P := regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN
  let hPE : P.E.Finite := by
    rw [regularTwoSum_ground]
    exact M.ground_finite.symmDiff N.ground_finite
  change weightedBasesSigma P hPE τ σ weight = _
  unfold weightedBasesSigma
  rw [← sum_twoSumBases M N hM hN p hinter hlM hlN hcM hcN hnM hnN]
  rw [show twoSumBasisPairs M N M.ground_finite N.ground_finite p =
      ((basisFinset M M.ground_finite) ×ˢ (basisFinset N N.ground_finite)).filter
        (fun q => p ∈ q.1 ↔ p ∉ q.2) from rfl]
  have hterm (q : Finset α × Finset α)
      (hq : q ∈ ((basisFinset M M.ground_finite) ×ˢ
        (basisFinset N N.ground_finite)).filter
          (fun q => p ∈ q.1 ↔ p ∉ q.2)) :
      (if (τ ∈ (q.1 ∪ q.2).erase p) = σ then
          ∏ e ∈ ((q.1 ∪ q.2).erase p).erase τ, weight e else 0) =
        (if (τ ∈ q.1) = σ then
          ∏ e ∈ (q.1.erase p).erase τ, weight e else 0) *
          (∏ e ∈ q.2.erase p, weight e) := by
    have hq' := (mem_twoSumBasisPairs M N _ _ p q).1 hq
    have h₁ := hq'.1.subset_ground
    have h₂ := hq'.2.1.subset_ground
    simp only [target_mem_gluePair_iff M N p τ hinter hτ hτp q.1 q.2 h₁ h₂]
    by_cases ht : (τ ∈ q.1) = σ
    · simp only [ht, ↓reduceIte, prod_gluePair_erase_target M N p τ hinter hτ hτp
        weight q.1 q.2 h₁ h₂]
    · simp [ht]
  rw [Finset.sum_congr rfl hterm]
  rw [sum_xor_mul
    (basisFinset M M.ground_finite) (basisFinset N N.ground_finite) p
    (fun B => if (τ ∈ B) = σ then
      ∏ e ∈ (B.erase p).erase τ, weight e else 0)
    (fun B => ∏ e ∈ B.erase p, weight e)]
  -- The four finite sums are exactly the two sectors on the target side
  -- and the port-in/out basis sums on the target-free side.
  simp only [sectorMass]
  congr 1
  · congr 1
    · apply Finset.sum_congr rfl
      intro B hB
      by_cases hp : p ∈ B <;> by_cases ht : (τ ∈ B) = σ <;> simp [hp, ht]
    · rw [← weightedBasesSigma_true]
      unfold weightedBasesSigma
      apply Finset.sum_congr rfl
      intro B hB
      by_cases hp : p ∈ B <;> simp [hp]
  · congr 1
    · apply Finset.sum_congr rfl
      intro B hB
      by_cases hp : p ∈ B <;> by_cases ht : (τ ∈ B) = σ <;> simp [hp, ht]
    · rw [← weightedBasesSigma_false]
      unfold weightedBasesSigma
      apply Finset.sum_congr rfl
      intro B hB
      by_cases hp : p ∈ B <;> simp [hp]

private theorem prod_update_port {α R : Type*} [CommMonoid R]
    (B : Finset α) (τ p : α) (hτp : τ ≠ p)
    (weight : α → R) (m : R) :
    (∏ e ∈ B.erase τ, Function.update weight p m e) =
      (if p ∈ B then m else 1) *
        (∏ e ∈ (B.erase p).erase τ, weight e) := by
  classical
  by_cases hp : p ∈ B
  · have hp' : p ∈ B.erase τ := Finset.mem_erase.mpr ⟨hτp.symm, hp⟩
    have he : (B.erase τ).erase p = (B.erase p).erase τ := by
      ext x
      simp only [Finset.mem_erase]
      tauto
    rw [Finset.prod_update_of_mem hp', Finset.sdiff_singleton_eq_erase]
    simp only [hp, ↓reduceIte, he]
  · have hp' : p ∉ B.erase τ := fun h => hp (Finset.erase_subset τ B h)
    rw [Finset.prod_update_of_notMem hp']
    simp [hp]

private theorem weightedBasesSigma_port_update {α R : Type*}
    [CommSemiring R] (M : Matroid α) (hE : M.E.Finite)
    (τ p : α) (hτp : τ ≠ p) (σ : Bool)
    (weight : α → R) (m : R) :
    weightedBasesSigma M hE τ σ (Function.update weight p m) =
      sectorMass M hE τ p σ false weight +
        m * sectorMass M hE τ p σ true weight := by
  classical
  unfold weightedBasesSigma sectorMass
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro B hB
  rw [prod_update_port B τ p hτp weight m]
  by_cases ht : (τ ∈ B) = σ <;> by_cases hp : p ∈ B <;>
    simp [ht, hp]

private theorem weightedBasesSigma_pos_of_basis {α : Type*}
    (M : Matroid α) (hE : M.E.Finite) (τ : α) (σ : Bool)
    (weight : α → ℝ≥0)
    (hw : ∀ e ∈ M.E, e ≠ τ → 0 < weight e)
    {B : Set α} (hB : M.IsBase B) (hσ : (τ ∈ B) = σ) :
    0 < weightedBasesSigma M hE τ σ weight := by
  classical
  let b := (hE.subset hB.subset_ground).toFinset
  have hb : (b : Set α) = B := by simp [b]
  have hbb : b ∈ basisFinset M hE := by
    apply (mem_basisFinset M hE b).2
    simpa only [hb] using hB
  unfold weightedBasesSigma
  apply Finset.sum_pos' (by intros; positivity)
  refine ⟨b, hbb, ?_⟩
  have hσb : (τ ∈ b) = σ := by
    simpa only [← Finset.mem_coe, hb] using hσ
  simp only [hσb, ↓reduceIte]
  apply Finset.prod_pos
  intro e he
  exact hw e (hB.subset_ground (by
    simpa only [← Finset.mem_coe, hb] using (Finset.erase_subset τ b he)))
    (Finset.ne_of_mem_erase he)

/-- At positive non-port weights a nonloop port has positive `P₁`. -/
theorem weightedBasesIn_pos_of_not_isLoop {α : Type*}
    (N : Matroid α) (hE : N.E.Finite) (p : α)
    (hpE : p ∈ N.E) (hlN : ¬ N.IsLoop p)
    (weight : α → ℝ≥0)
    (hw : ∀ e ∈ N.E, e ≠ p → 0 < weight e) :
    0 < weightedBasesIn N hE p weight := by
  obtain ⟨B, hB, hpB⟩ := (N.isNonloop_of_not_isLoop hpE hlN).exists_mem_isBase
  rw [← weightedBasesSigma_true]
  exact weightedBasesSigma_pos_of_basis N hE p true weight hw hB
    (by simp [hpB])

/-- At positive non-port weights a noncoloop port has positive `P₀`. -/
theorem weightedBasesOut_pos_of_not_isColoop {α : Type*}
    (N : Matroid α) (hE : N.E.Finite) (p : α)
    (hcN : ¬ N.IsColoop p) (weight : α → ℝ≥0)
    (hw : ∀ e ∈ N.E, e ≠ p → 0 < weight e) :
    0 < weightedBasesOut N hE p weight := by
  classical
  have hex : ∃ B : Set α, N.IsBase B ∧ p ∉ B := by
    by_contra h
    apply hcN
    apply N.isColoop_iff_forall_mem_isBase.mpr
    intro B hB
    by_contra hp
    exact h ⟨B, hB, hp⟩
  obtain ⟨B, hB, hpB⟩ := hex
  rw [← weightedBasesSigma_false]
  exact weightedBasesSigma_pos_of_basis N hE p false weight hw hB
    (by simp [hpB])

/-- The finite effective weight of a pointed matroid: manuscript
`eq:seymour-two-sum-P`, `P₀/P₁`, when `P₁ > 0`. -/
noncomputable def twoSumEffectiveWeight {α : Type*}
    (N : Matroid α) (hE : N.E.Finite) (p : α)
    (weight : α → ℝ≥0) : ℝ≥0 :=
  weightedBasesOut N hE p weight / weightedBasesIn N hE p weight

/-- One target class of the two-sum factorization, for either value of
`σ`. The proof uses the bilinear basis-pair identity and `P₁ > 0`. -/
theorem weightedBasesSigma_twoSum_factor {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p : α) (hinter : M.E ∩ N.E = {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard)
    (τ : α) (hτ : τ ∈ M.E) (hτp : τ ≠ p)
    (σ : Bool) (weight : α → ℝ≥0)
    (hP₁ : 0 < weightedBasesIn N N.ground_finite p weight) :
    weightedBasesSigma
      (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN)
      (by rw [regularTwoSum_ground]; exact M.ground_finite.symmDiff N.ground_finite)
      τ σ weight =
    weightedBasesIn N N.ground_finite p weight *
      weightedBasesSigma M M.ground_finite τ σ
        (Function.update weight p
          (twoSumEffectiveWeight N N.ground_finite p weight)) := by
  let A₀ := sectorMass M M.ground_finite τ p σ false weight
  let A₁ := sectorMass M M.ground_finite τ p σ true weight
  let P₀ := weightedBasesOut N N.ground_finite p weight
  let P₁ := weightedBasesIn N N.ground_finite p weight
  have hcancel : P₁ * (P₀ / P₁) = P₀ := by
    rw [mul_comm]
    exact div_mul_cancel₀ P₀ hP₁.ne'
  rw [weightedBasesSigma_twoSum_bilinear M N hM hN p hinter
    hlM hlN hcM hcN hnM hnN τ hτ hτp σ weight]
  rw [weightedBasesSigma_port_update M M.ground_finite τ p hτp σ
    weight (twoSumEffectiveWeight N N.ground_finite p weight)]
  change A₀ * P₁ + A₁ * P₀ = P₁ * (A₀ + (P₀ / P₁) * A₁)
  calc
    A₀ * P₁ + A₁ * P₀ = P₁ * A₀ + (P₁ * (P₀ / P₁)) * A₁ := by
      rw [hcancel]
      ac_rfl
    _ = P₁ * (A₀ + (P₀ / P₁) * A₁) := by ring

theorem twoSum_target_mem_ground {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p : α) (hinter : M.E ∩ N.E = {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard)
    (τ : α) (hτ : τ ∈ M.E) (hτp : τ ≠ p) :
    τ ∈ (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN).E := by
  rw [regularTwoSum_ground]
  apply Set.mem_symmDiff.mpr
  left
  refine ⟨hτ, ?_⟩
  intro hτN
  exact hτp (by simpa [hinter] using
    (show τ ∈ M.E ∩ N.E from ⟨hτ, hτN⟩))

private theorem twoSum_Nweight_pos {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p : α) (hinter : M.E ∩ N.E = {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard)
    (weight : α → ℝ≥0)
    (hw : ∀ e ∈ (regularTwoSum M N hM hN p hinter
      hlM hlN hcM hcN hnM hnN).E, 0 < weight e) :
    ∀ e ∈ N.E, e ≠ p → 0 < weight e := by
  intro e heN hep
  apply hw e
  rw [regularTwoSum_ground]
  apply Set.mem_symmDiff.mpr
  right
  refine ⟨heN, ?_⟩
  intro heM
  exact hep (by simpa [hinter] using
    (show e ∈ M.E ∩ N.E from ⟨heM, heN⟩))

/-- Properness and positive surviving weights make both pointed basis
sums positive, so the manuscript's finite effective weight is positive. -/
theorem twoSumEffectiveWeight_pos {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p : α) (hinter : M.E ∩ N.E = {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard)
    (weight : α → ℝ≥0)
    (hw : ∀ e ∈ (regularTwoSum M N hM hN p hinter
      hlM hlN hcM hcN hnM hnN).E, 0 < weight e) :
    0 < weightedBasesOut N N.ground_finite p weight ∧
    0 < weightedBasesIn N N.ground_finite p weight ∧
    0 < twoSumEffectiveWeight N N.ground_finite p weight := by
  have hpN : p ∈ N.E := by
    have hp : p ∈ M.E ∩ N.E := by rw [hinter]; simp
    exact hp.2
  have hwN := twoSum_Nweight_pos M N hM hN p hinter hlM hlN hcM hcN
    hnM hnN weight hw
  have hP₀ := weightedBasesOut_pos_of_not_isColoop N N.ground_finite p
    hcN weight hwN
  have hP₁ := weightedBasesIn_pos_of_not_isLoop N N.ground_finite p
    hpN hlN weight hwN
  exact ⟨hP₀, hP₁, div_pos hP₀ hP₁⟩

/-- Manuscript `thm:seymour-two-sum`, target-containing equation. -/
theorem weightedBasesIn_twoSum {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p : α) (hinter : M.E ∩ N.E = {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard)
    (τ : α) (hτ : τ ∈ M.E) (hτp : τ ≠ p)
    (weight : α → ℝ≥0)
    (hw : ∀ e ∈ (regularTwoSum M N hM hN p hinter
      hlM hlN hcM hcN hnM hnN).E, 0 < weight e) :
    weightedBasesIn
      (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN)
      (by rw [regularTwoSum_ground]; exact M.ground_finite.symmDiff N.ground_finite)
      τ weight =
    weightedBasesIn N N.ground_finite p weight *
      weightedBasesIn M M.ground_finite τ
        (Function.update weight p
          (twoSumEffectiveWeight N N.ground_finite p weight)) := by
  simpa only [weightedBasesSigma_true] using
    weightedBasesSigma_twoSum_factor M N hM hN p hinter hlM hlN hcM hcN
    hnM hnN τ hτ hτp true weight
    (twoSumEffectiveWeight_pos M N hM hN p hinter hlM hlN hcM hcN hnM hnN
      weight hw).2.1

/-- Manuscript `thm:seymour-two-sum`, target-omitting equation. -/
theorem weightedBasesOut_twoSum {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p : α) (hinter : M.E ∩ N.E = {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard)
    (τ : α) (hτ : τ ∈ M.E) (hτp : τ ≠ p)
    (weight : α → ℝ≥0)
    (hw : ∀ e ∈ (regularTwoSum M N hM hN p hinter
      hlM hlN hcM hcN hnM hnN).E, 0 < weight e) :
    weightedBasesOut
      (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN)
      (by rw [regularTwoSum_ground]; exact M.ground_finite.symmDiff N.ground_finite)
      τ weight =
    weightedBasesIn N N.ground_finite p weight *
      weightedBasesOut M M.ground_finite τ
        (Function.update weight p
          (twoSumEffectiveWeight N N.ground_finite p weight)) := by
  simpa only [weightedBasesSigma_false] using
    weightedBasesSigma_twoSum_factor M N hM hN p hinter hlM hlN hcM hcN
    hnM hnN τ hτ hτp false weight
    (twoSumEffectiveWeight_pos M N hM hN p hinter hlM hlN hcM hcN hnM hnN
      weight hw).2.1

/-- The replacement keeps every non-target weight of the target-side
matroid strictly positive. -/
theorem twoSum_replacement_weight_pos {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p : α) (hinter : M.E ∩ N.E = {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard)
    (τ : α) (_hτ : τ ∈ M.E) (_hτp : τ ≠ p)
    (weight : α → ℝ≥0)
    (hw : ∀ e ∈ (regularTwoSum M N hM hN p hinter
      hlM hlN hcM hcN hnM hnN).E, 0 < weight e) :
    ∀ e ∈ M.E, e ≠ τ →
      0 < Function.update weight p
        (twoSumEffectiveWeight N N.ground_finite p weight) e := by
  intro e heM heτ
  by_cases hep : e = p
  · subst e
    simpa using (twoSumEffectiveWeight_pos M N hM hN p hinter hlM hlN
      hcM hcN hnM hnN weight hw).2.2
  · rw [Function.update_of_ne hep]
    apply hw e
    exact twoSum_target_mem_ground M N hM hN p hinter hlM hlN hcM hcN
      hnM hnN e heM hep

/-- Manuscript `eq:seymour-two-sum-ratio`: equality in extended
nonnegative reals, including zero and infinite target ratios. -/
theorem weightedBasisRatio_twoSum {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p : α) (hinter : M.E ∩ N.E = {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard)
    (τ : α) (hτ : τ ∈ M.E) (hτp : τ ≠ p)
    (weight : α → ℝ≥0)
    (hw : ∀ e ∈ (regularTwoSum M N hM hN p hinter
      hlM hlN hcM hcN hnM hnN).E, 0 < weight e) :
    ((weightedBasesIn
      (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN)
      (by rw [regularTwoSum_ground]; exact M.ground_finite.symmDiff N.ground_finite)
      τ weight : ℝ≥0) : ℝ≥0∞) /
    ((weightedBasesOut
      (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN)
      (by rw [regularTwoSum_ground]; exact M.ground_finite.symmDiff N.ground_finite)
      τ weight : ℝ≥0) : ℝ≥0∞) =
    ((weightedBasesIn M M.ground_finite τ
      (Function.update weight p
        (twoSumEffectiveWeight N N.ground_finite p weight)) : ℝ≥0) : ℝ≥0∞) /
    ((weightedBasesOut M M.ground_finite τ
      (Function.update weight p
        (twoSumEffectiveWeight N N.ground_finite p weight)) : ℝ≥0) : ℝ≥0∞) := by
  rw [weightedBasesIn_twoSum M N hM hN p hinter hlM hlN hcM hcN
    hnM hnN τ hτ hτp weight hw,
    weightedBasesOut_twoSum M N hM hN p hinter hlM hlN hcM hcN
    hnM hnN τ hτ hτp weight hw]
  let wi := Function.update weight p (twoSumEffectiveWeight N N.ground_finite p weight)
  let a := weightedBasesIn M M.ground_finite τ wi
  let b := weightedBasesOut M M.ground_finite τ wi
  let c := weightedBasesIn N N.ground_finite p weight
  have hc : 0 < c :=
    (twoSumEffectiveWeight_pos M N hM hN p hinter hlM hlN hcM hcN hnM hnN
      weight hw).2.1
  change ((c * a : ℝ≥0) : ℝ≥0∞) / ((c * b : ℝ≥0) : ℝ≥0∞) =
    (a : ℝ≥0∞) / (b : ℝ≥0∞)
  rw [mul_comm c a, mul_comm c b]
  exact weightedBasisRatio_mul_cancel a b c hc

/-- Positive weights on both sides rule out the indeterminate `0/0`
target case in the two-sum ratio statement. -/
theorem weightedBasisSums_twoSum_nonzero {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p : α) (hinter : M.E ∩ N.E = {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard)
    (τ : α) (hτ : τ ∈ M.E) (hτp : τ ≠ p)
    (weight : α → ℝ≥0)
    (hw : ∀ e ∈ (regularTwoSum M N hM hN p hinter
      hlM hlN hcM hcN hnM hnN).E, 0 < weight e) :
    (weightedBasesIn
      (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN)
      (by rw [regularTwoSum_ground]; exact M.ground_finite.symmDiff N.ground_finite)
      τ weight ≠ 0 ∨
     weightedBasesOut
      (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN)
      (by rw [regularTwoSum_ground]; exact M.ground_finite.symmDiff N.ground_finite)
      τ weight ≠ 0) ∧
    (weightedBasesIn M M.ground_finite τ
      (Function.update weight p
        (twoSumEffectiveWeight N N.ground_finite p weight)) ≠ 0 ∨
     weightedBasesOut M M.ground_finite τ
      (Function.update weight p
        (twoSumEffectiveWeight N N.ground_finite p weight)) ≠ 0) := by
  have hPE : (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN).E.Finite := by
    rw [regularTwoSum_ground]
    exact M.ground_finite.symmDiff N.ground_finite
  constructor
  · apply weightedBasisSums_nonzero _ hPE τ weight
    intro e he heτ
    exact hw e he
  · apply weightedBasisSums_nonzero M M.ground_finite τ
      (Function.update weight p
        (twoSumEffectiveWeight N N.ground_finite p weight))
    exact twoSum_replacement_weight_pos M N hM hN p hinter hlM hlN hcM hcN
      hnM hnN τ hτ hτp weight hw

/-- A target loop gives zero extended ratio after the two-sum
factorization. -/
theorem weightedBasisRatio_twoSum_eq_zero_of_targetLoop {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p : α) (hinter : M.E ∩ N.E = {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard)
    (τ : α) (hτ : τ ∈ M.E) (hτp : τ ≠ p)
    (weight : α → ℝ≥0)
    (hw : ∀ e ∈ (regularTwoSum M N hM hN p hinter
      hlM hlN hcM hcN hnM hnN).E, 0 < weight e)
    (hloop : M.IsLoop τ) :
    ((weightedBasesIn
      (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN)
      (by rw [regularTwoSum_ground]; exact M.ground_finite.symmDiff N.ground_finite)
      τ weight : ℝ≥0) : ℝ≥0∞) /
    ((weightedBasesOut
      (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN)
      (by rw [regularTwoSum_ground]; exact M.ground_finite.symmDiff N.ground_finite)
      τ weight : ℝ≥0) : ℝ≥0∞) = 0 := by
  rw [weightedBasisRatio_twoSum M N hM hN p hinter hlM hlN hcM hcN
    hnM hnN τ hτ hτp weight hw]
  exact weightedBasisRatio_eq_zero_of_in_eq_zero M M.ground_finite τ
    (Function.update weight p
      (twoSumEffectiveWeight N N.ground_finite p weight))
    (weightedBasesIn_eq_zero_of_isLoop M M.ground_finite τ _ hloop)

/-- A target coloop gives infinite extended ratio after the two-sum
factorization. -/
theorem weightedBasisRatio_twoSum_eq_top_of_targetColoop {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p : α) (hinter : M.E ∩ N.E = {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard)
    (τ : α) (hτ : τ ∈ M.E) (hτp : τ ≠ p)
    (weight : α → ℝ≥0)
    (hw : ∀ e ∈ (regularTwoSum M N hM hN p hinter
      hlM hlN hcM hcN hnM hnN).E, 0 < weight e)
    (hcoloop : M.IsColoop τ) :
    ((weightedBasesIn
      (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN)
      (by rw [regularTwoSum_ground]; exact M.ground_finite.symmDiff N.ground_finite)
      τ weight : ℝ≥0) : ℝ≥0∞) /
    ((weightedBasesOut
      (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN)
      (by rw [regularTwoSum_ground]; exact M.ground_finite.symmDiff N.ground_finite)
      τ weight : ℝ≥0) : ℝ≥0∞) = ∞ := by
  rw [weightedBasisRatio_twoSum M N hM hN p hinter hlM hlN hcM hcN
    hnM hnN τ hτ hτp weight hw]
  exact weightedBasisRatio_eq_top_of_out_eq_zero M M.ground_finite τ
    (Function.update weight p
      (twoSumEffectiveWeight N N.ground_finite p weight))
    (twoSum_replacement_weight_pos M N hM hN p hinter hlM hlN hcM hcN
      hnM hnN τ hτ hτp weight hw)
    (weightedBasesOut_eq_zero_of_isColoop M M.ground_finite τ _ hcoloop)

end Matroid
