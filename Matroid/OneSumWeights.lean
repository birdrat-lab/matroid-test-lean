import Matroid.Sums
import Matroid.WeightedBases
import Mathlib.Basic.ENNReal.Inv
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Weighted basis sums for disjoint-ground-set one-sums. -/

open scoped NNReal ENNReal

namespace Matroid

attribute [local instance] Classical.propDecidable Classical.decEq

private theorem oneSum_isBase_union_iff {α : Type*}
    (M N : Matroid α) (hdisj : Disjoint M.E N.E)
    (hM : M.E.Nonempty) (hN : N.E.Nonempty)
    (P Q : Finset α) (hP : (P : Set α) ⊆ M.E)
    (hQ : (Q : Set α) ⊆ N.E) :
    (oneSum M N hdisj hM hN).IsBase ((P ∪ Q : Finset α) : Set α) ↔
      M.IsBase (P : Set α) ∧ N.IsBase (Q : Set α) := by
  have hPM : ((P ∪ Q : Finset α) : Set α) ∩ M.E = P := by
    ext e
    simp only [Finset.coe_union, Set.mem_inter_iff, Set.mem_union, Finset.mem_coe]
    constructor
    · rintro ⟨heP | heQ, heM⟩
      · exact heP
      · exact False.elim (Set.disjoint_left.mp hdisj heM (hQ heQ))
    · intro heP
      exact ⟨Or.inl heP, hP heP⟩
  have hQN : ((P ∪ Q : Finset α) : Set α) ∩ N.E = Q := by
    ext e
    simp only [Finset.coe_union, Set.mem_inter_iff, Set.mem_union, Finset.mem_coe]
    constructor
    · rintro ⟨heP | heQ, heN⟩
      · exact False.elim (Set.disjoint_left.mp hdisj (hP heP) heN)
      · exact heQ
    · intro heQ
      exact ⟨Or.inr heQ, hQ heQ⟩
  change (M.disjointSum N hdisj).IsBase ((P ∪ Q : Finset α) : Set α) ↔ _
  rw [Matroid.disjointSum_isBase_iff, hPM, hQN]
  constructor
  · intro h
    exact ⟨h.1, h.2.1⟩
  · intro h
    refine ⟨h.1, h.2, ?_⟩
    simpa only [Finset.coe_union] using Set.union_subset
      (hP.trans Set.subset_union_left)
      (hQ.trans Set.subset_union_right)

end Matroid

namespace Matroid

attribute [local instance] Classical.propDecidable Classical.decEq

private theorem oneSum_weightedIn_term {α R : Type*}
    [CommSemiring R] (M N : Matroid α) (hdisj : Disjoint M.E N.E)
    (hM : M.E.Nonempty) (hN : N.E.Nonempty) (τ : α) (hτ : τ ∈ M.E)
    (w : α → R) (P Q : Finset α) (hP : (P : Set α) ⊆ M.E)
    (hQ : (Q : Set α) ⊆ N.E) :
    (if (oneSum M N hdisj hM hN).IsBase ((P ∪ Q : Finset α) : Set α) ∧
          τ ∈ P ∪ Q then ∏ e ∈ (P ∪ Q).erase τ, w e else 0) =
      (if M.IsBase (P : Set α) ∧ τ ∈ P then ∏ e ∈ P.erase τ, w e else 0) *
      (if N.IsBase (Q : Set α) then ∏ e ∈ Q, w e else 0) := by
  have hτQ : τ ∉ Q := fun h => Set.disjoint_left.mp hdisj hτ (hQ h)
  have hPQ : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro e heP heQ
    exact Set.disjoint_left.mp hdisj (hP heP) (hQ heQ)
  have hprod : (∏ e ∈ (P ∪ Q).erase τ, w e) =
      (∏ e ∈ P.erase τ, w e) * (∏ e ∈ Q, w e) := by
    rw [Finset.erase_union_distrib, Finset.erase_eq_self.mpr hτQ]
    exact Finset.prod_union (hPQ.mono_left (Finset.erase_subset _ _))
  rw [hprod]
  simp only [oneSum_isBase_union_iff M N hdisj hM hN P Q hP hQ,
    Finset.mem_union, or_iff_left hτQ]
  by_cases hBP : M.IsBase (P : Set α) <;>
    by_cases hBQ : N.IsBase (Q : Set α) <;>
    by_cases ht : τ ∈ P <;> simp [hBP, hBQ, ht]

private theorem oneSum_weightedOut_term {α R : Type*}
    [CommSemiring R] (M N : Matroid α) (hdisj : Disjoint M.E N.E)
    (hM : M.E.Nonempty) (hN : N.E.Nonempty) (τ : α) (hτ : τ ∈ M.E)
    (w : α → R) (P Q : Finset α) (hP : (P : Set α) ⊆ M.E)
    (hQ : (Q : Set α) ⊆ N.E) :
    (if (oneSum M N hdisj hM hN).IsBase ((P ∪ Q : Finset α) : Set α) ∧
          τ ∉ P ∪ Q then ∏ e ∈ (P ∪ Q).erase τ, w e else 0) =
      (if M.IsBase (P : Set α) ∧ τ ∉ P then ∏ e ∈ P.erase τ, w e else 0) *
      (if N.IsBase (Q : Set α) then ∏ e ∈ Q, w e else 0) := by
  have hτQ : τ ∉ Q := fun h => Set.disjoint_left.mp hdisj hτ (hQ h)
  have hPQ : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro e heP heQ
    exact Set.disjoint_left.mp hdisj (hP heP) (hQ heQ)
  have hprod : (∏ e ∈ (P ∪ Q).erase τ, w e) =
      (∏ e ∈ P.erase τ, w e) * (∏ e ∈ Q, w e) := by
    rw [Finset.erase_union_distrib, Finset.erase_eq_self.mpr hτQ]
    exact Finset.prod_union (hPQ.mono_left (Finset.erase_subset _ _))
  rw [hprod]
  simp only [oneSum_isBase_union_iff M N hdisj hM hN P Q hP hQ,
    Finset.mem_union, not_or, and_iff_left hτQ]
  by_cases hBP : M.IsBase (P : Set α) <;>
    by_cases hBQ : N.IsBase (Q : Set α) <;>
    by_cases ht : τ ∈ P <;> simp [hBP, hBQ, ht]

/-- The target-containing weighted basis sum factors over a one-sum. -/
theorem weightedBasesIn_oneSum {α R : Type*}
    [CommSemiring R] (M N : Matroid α) (hdisj : Disjoint M.E N.E)
    (hM : M.E.Nonempty) (hN : N.E.Nonempty)
    (hME : M.E.Finite) (hNE : N.E.Finite)
    (hE : (oneSum M N hdisj hM hN).E.Finite)
    (τ : α) (hτ : τ ∈ M.E) (w : α → R) :
    weightedBasesIn (oneSum M N hdisj hM hN) hE τ w =
      weightedBasesIn M hME τ w * weightedBasesTotal N hNE w := by
  classical
  have hfinset : hE.toFinset = hME.toFinset ∪ hNE.toFinset := by
    ext e
    simp [oneSum_ground]
  have hfinDisj : Disjoint hME.toFinset hNE.toFinset := by
    apply Finset.disjoint_left.mpr
    intro e heM heN
    exact Set.disjoint_left.mp hdisj
      (by simpa using heM) (by simpa using heN)
  unfold weightedBasesIn weightedBasesTotal
  rw [hfinset, sum_powerset_union_of_disjoint _ _ hfinDisj,
    Finset.sum_product]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro P hP
  have hPground : (P : Set α) ⊆ M.E := by
    intro e he
    simpa using ((Finset.mem_powerset.mp hP) he)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Q hQ
  have hQground : (Q : Set α) ⊆ N.E := by
    intro e he
    simpa using ((Finset.mem_powerset.mp hQ) he)
  exact oneSum_weightedIn_term M N hdisj hM hN τ hτ w P Q hPground hQground

/-- The target-omitting weighted basis sum factors over a one-sum. -/
theorem weightedBasesOut_oneSum {α R : Type*}
    [CommSemiring R] (M N : Matroid α) (hdisj : Disjoint M.E N.E)
    (hM : M.E.Nonempty) (hN : N.E.Nonempty)
    (hME : M.E.Finite) (hNE : N.E.Finite)
    (hE : (oneSum M N hdisj hM hN).E.Finite)
    (τ : α) (hτ : τ ∈ M.E) (w : α → R) :
    weightedBasesOut (oneSum M N hdisj hM hN) hE τ w =
      weightedBasesOut M hME τ w * weightedBasesTotal N hNE w := by
  classical
  have hfinset : hE.toFinset = hME.toFinset ∪ hNE.toFinset := by
    ext e
    simp [oneSum_ground]
  have hfinDisj : Disjoint hME.toFinset hNE.toFinset := by
    apply Finset.disjoint_left.mpr
    intro e heM heN
    exact Set.disjoint_left.mp hdisj
      (by simpa using heM) (by simpa using heN)
  unfold weightedBasesOut weightedBasesTotal
  rw [hfinset, sum_powerset_union_of_disjoint _ _ hfinDisj,
    Finset.sum_product]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro P hP
  have hPground : (P : Set α) ⊆ M.E := by
    intro e he
    simpa using ((Finset.mem_powerset.mp hP) he)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro Q hQ
  have hQground : (Q : Set α) ⊆ N.E := by
    intro e he
    simpa using ((Finset.mem_powerset.mp hQ) he)
  exact oneSum_weightedOut_term M N hdisj hM hN τ hτ w P Q hPground hQground

/-- Positive weights give the target-free summand a nonzero basis mass. -/
theorem weightedBasesTotal_pos {α : Type*} (N : Matroid α)
    (hNE : N.E.Finite) (w : α → ℝ≥0)
    (hw : ∀ e ∈ N.E, 0 < w e) :
    0 < weightedBasesTotal N hNE w := by
  classical
  obtain ⟨B, hB⟩ := N.exists_isBase
  let hBfin : B.Finite := hNE.subset hB.subset_ground
  let b := hBfin.toFinset
  have hb : b ∈ hNE.toFinset.powerset := by
    apply Finset.mem_powerset.mpr
    intro e he
    have heB : e ∈ B := by simpa [b] using he
    simpa using hB.subset_ground heB
  have hbEq : (b : Set α) = B := by
    ext e
    simp [b]
  unfold weightedBasesTotal
  apply Finset.sum_pos' (by intros; positivity)
  refine ⟨b, hb, ?_⟩
  simp only [hbEq, hB, ↓reduceIte]
  apply Finset.prod_pos
  intro e he
  exact hw e (hB.subset_ground (by simpa [b] using he))

/-- The extended nonnegative ratio is unchanged by a positive target-free factor.
This includes zero denominators (and hence the coloop value `∞`). -/
theorem weightedBasisRatio_mul_cancel (a b c : ℝ≥0) (hc : 0 < c) :
    ((a * c : ℝ≥0) : ℝ≥0∞) / ((b * c : ℝ≥0) : ℝ≥0∞) =
      (a : ℝ≥0∞) / (b : ℝ≥0∞) := by
  rw [ENNReal.coe_mul, ENNReal.coe_mul]
  exact ENNReal.mul_div_mul_right _ _ (by simpa using hc.ne') ENNReal.coe_ne_top

/-- A finite matroid has a basis, and at positive non-target weights one of
the target-containing or target-omitting basis sums is nonzero. -/
theorem weightedBasisSums_nonzero {α : Type*} (M : Matroid α)
    (hE : M.E.Finite) (τ : α) (w : α → ℝ≥0)
    (hw : ∀ e ∈ M.E, e ≠ τ → 0 < w e) :
    weightedBasesIn M hE τ w ≠ 0 ∨ weightedBasesOut M hE τ w ≠ 0 := by
  classical
  obtain ⟨B, hB⟩ := M.exists_isBase
  let hBfin : B.Finite := hE.subset hB.subset_ground
  let b := hBfin.toFinset
  have hb : b ∈ hE.toFinset.powerset := by
    apply Finset.mem_powerset.mpr
    intro e he
    have heB : e ∈ B := by simpa [b] using he
    simpa using hB.subset_ground heB
  have hbEq : (b : Set α) = B := by
    ext e
    simp [b]
  have hprod : 0 < ∏ e ∈ b.erase τ, w e := by
    apply Finset.prod_pos
    intro e he
    exact hw e (hB.subset_ground (by
      simpa [b] using (Finset.erase_subset τ b he)))
      (Finset.ne_of_mem_erase he)
  by_cases hτB : τ ∈ B
  · left
    apply ne_of_gt
    unfold weightedBasesIn
    apply Finset.sum_pos' (by intros; positivity)
    refine ⟨b, hb, ?_⟩
    have hcond : M.IsBase (b : Set α) ∧ τ ∈ b := by
      exact ⟨by simpa [hbEq] using hB, by simpa [b] using hτB⟩
    rw [ite_eq_left hcond]
    exact hprod

  · right
    apply ne_of_gt
    unfold weightedBasesOut
    apply Finset.sum_pos' (by intros; positivity)
    refine ⟨b, hb, ?_⟩
    have hcond : M.IsBase (b : Set α) ∧ τ ∉ b := by
      exact ⟨by simpa [hbEq] using hB, by simpa [b] using hτB⟩
    rw [ite_eq_left hcond]
    exact hprod

/-- A loop cannot occur in any basis, so its target-containing mass is zero. -/
theorem weightedBasesIn_eq_zero_of_isLoop {α : Type*}
    (M : Matroid α) (hE : M.E.Finite) (τ : α) (w : α → ℝ≥0)
    (hτ : M.IsLoop τ) : weightedBasesIn M hE τ w = 0 := by
  classical
  unfold weightedBasesIn
  apply Finset.sum_eq_zero
  intro B hB
  split_ifs with h
  · exact ((M.isLoop_iff_forall_notMem_isBase).mp hτ _ h.1 h.2).elim
  · rfl

/-- At positive non-target weights, a vanishing target-omitting sum has
extended ratio `∞`; the nonvanishing numerator is proved from a basis. -/
theorem weightedBasisRatio_eq_top_of_out_eq_zero {α : Type*}
    (M : Matroid α) (hE : M.E.Finite) (τ : α) (w : α → ℝ≥0)
    (hw : ∀ e ∈ M.E, e ≠ τ → 0 < w e)
    (hout : weightedBasesOut M hE τ w = 0) :
    ((weightedBasesIn M hE τ w : ℝ≥0) : ℝ≥0∞) /
      ((weightedBasesOut M hE τ w : ℝ≥0) : ℝ≥0∞) = ∞ := by
  have hin : weightedBasesIn M hE τ w ≠ 0 :=
    (weightedBasisSums_nonzero M hE τ w hw).resolve_right (by simpa [hout])
  rw [hout]
  exact ENNReal.div_zero (by simpa using hin)

/-- A vanishing target-containing sum has extended ratio zero, including
the target-loop case. -/
theorem weightedBasisRatio_eq_zero_of_in_eq_zero {α : Type*}
    (M : Matroid α) (hE : M.E.Finite) (τ : α) (w : α → ℝ≥0)
    (hin : weightedBasesIn M hE τ w = 0) :
    ((weightedBasesIn M hE τ w : ℝ≥0) : ℝ≥0∞) /
      ((weightedBasesOut M hE τ w : ℝ≥0) : ℝ≥0∞) = 0 := by
  simp [hin]

/-- Manuscript `prop:seymour-one-sum` (N137): its ratio equality uses the
extended nonnegative reals, so zero denominators have their intended meaning. -/
theorem weightedBasisRatio_oneSum {α : Type*}
    (M N : Matroid α) (hdisj : Disjoint M.E N.E)
    (hM : M.E.Nonempty) (hN : N.E.Nonempty)
    (hME : M.E.Finite) (hNE : N.E.Finite)
    (hE : (oneSum M N hdisj hM hN).E.Finite)
    (τ : α) (hτ : τ ∈ M.E) (w : α → ℝ≥0)
    (hw : ∀ e ∈ M.E ∪ N.E, e ≠ τ → 0 < w e) :
    ((weightedBasesIn (oneSum M N hdisj hM hN) hE τ w : ℝ≥0) : ℝ≥0∞) /
      ((weightedBasesOut (oneSum M N hdisj hM hN) hE τ w : ℝ≥0) : ℝ≥0∞) =
    ((weightedBasesIn M hME τ w : ℝ≥0) : ℝ≥0∞) /
      ((weightedBasesOut M hME τ w : ℝ≥0) : ℝ≥0∞) := by
  rw [weightedBasesIn_oneSum M N hdisj hM hN hME hNE hE τ hτ w,
    weightedBasesOut_oneSum M N hdisj hM hN hME hNE hE τ hτ w]
  have hNpos : ∀ e ∈ N.E, 0 < w e := by
    intro e he
    exact hw e (Or.inr he) (fun heq =>
      Set.disjoint_left.mp hdisj hτ (heq ▸ he))
  exact weightedBasisRatio_mul_cancel _ _ _ (weightedBasesTotal_pos N hNE w hNpos)

end Matroid
