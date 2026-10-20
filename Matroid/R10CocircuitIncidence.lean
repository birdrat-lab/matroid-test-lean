import Matroid.R10MaxNegative
import Matroid.DualCocircuit
import Mathlib.Tactic.FinCases

/-! Exact labeled finite cocircuit family for the natural R10 program. -/

namespace Matroid

/-- Nine target cocircuits dual to the punctured row-column double stars.
The quotient and remainder index the row and column in manuscript order. -/
def r10TargetSixCocircuit (i : Fin 9) : Finset (Fin 10) :=
  Finset.univ \ r10MaxNegativeStar
    ⟨i.val / 3, by omega⟩ ⟨i.val % 3, by omega⟩

theorem r10TargetSixCocircuit_card (i : Fin 9) :
    (r10TargetSixCocircuit i).card = 6 := by
  fin_cases i <;> decide

theorem r10TargetSixCocircuit_target (i : Fin 9) :
    0 ∈ r10TargetSixCocircuit i := by
  fin_cases i <;> decide

theorem r10TargetSixCocircuit_injective :
    Function.Injective r10TargetSixCocircuit := by
  decide

/-- The nine exact candidates are genuine manuscript cocircuits. -/
theorem r10TargetSixCocircuit_isCocircuit (i : Fin 9) :
    r10.IsHyperplaneCocircuit (r10TargetSixCocircuit i : Set (Fin 10)) := by
  let s := r10MaxNegativeStar
    ⟨i.val / 3, by omega⟩ ⟨i.val % 3, by omega⟩
  have h0 : 0 ∉ s := by
    fin_cases i <;> decide
  have hcert : r10MaxNegativeCert s :=
    Or.inl ⟨⟨i.val / 3, by omega⟩, ⟨i.val % 3, by omega⟩, rfl⟩
  have hmax := (r10_maximal_negative_iff s h0).2 hcert
  have hs : (s : Set (Fin 10)) ⊆ r10.E \ {0} := by
    intro x hx
    exact ⟨by simp, by intro he; subst x; exact h0 (by simpa using hx)⟩
  have hc := r10.maximal_nonspanning_isHyperplaneCocircuit
    0 (s : Set (Fin 10)) (by simp) hs hmax.1 hmax.2
  simpa [r10TargetSixCocircuit, s, r10_ground] using hc

private theorem r10_complement_card_six_iff_card_four
    (s : Finset (Fin 10)) :
    (Finset.univ \ s).card = 6 ↔ s.card = 4 := by
  simp [Finset.card_sdiff]
  omega

/-- The nine candidates are the complete six-element target-cocircuit
family, not merely nine examples. N196 rules out the six larger
row/column-star complements. -/
theorem r10_targetSixCocircuit_iff (D : Finset (Fin 10)) :
    (r10.IsHyperplaneCocircuit (D : Set (Fin 10)) ∧
      0 ∈ D ∧ D.card = 6) ↔
      ∃ i : Fin 9, D = r10TargetSixCocircuit i := by
  constructor
  · rintro ⟨⟨H, hH, hEq⟩, h0D, hDcard⟩
    have hHfin : H.Finite := r10.ground_finite.subset hH.1.subset_ground
    let s : Finset (Fin 10) := hHfin.toFinset
    have hHs : (s : Set (Fin 10)) = H := hHfin.coe_toFinset
    have hDfin : D = Finset.univ \ s := by
      apply Finset.coe_injective
      simpa [hHs, r10_ground] using hEq
    have h0s : 0 ∉ s := by
      intro h
      have : 0 ∈ (Finset.univ \ s : Finset (Fin 10)) := hDfin ▸ h0D
      exact (Finset.mem_sdiff.mp this).2 h
    have hτ : 0 ∈ r10.E \ H := by
      exact ⟨by simp, by simpa [← hHs] using h0s⟩
    have hmax := hH.maximal_target_nonspanning 0 hτ
    have hcert : r10MaxNegativeCert s :=
      (r10_maximal_negative_iff s h0s).1 (by simpa [hHs] using hmax)
    have hscard : s.card = 4 :=
      (r10_complement_card_six_iff_card_four s).1 (by rwa [← hDfin])
    have hp : ∃ i : Fin 9, Finset.univ \ s = r10TargetSixCocircuit i := by
      rcases hcert with ⟨i, j, hEqS⟩ | ⟨i, hEqS⟩ | ⟨j, hEqS⟩
      · rw [hEqS]
        fin_cases i <;> fin_cases j <;> decide
      · have hwrong : ∀ i : Fin 3,
            ((Finset.univ.erase 0) \ r10Row i).card ≠ 4 := by decide
        rw [hEqS] at hscard
        exact False.elim ((hwrong i) hscard)
      · have hwrong : ∀ j : Fin 3,
            ((Finset.univ.erase 0) \ r10Column j).card ≠ 4 := by decide
        rw [hEqS] at hscard
        exact False.elim ((hwrong j) hscard)
    obtain ⟨i, hi⟩ := hp
    exact ⟨i, hDfin.trans hi⟩
  · rintro ⟨i, rfl⟩
    exact ⟨r10TargetSixCocircuit_isCocircuit i,
      r10TargetSixCocircuit_target i,
      r10TargetSixCocircuit_card i⟩

/-- Every non-target label lies in exactly five of these nine distinct
six-element target cocircuits. This is the manuscript's incidence count. -/
theorem r10_targetSixCocircuit_incidence (e : Fin 10) (he : e ≠ 0) :
    (Finset.univ.filter (fun i : Fin 9 => e ∈ r10TargetSixCocircuit i)).card = 5 := by
  fin_cases e
  · exact (he rfl).elim
  all_goals decide

end Matroid
