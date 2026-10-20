import Matroid.R10Minors
import Matroid.CographicMinors
import Mathlib.Combinatorics.Matroid.Minor.Order

/-! Matroid-level first reduction for the proper-R10-minor claim (N177).
The remaining proof must factor through a single deletion or contraction
and transport the K3,3 graph realizations to surviving original labels. -/

namespace Matroid

/-- Every genuine strict minor loses at least one original ground element;
in particular there are no proper matroid minors with the same labels. -/
theorem IsStrictMinor.exists_lost_ground_element {α : Type*}
    {M N : Matroid α} (h : N <m M) :
    ∃ e ∈ M.E, e ∉ N.E := by
  have hsub : N.E ⊆ M.E := h.isMinor.subset
  by_contra hnone
  push Not at hnone
  have hrev : M.E ⊆ N.E := by
    intro e he
    exact hnone e he
  have heq : M = N := h.isMinor.eq_of_ground_subset hrev
  exact h.ne heq.symm

/-- Any strict minor factors through one deletion or one contraction of a
lost original label. This is the structural reduction needed before applying
the published single-element R10 minor identities. -/
theorem IsStrictMinor.exists_single_step_factor {α : Type*}
    {M N : Matroid α} (h : N <m M) :
    ∃ e ∈ M.E, N ≤m (M ／ {e}) ∨ N ≤m (M ＼ {e}) := by
  obtain ⟨e, heM, heN⟩ := h.exists_lost_ground_element
  obtain ⟨C, D, hCE, hDE, hCD, hEq⟩ :=
    h.isMinor.exists_eq_contract_delete_disjoint
  have heCD : e ∈ C ∨ e ∈ D := by
    rw [hEq, Matroid.delete_ground, Matroid.contract_ground] at heN
    by_contra hnone
    push Not at hnone
    exact heN ⟨⟨heM, hnone.1⟩, hnone.2⟩
  refine ⟨e, heM, ?_⟩
  rcases heCD with heC | heD
  · left
    refine ⟨C \ {e}, D, ?_⟩
    have hC : ({e} : Set α) ∪ (C \ {e}) = C := by
      ext x
      by_cases hx : x = e
      · subst x; simp [heC]
      · simp [hx]
    rw [hEq, Matroid.contract_contract, hC]
  · right
    refine ⟨C, D \ {e}, ?_⟩
    have hD : ({e} : Set α) ∪ (D \ {e}) = D := by
      ext x
      by_cases hx : x = e
      · subst x; simp [heD]
      · simp [hx]
    have hdisj : Disjoint C ({e} : Set α) := by
      apply Set.disjoint_left.mpr
      intro x hxC hxE
      have hxe : x = e := by simpa using hxE
      subst x
      exact (Set.disjoint_left.mp hCD hxC) heD
    rw [hEq, ← Matroid.contract_delete_comm M hdisj,
      Matroid.delete_delete, hD]

end Matroid
