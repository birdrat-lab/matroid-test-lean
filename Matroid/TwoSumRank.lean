import Matroid.External.TwoSumBases
import Mathlib.Data.Set.Card

/-! Rank of a proper two-sum (N150). -/

namespace Matroid

universe u w

/-- N150: the proper two-sum rank is the sum of factor ranks minus one.
The addition form avoids truncated subtraction in `ℕ∞`. -/
theorem regularTwoSum_eRank_add_one {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p : α) (hinter : M.E ∩ N.E = {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard) :
    (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN).eRank + 1 =
      M.eRank + N.eRank := by
  let P := regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN
  obtain ⟨B, hB⟩ := P.exists_isBase
  obtain ⟨B₁, B₂, hB₁, hB₂, hport, hEq⟩ :=
    (External.regularTwoSum_isBase_iff M N hM hN p hinter
      hlM hlN hcM hcN hnM hnN B).mp hB
  have hB₁fin : B₁.Finite := M.ground_finite.subset hB₁.subset_ground
  have hB₂fin : B₂.Finite := N.ground_finite.subset hB₂.subset_ground
  have hBfin : B.Finite := by
    rw [hEq]
    exact (hB₁fin.union hB₂fin).sdiff
  have hdisj : Disjoint B₁ B₂ := by
    apply Set.disjoint_left.mpr
    intro x hx₁ hx₂
    have hxp : x = p := by
      have hx : x ∈ ({p} : Set α) := by
        rw [← hinter]
        exact ⟨hB₁.subset_ground hx₁, hB₂.subset_ground hx₂⟩
      simpa using hx
    subst x
    by_cases hp₁ : p ∈ B₁
    · exact (hport.mp hp₁) hx₂
    · exact hp₁ hx₁
  have hpU : p ∈ B₁ ∪ B₂ := by
    by_cases hp₁ : p ∈ B₁
    · exact Or.inl hp₁
    · right
      by_contra hp₂
      exact hp₁ (hport.mpr hp₂)
  have hcard : B.ncard + 1 = B₁.ncard + B₂.ncard := by
    rw [hEq]
    calc
      ((B₁ ∪ B₂) \ {p}).ncard + 1 = (B₁ ∪ B₂).ncard :=
        Set.ncard_sdiff_singleton_add_one hpU (hB₁fin.union hB₂fin)
      _ = B₁.ncard + B₂.ncard := Set.ncard_union_eq hdisj hB₁fin hB₂fin
  have hcast : (B.ncard : ℕ∞) + 1 =
      (B₁.ncard : ℕ∞) + (B₂.ncard : ℕ∞) := by exact_mod_cast hcard
  calc
    P.eRank + 1 = (B.ncard : ℕ∞) + 1 := by
      rw [← hB.encard_eq_eRank, ← hBfin.cast_ncard_eq]
    _ = (B₁.ncard : ℕ∞) + (B₂.ncard : ℕ∞) := hcast
    _ = M.eRank + N.eRank := by
      rw [← hB₁.encard_eq_eRank, ← hB₂.encard_eq_eRank,
        ← hB₁fin.cast_ncard_eq, ← hB₂fin.cast_ncard_eq]

end Matroid
