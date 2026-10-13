import Matroid.TwoSumCycles
import Mathlib.Data.Set.Card

/-! Ground-set cardinality for a proper two-sum. -/

open Set

namespace Matroid

private theorem symmDiff_eq_sdiff_union_of_inter_singleton
    {α : Type*} {E F : Set α} {p : α}
    (hinter : E ∩ F = {p}) :
    _root_.symmDiff E F = (E \ {p}) ∪ (F \ {p}) := by
  have hp : p ∈ E ∩ F := by rw [hinter]; simp
  have hpE : p ∈ E := hp.1
  have hpF : p ∈ F := hp.2
  ext x
  have hboth : x ∈ E → x ∈ F → x = p := by
    intro hxE hxF
    have hx : x ∈ ({p} : Set α) := hinter ▸ ⟨hxE, hxF⟩
    simpa using hx
  by_cases hxp : x = p
  · subst x
    simp [Set.mem_symmDiff, hpE, hpF]
  · have hnot : ¬ (x ∈ E ∧ x ∈ F) := by
      rintro ⟨hxE, hxF⟩
      exact hxp (hboth hxE hxF)
    simp only [Set.mem_symmDiff, Set.mem_union, Set.mem_sdiff,
      Set.mem_singleton_iff, hxp, not_false_eq_true, and_true]
    tauto

private theorem ncard_symmDiff_add_two_of_inter_singleton
    {α : Type*} {E F : Set α} {p : α}
    (hE : E.Finite) (hF : F.Finite)
    (hinter : E ∩ F = {p}) :
    (_root_.symmDiff E F).ncard + 2 = E.ncard + F.ncard := by
  have hp : p ∈ E ∩ F := by rw [hinter]; simp
  have hpE : p ∈ E := hp.1
  have hpF : p ∈ F := hp.2
  have hdisj : Disjoint (E \ {p}) (F \ {p}) := by
    apply Set.disjoint_left.mpr
    intro x hxE hxF
    have hx : x ∈ E ∩ F := ⟨hxE.1, hxF.1⟩
    rw [hinter] at hx
    exact hxE.2 hx
  rw [symmDiff_eq_sdiff_union_of_inter_singleton hinter,
    Set.ncard_union_eq hdisj hE.sdiff hF.sdiff]
  have hEc := Set.ncard_sdiff_singleton_add_one hpE hE
  have hFc := Set.ncard_sdiff_singleton_add_one hpF hF
  omega

/-- N149: the exact labeled proper two-sum ground size. -/
theorem regularTwoSum_ground_ncard {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u,0,w} M) (hN : Regular.{u,0,w} N)
    (p : α) (hinter : M.E ∩ N.E = {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard) :
    (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN).E.ncard =
      M.E.ncard + N.E.ncard - 2 := by
  rw [regularTwoSum_ground]
  have h := ncard_symmDiff_add_two_of_inter_singleton
    M.ground_finite N.ground_finite hinter
  omega

end Matroid
