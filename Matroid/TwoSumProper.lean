import Matroid.TwoSumCycles

/-! Exact proper-sum predicate shared by manuscript constructions. -/

namespace Matroid

/-- A proper labeled 2-sum, specified by the exact cycle correspondence
proved for regular factors in N065. The hypotheses record the manuscript's
nonloop, noncoloop, and size requirements at the common port. -/
def IsProperTwoSum {α : Type*} (M N P : Matroid α) (p : α) : Prop :=
  M.E ∩ N.E = {p} ∧
  ¬ M.IsLoop p ∧ ¬ N.IsLoop p ∧
  ¬ M.IsColoop p ∧ ¬ N.IsColoop p ∧
  3 ≤ M.E.ncard ∧ 3 ≤ N.E.ncard ∧
  P.E = _root_.symmDiff M.E N.E ∧
  ∀ X : Set α, P.IsCircuitUnion X ↔ TwoSumCycle M N p X

/-- The N065 constructor satisfies the recursive construction's precise
proper-sum predicate under exactly its recorded hypotheses. -/
theorem isProperTwoSum_regularTwoSum {α : Type*}
    {M N : Matroid α} [M.Finite] [N.Finite]
    (hM : Regular M) (hN : Regular N)
    (p : α) (hinter : M.E ∩ N.E = {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard) :
    IsProperTwoSum M N
      (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN) p := by
  refine ⟨hinter, hlM, hlN, hcM, hcN, hnM, hnN,
    regularTwoSum_ground M N hM hN p hinter hlM hlN hcM hcN hnM hnN, ?_⟩
  intro X
  exact (Classical.choose_spec (exists_twoSum_of_regular hM hN p hinter)).2 X

end Matroid
