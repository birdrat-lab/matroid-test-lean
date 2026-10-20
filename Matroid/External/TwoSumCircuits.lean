import Matroid.TwoSumCycles

/-! Oxley, *Matroid Theory*, 2nd ed. (2011), Proposition 7.1.20,
printed p. 260: the circuits of a proper 2-sum are precisely circuits of
either factor avoiding the port and unions of two port-containing circuits
with the port removed. The source is stated for arbitrary matroids whose
shared point is nonseparating. The finite regular, nonloop/noncoloop, and
size-three assumptions below specialize it to the N065 labeled construction.
This is the isolated external N146 premise; no target-specific clause is
admitted. -/

namespace Matroid.External

universe u w

theorem regularTwoSum_isCircuit_iff {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p : α) (hinter : M.E ∩ N.E = {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard)
    (C : Set α) :
    (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN).IsCircuit C ↔
      (M.IsCircuit C ∧ p ∉ C) ∨
      (N.IsCircuit C ∧ p ∉ C) ∨
      ∃ C₁ C₂ : Set α, M.IsCircuit C₁ ∧ N.IsCircuit C₂ ∧
        p ∈ C₁ ∧ p ∈ C₂ ∧ C = (C₁ ∪ C₂) \ {p} := by
  sorry

end Matroid.External
