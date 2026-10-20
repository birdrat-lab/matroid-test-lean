import Matroid.TwoSumCycles

/-! N148 external premise. Oxley, *Matroid Theory*, 2nd ed., Proposition
7.1.20 (printed p. 260) gives the circuit classification. Oxley, "A class
of non-binary matroids" (1990), p. 182, states under the same proper 2-sum
hypotheses that the dual of a 2-sum is the 2-sum of the duals. Applying the
circuit classification to the duals gives the following complete labeled
cocircuit classification. The manuscript uses only its target-side case. -/

namespace Matroid.External

universe u w

theorem regularTwoSum_isCocircuit_iff {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p : α) (hinter : M.E ∩ N.E = {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard)
    (D : Set α) :
    (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN).IsCocircuit D ↔
      (M.IsCocircuit D ∧ p ∉ D) ∨
      (N.IsCocircuit D ∧ p ∉ D) ∨
      ∃ D₁ D₂ : Set α, M.IsCocircuit D₁ ∧ N.IsCocircuit D₂ ∧
        p ∈ D₁ ∧ p ∈ D₂ ∧ D = (D₁ ∪ D₂) \ {p} := by
  sorry

end Matroid.External
