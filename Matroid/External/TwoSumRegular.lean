import Matroid.TwoSumCycles

/-! N068. Oxley, *Matroid Theory*, 2nd ed., Corollary 7.1.26,
printed p. 263: regular matroids are closed under proper 2-sums.
The N065 cycle characterization identifies this exact labeled object with
Oxley's proper 2-sum. Mathlib has no matching closure theorem. -/

namespace Matroid.External

universe u w

/-- Source-verified external regularity closure for the existing original-label
proper two-sum, with all properness hypotheses retained. -/
theorem regularTwoSum_regular {α : Type u}
    {M N : Matroid α} [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p : α) (hinter : M.E ∩ N.E = {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard) :
    Regular.{u, 0, w}
      (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN) := by
  sorry

end Matroid.External
