import Matroid.TwoSumBasis

/-!
The sole admission below is the basis characterization of a proper 2-sum.
Source: Oxley, *Matroid Theory*, 2nd ed., Proposition 7.1.13(ii)
(parallel-connection bases), the definition of 2-sum as parallel connection
with the basepoint deleted on p. 260, and Proposition 7.1.20 (its circuit
characterization).  The local `regularTwoSum` has precisely that circuit
characterization on the original labels.  The source permits arbitrary
matroids with a nonseparating basepoint; this declaration specializes to
finite regular matroids with a nonloop, noncoloop port and at least three
elements on each side.  No weighted identity is admitted here.
-/

namespace Matroid.External

universe u w

/-- Oxley's proper 2-sum basis correspondence, on the existing labeled
`regularTwoSum` construction.  The two input bases contain the port on
exactly one side. -/
theorem regularTwoSum_isBase_iff {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p : α) (hinter : M.E ∩ N.E = {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard)
    (B : Set α) :
    (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN).IsBase B ↔
      ∃ B₁ B₂ : Set α, M.IsBase B₁ ∧ N.IsBase B₂ ∧
        (p ∈ B₁ ↔ p ∉ B₂) ∧ B = (B₁ ∪ B₂) \ {p} := by
  sorry

end Matroid.External
