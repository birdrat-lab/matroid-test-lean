import Matroid.RecursiveCircuitBounds
import Matroid.R10CircuitIncidence

/-! The root support calculation for the recursive target-circuit bound.
The transport through the nine intermediate two-sum stages remains N226's
unproved induction step. -/

namespace Matroid

/-- Each displayed six-element target circuit uses exactly five of the nine
non-target root ports. -/
theorem r10TargetSixCircuit_nonTarget_card (i : Fin 9) :
    ((r10TargetSixCandidate i).erase 0).card = 5 := by
  rw [Finset.card_erase_of_mem (r10TargetSixCandidate_target i),
    r10TargetSixCandidate_card]

/-- If each child substitution contributes at most `l` leaves, then the
five ports of a chosen root target circuit contribute at most `5*l` leaves.
This is the finite root count required by the manuscript's induction. -/
theorem r10TargetSixCircuit_activePort_bound {α : Type*} [DecidableEq α]
    (i : Fin 9) (childSupport : Fin 10 → Finset α) (l : ℕ)
    (hchild : ∀ e ∈ (r10TargetSixCandidate i).erase 0,
      (childSupport e).card ≤ l) :
    (((r10TargetSixCandidate i).erase 0).biUnion childSupport).card ≤
      5 * l := by
  exact (Finset.card_biUnion_le_card_mul _ _ l hchild).trans
    (by rw [r10TargetSixCircuit_nonTarget_card])

end Matroid
