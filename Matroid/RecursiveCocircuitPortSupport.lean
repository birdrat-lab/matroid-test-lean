import Matroid.RecursiveCocircuitBounds
import Matroid.R10CocircuitIncidence

/-! The exact active-port count at the root of the recursive R₁₀
cocircuit construction. Transport through all nine proper two-sum stages
remains open in N227. -/

namespace Matroid

/-- Every displayed six-element target cocircuit of R₁₀ has exactly five
non-target ports. -/
theorem r10TargetSixCocircuit_nonTarget_card (i : Fin 9) :
    ((r10TargetSixCocircuit i).erase 0).card = 5 := by
  rw [Finset.card_erase_of_mem (r10TargetSixCocircuit_target i),
    r10TargetSixCocircuit_card]

/-- Replacing only the ports active in one root target cocircuit by child
supports of size at most `l` gives at most `5*l` leaves. This is the
counting obligation behind N227's global stage invariant. -/
theorem r10TargetSixCocircuit_activePort_bound {α : Type*} [DecidableEq α]
    (i : Fin 9) (childSupport : Fin 10 → Finset α) (l : ℕ)
    (hchild : ∀ e ∈ (r10TargetSixCocircuit i).erase 0,
      (childSupport e).card ≤ l) :
    (((r10TargetSixCocircuit i).erase 0).biUnion childSupport).card ≤
      5 * l := by
  exact (Finset.card_biUnion_le_card_mul _ _ l hchild).trans
    (by rw [r10TargetSixCocircuit_nonTarget_card])

end Matroid
