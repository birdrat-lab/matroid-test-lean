import Matroid.R10TargetCircuits
import Mathlib.Tactic.FinCases

/-! Exact finite certificates for N200's target-circuit incidence. -/

namespace Matroid

/-- The nine displayed six-element target circuits are pairwise distinct. -/
theorem r10TargetSixCandidate_injective :
    Function.Injective r10TargetSixCandidate := by
  decide

/-- Each non-target label occurs in exactly five of the nine six-element
target circuits, matching the manuscript's natural-program lower bound. -/
theorem r10_targetSixCircuit_incidence (e : Fin 10) (he : e ≠ 0) :
    (Finset.univ.filter (fun i : Fin 9 => e ∈ r10TargetSixCandidate i)).card = 5 := by
  fin_cases e
  · exact (he rfl).elim
  all_goals decide

/-- The certificate refers to genuine target circuits of the displayed R10. -/
theorem r10_targetSixCircuit_family (i : Fin 9) :
    r10.IsCircuit (r10TargetSixCandidate i : Set (Fin 10)) ∧
      0 ∈ r10TargetSixCandidate i ∧
      (r10TargetSixCandidate i).card = 6 :=
  ⟨r10TargetSixCandidate_isCircuit i,
   r10TargetSixCandidate_target i,
   r10TargetSixCandidate_card i⟩

end Matroid
