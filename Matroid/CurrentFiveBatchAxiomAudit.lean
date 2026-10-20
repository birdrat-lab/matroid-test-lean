import Matroid.ThreeSumClosureClassBridge
import Matroid.CocircuitBasisHitting
import Matroid.RecursiveR10MinorPartial
import Matroid.R10Nongraphic
import Matroid.RegularFreeQuotientPartial
import Matroid.R10ProperMinorPartial
import Matroid.R10FixedWeightContribution
import Matroid.RecursiveCircuitPortSupport
import Matroid.R10SmallMinorPartial

/-! Transitive axiom audit for scheduler batches 31–35. Append each new
target-facing declaration as the selected batches progress. -/

#print axioms Matroid.External.properThreeSum_isBase_iff
#print axioms Matroid.IsProperThreeSum.left_coindep
#print axioms Matroid.IsProperThreeSum.right_coindep
#print axioms Matroid.coindep_delete_isBase_iff_closure_all
#print axioms Matroid.isCocircuit_iff_minimal_basis_hitting
#print axioms Matroid.ContainsR10Minor
#print axioms Matroid.ContainsR10Minor.of_minor
#print axioms Matroid.RecursiveR10.base_containsR10Minor
#print axioms Matroid.External.binaryR10_not_graphic_or_cographic
#print axioms Matroid.r10_not_graphic_or_cographic
#print axioms Matroid.standardForm_augmented_mulVec_quotient
#print axioms Matroid.IsStrictMinor.exists_lost_ground_element
#print axioms Matroid.IsStrictMinor.exists_single_step_factor
#print axioms Matroid.r10_targetFree_effectiveWeight_eq
#print axioms Matroid.r10_targetBasisRatio_eq
#print axioms Matroid.r10TargetSixCircuit_nonTarget_card
#print axioms Matroid.r10TargetSixCircuit_activePort_bound
#print axioms Matroid.IsMinor.strict_of_ground_ncard_lt
#print axioms Matroid.r10_small_ground_two_lost
#print axioms Matroid.r10_smallMinor_factors_strict_single_step
