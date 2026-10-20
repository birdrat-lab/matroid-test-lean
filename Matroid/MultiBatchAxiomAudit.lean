import Matroid.TwoSumTargetCircuits
import Matroid.R10Transitivity
import Matroid.R10Automorphism
import Matroid.TriangleIdentityAlgebra
import Matroid.External.TwoSumRegular
import Matroid.CocircuitSeparation
import Matroid.RegularFreeQuotientPartial
import Matroid.NegativeSupport
import Matroid.MaximalNonspanning

/-! Axiom audit for the current five-batch scheduler-directed run. -/

#print axioms Matroid.External.regularTwoSum_isCircuit_iff
#print axioms Matroid.regularTwoSum_targetCircuit_iff
#print axioms Matroid.r10_eq_binary
#print axioms Matroid.External.binaryR10_element_transitive
#print axioms Matroid.r10_element_transitive
#print axioms Matroid.isR10Automorphism_refl
#print axioms Matroid.triangle_identity_of_det_coefficients
#print axioms Matroid.External.regularTwoSum_regular
#print axioms Matroid.standardForm_mul_kernelBlock
#print axioms Matroid.cocircuit_separates_closure
#print axioms Matroid.IsCocircuit.isHyperplaneCocircuit
#print axioms Matroid.cocircuit_separates_closure_manuscript
#print axioms Matroid.negativeTargetSupport
#print axioms Matroid.negativeTargetSupport_spec
#print axioms Matroid.maximal_nonspanning_isHyperplane
#print axioms Matroid.maximal_nonspanning_isHyperplaneCocircuit
