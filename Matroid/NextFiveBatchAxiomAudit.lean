import Matroid.ThreeSum
import Matroid.R10Automorphism
import Matroid.RecursiveCircuitBounds
import Matroid.R10CircuitIncidence
import Matroid.GeneratedModularCut
import Matroid.ModularCutExtension
import Matroid.R10MaxNegative
import Matroid.K4Triangle
import Matroid.TriangleIdentityAlgebra
import Matroid.TwoSumTargetCocircuits
import Matroid.RecursiveCocircuitBounds
import Matroid.R10CocircuitIncidence

/-! Axiom audit for the current scheduler-directed five-batch pass. -/

#print axioms Matroid.triangle_quotient_sum_eq_zero_iff
#print axioms Matroid.threeSumCycle_side_restrict
#print axioms Matroid.binary_sum_sdiff_eq_sum_inter
#print axioms Matroid.isR10Automorphism_iff_preserves_bases
#print axioms Matroid.isR10Automorphism_iff_finset_bases
#print axioms Matroid.isCircuit_iff_minimal_nonempty_cycle
#print axioms Matroid.ext_isCircuitUnion
#print axioms Matroid.IsProperTwoSum.eq_regularTwoSum
#print axioms Matroid.IsProperTwoSum.targetCircuit_iff
#print axioms Matroid.r10TargetSixCandidate_injective
#print axioms Matroid.r10_targetSixCircuit_incidence
#print axioms Matroid.r10_targetSixCircuit_family
#print axioms Matroid.isModularCut_sInter
#print axioms Matroid.allFlats_isModularCut
#print axioms Matroid.generatedModularCut_isModularCut
#print axioms Matroid.subset_generatedModularCut
#print axioms Matroid.generatedModularCut_least
#print axioms Matroid.extension_modularCut
#print axioms Matroid.modularCut_extension_unique
#print axioms Matroid.r10_maxNegative_finite_certificate
#print axioms Matroid.r10_mem_closure_zero_iff_cert
#print axioms Matroid.r10_maximal_negative_iff
#print axioms Matroid.K4Triangle.signature
#print axioms Matroid.threeSumCycle_iff_common_trace
#print axioms Matroid.threeSumCycle_iff_finite_common_trace
#print axioms Matroid.binary_sum_union_eq_zero_iff
#print axioms Matroid.r10_indep_iff_cert
#print axioms Matroid.r10_isBase_iff_cert
#print axioms Matroid.isR10Automorphism_iff_cert
#print axioms Matroid.IsProperTwoSum.targetCircuit_ncard_le
#print axioms Matroid.triangle_identity_of_rank_two_polynomial
#print axioms Matroid.isHyperplaneCocircuit_iff_dual_isCircuit
#print axioms Matroid.External.regularTwoSum_isCocircuit_iff
#print axioms Matroid.regularTwoSum_targetCocircuit_iff
#print axioms Matroid.IsProperTwoSum.targetCocircuit_iff
#print axioms Matroid.IsProperTwoSum.targetCocircuit_ncard_le
#print axioms Matroid.r10TargetSixCocircuit_isCocircuit
#print axioms Matroid.r10TargetSixCocircuit_injective
#print axioms Matroid.r10_targetSixCocircuit_iff
#print axioms Matroid.r10_targetSixCocircuit_incidence
