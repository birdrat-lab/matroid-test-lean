import Matroid.ThreeSum
import Matroid.R10Automorphism
import Matroid.RecursiveCircuitBounds
import Matroid.R10CircuitIncidence
import Matroid.GeneratedModularCut
import Matroid.ModularCutExtension
import Matroid.R10MaxNegative
import Matroid.K4Triangle

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
