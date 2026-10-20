import Matroid.RecursiveR10
import Matroid.R10TargetCircuits
import Matroid.TwoSumTargetClosure
import Matroid.MapCircuitUnion
import Matroid.TwoElementCircuit
import Matroid.TwoSumRank
import Matroid.ParallelTarget
import Matroid.ThreeSum
import Matroid.R10Minors

/-! Reproducible axiom audit for the current five-batch invocation. -/

#print axioms Matroid.r10CircuitCandidate_isCircuit
#print axioms Matroid.r10_common_circuit
#print axioms Matroid.IsProperTwoSum
#print axioms Matroid.isProperTwoSum_regularTwoSum
#print axioms Matroid.RecursiveR10
#print axioms Matroid.r10_targetCircuit_iff
#print axioms Matroid.r10_minimalTargetSpanning_iff
#print axioms Matroid.regularTwoSum_available_subset_ground
#print axioms Matroid.regularTwoSum_target_mem_closure_iff
#print axioms Matroid.isCircuitUnion_iff_empty_or_pair
#print axioms Matroid.regularTwoSum_cycle_iff_relabelPort
#print axioms Matroid.mapEquiv_isCircuit_iff
#print axioms Matroid.regularTwoSum_eRank_add_one
#print axioms Matroid.parallelTargetCopy_target_pair_isCircuit
#print axioms Matroid.IsParallelTargetConstruction
#print axioms Matroid.exists_parallelTargetConstruction
#print axioms Matroid.triangle_pair_mem_span_iff_exists_subset_sum
#print axioms Matroid.K33.cycleMatroid_ground
#print axioms Matroid.External.binaryR10_delete_isK33
#print axioms Matroid.External.binaryR10_contract_isK33Dual
#print axioms Matroid.r10_delete_isK33
#print axioms Matroid.r10_contract_isK33Dual
