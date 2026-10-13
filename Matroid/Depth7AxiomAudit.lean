import Matroid.FlatsAndCocircuits
import Matroid.PositiveCircuitSupport
import Matroid.ContractedPort
import Matroid.TwoSumCardinality
import Matroid.CographicMinors
import Matroid.TriangleClassPositivity
import Matroid.RelationFundamentalCircuit
import Matroid.R10CircuitParity
import Matroid.TwoSumBasis
import Matroid.External.TutteRegularTU

/-! Reproducible depth-seven trust audit. -/

#print axioms Matroid.IsHyperplaneCocircuit
#print axioms Matroid.isHyperplaneCocircuit_iff
#print axioms Matroid.IsModularCut
#print axioms Matroid.positiveCircuitSupport
#print axioms Matroid.positiveSpanningSupport_eq_circuitSupport
#print axioms Matroid.contractedPort_isLoop
#print axioms Matroid.contractedPort_ratio_eq_top
#print axioms Matroid.regularTwoSum_ground_ncard
#print axioms Matroid.IsCographic
#print axioms Matroid.isCographic_iff_dual_isGraphic
#print axioms Matroid.IsCographic.minor
#print axioms Matroid.weightedTriangle_a_pos
#print axioms Matroid.weightedTriangle_c_pos
#print axioms Matroid.freeRelation_mem_closure_iff_support_subset
#print axioms Matroid.freeRelation_fundCircuit_eq_support
#print axioms Matroid.positiveRelation_fundCircuit
#print axioms Matroid.positiveRelation_fundCircuit_isCircuit
#print axioms Matroid.Represents.binaryCircuit_sum_zero
#print axioms Matroid.r10BinaryMatrix_column_parity
#print axioms Matroid.r10_circuit_card_ne_three
#print axioms Matroid.IsCircuit.isCircuitUnion
#print axioms Matroid.IsCircuitUnion.eq_empty_of_subset_indep
#print axioms Matroid.regularTwoSum_indep_of_bases_first_port
#print axioms Matroid.External.regular_ground_exists_realTU
