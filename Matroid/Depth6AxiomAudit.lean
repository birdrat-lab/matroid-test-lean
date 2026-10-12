import Matroid.Depth6Basics
import Matroid.Depth6Quotient
import Matroid.Depth6Support
import Matroid.Depth6TriangleWeights
import Matroid.Depth6UniformRegular
import Matroid.R10
import Matroid.OneSumWeights

/-! Reproducible depth-six axiom audit. Any `sorryAx` invalidates a
kernel-proved classification. Ordinary foundational axioms are listed by Lean. -/

#print axioms Matroid.isFlat_iff_closure_eq_manuscript
#print axioms Matroid.IsFlat.eRk_lt_eRk_insert
#print axioms Matroid.isFlat_iff_forall_eRk_lt_insert
#print axioms Matroid.IsFlat.eq_ground_of_isBase_subset
#print axioms Matroid.IsHyperplane
#print axioms Matroid.isLoop_contract_of_mem_closure
#print axioms Matroid.IsModularPair
#print axioms Matroid.flat_join_isFlat
#print axioms Matroid.flat_join_least
#print axioms Matroid.flat_join_upper
#print axioms Matroid.Represents.isFlat_functional_zero
#print axioms Matroid.Regular.delete
#print axioms Matroid.Regular.contract
#print axioms Matroid.Regular.contract_any
#print axioms Matroid.freeRelationVector
#print axioms Matroid.freeRelationMatroid
#print axioms Matroid.freeRelation_generators_indep
#print axioms Matroid.freeRelation_generators_isBase
#print axioms Matroid.freeRelation_relation_span
#print axioms Matroid.freeRelation_contract_ground
#print axioms Matroid.freeRelation_contract_eq_quotient
#print axioms Matroid.freeRelation_positive_closure
#print axioms Matroid.freeRelation_positive_closure_of_equation
#print axioms Matroid.freeRelation_negative_nonclosure
#print axioms Matroid.positiveSpanningSupport
#print axioms Matroid.positiveReconstructionSupport
#print axioms Matroid.positiveSpanningSupport_eq_reconstruction
#print axioms Matroid.twoSumPortRatio_eq_top_of_isLoop
#print axioms Matroid.twoSumPortRatio_eq_zero_of_isColoop
#print axioms Matroid.r10Matrix_rank
#print axioms Matroid.r10_eRank
#print axioms Matroid.weightedTrianglePhi
#print axioms Matroid.weightedTriangleSignature
#print axioms Matroid.weightedTrianglePhi_eq_zero_of_not_five
#print axioms Matroid.oneRowOnes
#print axioms Matroid.oneRowOnes_isTotallyUnimodular
#print axioms Matroid.oneRowOnesReal
#print axioms Matroid.oneRowOnesReal_isTotallyUnimodular
#print axioms Matroid.oneRowOnesReal_linearIndependent_iff
#print axioms Matroid.uniformOn_one_eq_oneRowVectorMatroid
#print axioms Matroid.uniformOn_one_regular
