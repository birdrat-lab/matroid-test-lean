import Matroid.TwoSumWeights

/-! Reproducible N138/N139 trust audit. Only N138's externally cited
basis correspondence should carry `sorryAx`; N139 inherits it transitively. -/

#print axioms Matroid.regularTwoSum_indep_of_bases_first_port
#print axioms Matroid.External.regularTwoSum_isBase_iff
#print axioms Matroid.regularTwoSum_basisPair_unique
#print axioms Matroid.sum_twoSumBases
#print axioms Matroid.twoSumEffectiveWeight_pos
#print axioms Matroid.weightedBasesIn_twoSum
#print axioms Matroid.weightedBasesOut_twoSum
#print axioms Matroid.weightedBasisRatio_twoSum
#print axioms Matroid.weightedBasisSums_twoSum_nonzero
#print axioms Matroid.weightedBasisRatio_twoSum_eq_zero_of_targetLoop
#print axioms Matroid.weightedBasisRatio_twoSum_eq_top_of_targetColoop
