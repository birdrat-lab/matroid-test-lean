import Matroid.R10PointedEquivariance
import Matroid.TwoElementCircuitRelabel
import Matroid.ThreeSumExistence
import Matroid.External.ThreeSumBases
import Matroid.R10NoThreeSum
import Matroid.R10AutomorphismFourCertificate
import Matroid.RecursiveCocircuitPortSupport
import Matroid.RegularEffectiveWeightMonotonicity

/-! Transitive axiom audit for scheduler batches 26–30. -/

#print axioms Matroid.r10_pointed_basis_polynomials_equivariant
#print axioms Matroid.mapEquiv_isCircuitUnion_iff
#print axioms Matroid.twoSumWithPair_cycle_iff_relabelPort
#print axioms Matroid.twoSumWithPair_eq_mapEquiv_swap
#print axioms Matroid.ThreeSumCycle.candidate_isCircuitUnion
#print axioms Matroid.ThreeSumCycle.of_candidate_isCircuitUnion
#print axioms Matroid.exists_properThreeSum
#print axioms Matroid.External.properThreeSum_isBase_iff
#print axioms Matroid.IsOneSum
#print axioms Matroid.IsR10Copy
#print axioms Matroid.SeymourDecomposition
#print axioms Matroid.IsR10Copy.circuit_card_ne_three
#print axioms Matroid.IsR10Copy.not_properThreeSum_left
#print axioms Matroid.IsR10Copy.not_properThreeSum_right
#print axioms Matroid.r10FourDependencyCert_count
#print axioms Matroid.r10TargetSixCocircuit_nonTarget_card
#print axioms Matroid.r10TargetSixCocircuit_activePort_bound
#print axioms Matroid.External.regular_rayleigh_pair
#print axioms Matroid.rayleigh_affine_ratio_mono
#print axioms Matroid.regularEffectiveWeight_update_mono
#print axioms Matroid.regularEffectiveWeight_mono_of_positive
