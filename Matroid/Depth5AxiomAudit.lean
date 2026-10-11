import Matroid.OneSumWeights
import Matroid.RowCompression
import Matroid.TotallyUnimodular
import Matroid.TUWeightedBasisDeterminant

/-! Reproducible axiom audit for the four depth-5 target interfaces. -/

#print axioms Matroid.weightedBasesIn_oneSum
#print axioms Matroid.weightedBasesOut_oneSum
#print axioms Matroid.weightedBasesTotal_pos
#print axioms Matroid.weightedBasesIn_eq_zero_of_isLoop
#print axioms Matroid.weightedBasisRatio_eq_top_of_out_eq_zero
#print axioms Matroid.weightedBasisRatio_oneSum
#print axioms Matrix.exists_rowCompression_factor
#print axioms Matroid.rowCompression_after_columnRestriction
#print axioms Matrix.linearIndependent_cols_iff_exists_minor_det_ne_zero
#print axioms Matrix.IsTotallyUnimodular.intCast_minor_ne_zero_iff
#print axioms Matroid.vectorMatroid_intCast_eq_of_totallyUnimodular
#print axioms Matrix.IsTotallyUnimodular.exists_intCast_eq
#print axioms Matroid.vectorMatroid_realTU_represents_over_field
#print axioms Matrix.weightedGram_det_sum_minor
#print axioms Matrix.weightedCauchyBinet
#print axioms Matrix.weightedCauchyBinet_real
#print axioms Matrix.IsTotallyUnimodular.det_submatrix_sq_of_ne_zero
#print axioms Matroid.weightedGram_det_eq_weightedBasesTotal_of_tu
