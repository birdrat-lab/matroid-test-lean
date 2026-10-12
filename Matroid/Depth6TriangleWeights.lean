import Matroid.ThreeSum
import Matroid.WeightedBases

/-! Weighted closure classes for a distinguished triangle. -/

open Set

namespace Matroid

/-- N266: the weighted signature entry for a closure class `L` of a
triangle. A summand is independent, avoids the triangle, and together with
the triangle spans the whole matroid. -/
noncomputable def weightedTrianglePhi {α R : Type*} [CommSemiring R]
    (M : Matroid α) (hE : M.E.Finite) (T L : Set α) (w : α → R) : R := by
  classical
  exact ∑ S ∈ (hE.toFinset \ (hE.toFinset.filter (· ∈ T))).powerset,
    if M.Indep (S : Set α) ∧ M.closure ((S : Set α) ∪ T) = M.E ∧
        M.closure (S : Set α) ∩ T = L
      then ∏ e ∈ S, w e else 0

/-- The five entries are exactly the all, three single-vertex, and empty
closure classes in the manuscript's notation. -/
noncomputable def weightedTriangleSignature {α R : Type*} [CommSemiring R]
    (M : Matroid α) (hE : M.E.Finite) (a b c : α) (w : α → R) :
    R × R × R × R × R :=
  (weightedTrianglePhi M hE {a, b, c} {a, b, c} w,
   weightedTrianglePhi M hE {a, b, c} {a} w,
   weightedTrianglePhi M hE {a, b, c} {b} w,
   weightedTrianglePhi M hE {a, b, c} {c} w,
   weightedTrianglePhi M hE {a, b, c} ∅ w)

/-- N266: any class outside the five possible triangle intersections has
zero mass. This uses N158 and does not assert a three-sum gluing formula. -/
theorem weightedTrianglePhi_eq_zero_of_not_five {α R : Type*}
    [CommSemiring R] (M : Matroid α) (hE : M.E.Finite)
    (a b c : α) (w : α → R)
    (hT : M.IsCircuit ({a, b, c} : Set α))
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (L : Set α)
    (hL : L ≠ ∅ ∧ L ≠ {a} ∧ L ≠ {b} ∧ L ≠ {c} ∧
      L ≠ ({a, b, c} : Set α)) :
    weightedTrianglePhi M hE {a, b, c} L w = 0 := by
  classical
  unfold weightedTrianglePhi
  apply Finset.sum_eq_zero
  intro S _
  split_ifs with h
  · rcases M.triangle_closure_five_classes hT hab hac hbc (S := (S : Set α)) with
      hnone | ha | hb | hc | hall
    · exact (hL.1 (h.2.2.symm.trans hnone)).elim
    · exact (hL.2.1 (h.2.2.symm.trans ha)).elim
    · exact (hL.2.2.1 (h.2.2.symm.trans hb)).elim
    · exact (hL.2.2.2.1 (h.2.2.symm.trans hc)).elim
    · exact (hL.2.2.2.2 (h.2.2.symm.trans hall)).elim
  · rfl

end Matroid
