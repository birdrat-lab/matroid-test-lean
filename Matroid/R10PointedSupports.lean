import Matroid.R10BasisCount
import Matroid.WeightedBases

/-! Evaluation bridges from the checked R10 monomial supports to the
manuscript's actual weighted basis sums. -/

namespace Matroid

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Every target-omitting monomial appears exactly once in the public
weighted basis sum. -/
theorem r10_weightedBasesOut_eq_support_sum {R : Type*} [CommSemiring R]
    (e : Fin 10) (w : Fin 10 → R) :
    weightedBasesOut r10 r10.ground_finite e w =
      ∑ B ∈ r10PointedOutSupport e, ∏ x ∈ B, w x := by
  classical
  simp [weightedBasesOut, r10PointedOutSupport, r10BasisFamilyCert,
    r10_ground, r10_isBase_iff_cert, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro B _
  by_cases hcert : r10BasisCert B
  · by_cases he : e ∈ B
    · simp [hcert, he]
    · simp [hcert, he]
  · simp [hcert]

/-- Every target-containing monomial appears exactly once after deleting
the target label from its basis. -/
theorem r10_weightedBasesIn_eq_support_sum {R : Type*} [CommSemiring R]
    (e : Fin 10) (w : Fin 10 → R) :
    weightedBasesIn r10 r10.ground_finite e w =
      ∑ S ∈ r10PointedInSupport e, ∏ x ∈ S, w x := by
  classical
  unfold r10PointedInSupport
  have hinj : Set.InjOn (fun B : Finset (Fin 10) => B.erase e)
      ↑(r10BasisFamilyCert.filter (fun B => e ∈ B)) := by
    intro B hB C hC hErase
    have heB : e ∈ B := (Finset.mem_filter.mp hB).2
    have heC : e ∈ C := (Finset.mem_filter.mp hC).2
    change B.erase e = C.erase e at hErase
    calc
      B = insert e (B.erase e) := (Finset.insert_erase heB).symm
      _ = insert e (C.erase e) := by rw [hErase]
      _ = C := Finset.insert_erase heC
  rw [Finset.sum_image hinj]
  simp [weightedBasesIn, r10BasisFamilyCert,
    r10_ground, r10_isBase_iff_cert, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro B _
  by_cases hcert : r10BasisCert B
  · by_cases he : e ∈ B
    · simp only [hcert, he, true_and, ↓reduceIte]
      congr 1
      ext x
      simp
    · simp [hcert, he]
  · simp [hcert]

end Matroid
