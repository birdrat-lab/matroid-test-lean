import Matroid.R10Automorphism
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-! A smaller finite predicate for the still-open R₁₀ automorphism order. -/

namespace Matroid

/-- The four-element binary dependencies of the displayed R₁₀ matrix. -/
def r10FourDependencyCert (C : Finset (Fin 10)) : Prop :=
  C.card = 4 ∧ ∑ e ∈ C, r10BinaryMatrix.col e = 0

instance (C : Finset (Fin 10)) : Decidable (r10FourDependencyCert C) := by
  unfold r10FourDependencyCert
  infer_instance

/-- A checked count of the four-column dependencies used as a candidate
smaller automorphism certificate. This does not count automorphisms. -/
theorem r10FourDependencyCert_count :
    (((Finset.univ : Finset (Fin 10)).powersetCard 4).filter
      r10FourDependencyCert).card = 15 := by
  decide

end Matroid
