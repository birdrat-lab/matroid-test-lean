import Matroid.External.R10Minors

/-! The source-verified minor identities for the manuscript's real TU R10.
These wrappers inherit only the two explicit Oxley premises above. -/

namespace Matroid

/-- N172: any single-element deletion of R10 is a relabeled K3,3 cycle matroid. -/
theorem r10_delete_isK33 (e : Fin 10) :
    ∃ f : K33.Edge ↪ Fin 10,
      Set.range f = Set.univ \ {e} ∧
      (r10 ＼ {e}) = K33.cycleMatroid.mapEmbedding f := by
  rw [r10_eq_binary]
  exact External.binaryR10_delete_isK33 e

/-- N173: any single-element contraction of R10 is a relabeled K3,3 bond matroid. -/
theorem r10_contract_isK33Dual (e : Fin 10) :
    ∃ f : K33.Edge ↪ Fin 10,
      Set.range f = Set.univ \ {e} ∧
      (r10 ／ {e}) = K33.bondMatroid.mapEmbedding f := by
  rw [r10_eq_binary]
  exact External.binaryR10_contract_isK33Dual e

end Matroid
