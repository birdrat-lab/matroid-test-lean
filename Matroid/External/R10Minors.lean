import Matroid.K33
import Matroid.R10CircuitParity
import Mathlib.Combinatorics.Matroid.Map

/-! Oxley, *Matroid Theory*, second edition (2011), Lemma 6.6.9,
printed p. 210: for each element e of R10, deletion is isomorphic to
M(K3,3), and contraction is isomorphic to its dual. The proof identifies
the binary matrix A10 and uses its element-transitive automorphism group.
Our `r10BinaryMatrix` is that A10 with labels shifted from 1..10 to Fin 10.
The embeddings here make the abstract isomorphisms precise on the retained
original labels. The K3,3 edge type has nine distinct edge labels. -/

namespace Matroid.External

/-- N172's exact external premise, stated on Oxley's binary A10. -/
theorem binaryR10_delete_isK33 (e : Fin 10) :
    ∃ f : K33.Edge ↪ Fin 10,
      Set.range f = Set.univ \ {e} ∧
      (vectorMatroid (K := ZMod 2) Set.univ Set.finite_univ
        r10BinaryMatrix.col ＼ {e}) = K33.cycleMatroid.mapEmbedding f := by
  sorry

/-- N173's exact external premise, stated on Oxley's binary A10. -/
theorem binaryR10_contract_isK33Dual (e : Fin 10) :
    ∃ f : K33.Edge ↪ Fin 10,
      Set.range f = Set.univ \ {e} ∧
      (vectorMatroid (K := ZMod 2) Set.univ Set.finite_univ
        r10BinaryMatrix.col ／ {e}) = K33.bondMatroid.mapEmbedding f := by
  sorry

end Matroid.External
