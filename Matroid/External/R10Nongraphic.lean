import Matroid.CographicMinors
import Matroid.R10CircuitParity

/-! Oxley, *Matroid Theory*, 2nd ed. (2011), Proposition 14.5.3(i)
lists R10 as an excluded minor for the union of graphic and cographic
matroids, hence it is neither. Section 13.1 explicitly names the binary
`A₁₀` realization; Lemma 6.6.9 and the admission-free `r10_eq_binary`
identify its ten original labels with the manuscript's real TU matrix.
The project graphic/cographic predicates allow finite labeled multigraphs,
including loops and parallel edges, as in the standard matroid classes. -/

namespace Matroid.External

universe u

/-- Exact cited obstruction for the indexed binary R10, with arbitrary
finite labeled graph realizations quantified by `IsGraphic` and
`IsCographic`. -/
theorem binaryR10_not_graphic_or_cographic :
    ¬ (vectorMatroid (K := ZMod 2) Set.univ Set.finite_univ
        r10BinaryMatrix.col).IsGraphic.{u,0} ∧
    ¬ (vectorMatroid (K := ZMod 2) Set.univ Set.finite_univ
        r10BinaryMatrix.col).IsCographic.{u,0} := by
  sorry

end Matroid.External
