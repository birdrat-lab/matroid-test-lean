import Matroid.R10CircuitParity
import Mathlib.Combinatorics.Matroid.Map

/-! Oxley, *Matroid Theory*, 2nd ed. (2011), proof of Lemma 6.6.9,
printed p. 210: the binary matrix `A₁₀` has permutations within each block
of five elements and an automorphism crossing the blocks. Therefore its
automorphism group is transitive on the ten labeled elements. This admitted
premise states only transitivity, not the separately enumerated order 720.
The matrix below is the manuscript's indexed binary reduction of `A₁₀`;
`r10_eq_binary` is an admission-free bridge to the real TU realization. -/

namespace Matroid.External

theorem binaryR10_element_transitive (a b : Fin 10) :
    ∃ σ : Equiv.Perm (Fin 10), σ a = b ∧
      (vectorMatroid (K := ZMod 2) Set.univ Set.finite_univ
        r10BinaryMatrix.col).mapEquiv σ =
      vectorMatroid (K := ZMod 2) Set.univ Set.finite_univ
        r10BinaryMatrix.col := by
  sorry

end Matroid.External
