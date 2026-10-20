import Matroid.ThreeSumExistence
import Mathlib.Combinatorics.Matroid.Constructions

/-!
The sole premise below is the displayed three-sum basis formula in
Bérczi, Mátravölgyi and Schwarcz, *Reconfiguration of Basis Pairs in Regular
Matroids*, Section 2, immediately after Lemma 2.3 (arXiv:2311.07130,
equation displayed on lines 256–259 of the HTML version). It has the two
contraction/deletion families and the middle family of augmented bases with
three distinct triangle indices. The paper assumes binary factors and a
coindependent common triangle; our finite regular proper-sum interface is a
specialization. This premise does not itself assert the manuscript's
closure-class compatibility translation (N159).
-/

namespace Matroid.External

universe u w

/-- The published three-family characterization of bases of a proper
three-sum, on the original labels. No closure-class or weighted identity is
admitted here. -/
theorem properThreeSum_isBase_iff {α : Type u}
    (M N P : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (T : Set α) (h : IsProperThreeSum M N P T)
    (a b c : α) (hT : T = {a, b, c})
    (B : Set α) :
    P.IsBase B ↔
      ∃ S₁ S₂ : Set α, S₁ ⊆ M.E \ T ∧ S₂ ⊆ N.E \ T ∧
        B = S₁ ∪ S₂ ∧
        ((M ／ T).IsBase S₁ ∧ (N ＼ T).IsBase S₂ ∨
         (∃ i j k : α, {i, j, k} = T ∧
            M.IsBase (S₁ ∪ {i}) ∧ M.IsBase (S₁ ∪ {j}) ∧
            N.IsBase (S₂ ∪ {i}) ∧ N.IsBase (S₂ ∪ {k})) ∨
         (M ＼ T).IsBase S₁ ∧ (N ／ T).IsBase S₂) := by
  sorry

end Matroid.External
