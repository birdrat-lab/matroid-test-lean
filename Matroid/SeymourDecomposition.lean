import Matroid.ThreeSumExistence
import Matroid.TwoSumProper
import Matroid.CographicMinors
import Matroid.R10
import Matroid.Sums

/-! The manuscript's rooted, labeled binary decomposition tree. -/

namespace Matroid

universe u v w z

/-- A labeled one-sum node, including the manuscript's disjoint, nonempty
side convention. -/
def IsOneSum {α : Type u} (M N P : Matroid α) : Prop :=
  ∃ (hdisj : Disjoint M.E N.E) (hM : M.E.Nonempty) (hN : N.E.Nonempty),
    P = oneSum M N hdisj hM hN

/-- An exact labeled copy of the displayed `R₁₀` inside a possibly larger
ambient label type. -/
def IsR10Copy {α : Type u} (M : Matroid α) : Prop :=
  ∃ f : Fin 10 ↪ α, M = r10.mapEmbedding f

/-- N071: a finite regular matroid at every vertex of a rooted binary
tree. Internal vertices are actual labeled 1-, proper 2-, or proper
3-sums of their two children. Leaves have graphic, cographic, or R₁₀
realizations. The child grounds may include ports absent from the parent. -/
inductive SeymourDecomposition {α : Type u} : Matroid α → Type (u + 1) where
  | graphic (M : Matroid α) [M.Finite] (hR : Regular.{u,v,w} M)
      (hG : M.IsGraphic.{z,u}) : SeymourDecomposition M
  | cographic (M : Matroid α) [M.Finite] (hR : Regular.{u,v,w} M)
      (hG : M.IsCographic.{z,u}) : SeymourDecomposition M
  | r10 (M : Matroid α) [M.Finite] (hR : Regular.{u,v,w} M)
      (hCopy : IsR10Copy M) : SeymourDecomposition M
  | one {M N P : Matroid α} [M.Finite] [N.Finite] [P.Finite]
      (hR : Regular.{u,v,w} P) (h : IsOneSum M N P)
      (left : SeymourDecomposition M) (right : SeymourDecomposition N) :
      SeymourDecomposition P
  | two {M N P : Matroid α} [M.Finite] [N.Finite] [P.Finite]
      (hR : Regular.{u,v,w} P) (p : α) (h : IsProperTwoSum M N P p)
      (left : SeymourDecomposition M) (right : SeymourDecomposition N) :
      SeymourDecomposition P
  | three {M N P : Matroid α} [M.Finite] [N.Finite] [P.Finite]
      (hR : Regular.{u,v,w} P) (T : Set α) (h : IsProperThreeSum M N P T)
      (left : SeymourDecomposition M) (right : SeymourDecomposition N) :
      SeymourDecomposition P

end Matroid
