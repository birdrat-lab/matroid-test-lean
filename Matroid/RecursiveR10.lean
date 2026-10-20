import Matroid.R10Connected
import Matroid.TwoSumProper
import Mathlib.Combinatorics.Matroid.Map

/-! The manuscript's recursive pointed R10 construction. -/

namespace Matroid

/-- N218: a stage of the recursive pointed R10 construction. At each step
the root is a fresh labeled copy of the displayed R10; the nine children are
pairwise disjoint outside their separately identified ports; and the ten
intermediate matroids record the nine proper 2-sums in order. The target is
the untouched root target. Existence and preservation properties belong to
the following recursive-closure propositions. -/
inductive RecursiveR10 {α : Type*} (rootTarget : Fin 10) :
    ℕ → Matroid α → α → Prop
  | base (f : Fin 10 ↪ α) :
      RecursiveR10 rootTarget 1 (r10.mapEmbedding f) (f rootTarget)
  | step {h : ℕ}
      (f : Fin 10 ↪ α)
      (ports : Fin 9 ≃ {e : Fin 10 // e ≠ rootTarget})
      (children : Fin 9 → Matroid α)
      (stages : Fin 10 → Matroid α)
      (child_recursive : ∀ i : Fin 9,
        RecursiveR10 rootTarget h (children i) (f (ports i).1))
      (child_disjoint : ∀ i j : Fin 9, i ≠ j →
        Disjoint (children i).E (children j).E)
      (root_child_intersection : ∀ i : Fin 9,
        (r10.mapEmbedding f).E ∩ (children i).E = {f (ports i).1})
      (initial : stages 0 = r10.mapEmbedding f)
      (attach : ∀ i : Fin 9,
        IsProperTwoSum (stages (Fin.castSucc i)) (children i)
          (stages (Fin.succ i)) (f (ports i).1)) :
      RecursiveR10 rootTarget (h + 1) (stages (Fin.last 9)) (f rootTarget)

end Matroid
