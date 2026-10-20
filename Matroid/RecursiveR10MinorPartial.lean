import Matroid.RecursiveR10
import Matroid.TwoElementCircuitRelabel
import Mathlib.Combinatorics.Matroid.Minor.Order

/-! Initial matroid-level minor infrastructure for N223. The nine-stage
two-sum minor transport remains open. -/

namespace Matroid

/-- An exact-label copy of the displayed R10 occurs as a minor. The
embedding may change after contracting attached children to pairs. -/
def ContainsR10Minor {α : Type*} (M : Matroid α) : Prop :=
  ∃ f : Fin 10 ↪ α, r10.mapEmbedding f ≤m M

theorem containsR10Minor_mapEmbedding {α : Type*} (f : Fin 10 ↪ α) :
    ContainsR10Minor (r10.mapEmbedding f) :=
  ⟨f, Matroid.IsMinor.refl⟩

/-- Minor containment transports along any labeled ambient minor. -/
theorem ContainsR10Minor.of_minor {α : Type*} {M N : Matroid α}
    (hN : ContainsR10Minor N) (hNM : N ≤m M) :
    ContainsR10Minor M := by
  obtain ⟨f, hf⟩ := hN
  exact ⟨f, hf.trans hNM⟩

/-- The root of the recursive construction contains R10 at depth one. -/
theorem RecursiveR10.base_containsR10Minor {α : Type*}
    (_rootTarget : Fin 10) (f : Fin 10 ↪ α) :
    ContainsR10Minor (r10.mapEmbedding f) :=
  containsR10Minor_mapEmbedding f

end Matroid
