import Mathlib.Combinatorics.Matroid.Circuit

/-! # Cycles -/

open Set

namespace Matroid

/-- Manuscript: `def:matroid-cycle` (N063). A finite disjoint union of circuits,
including the empty union, is a cycle in the manuscript's terminology. -/
def IsCircuitUnion {α : Type*} (M : Matroid α) (X : Set α) : Prop :=
  ∃ Cs : Finset (Set α),
    (∀ C ∈ Cs, M.IsCircuit C) ∧
    (∀ C ∈ Cs, ∀ D ∈ Cs, C ≠ D → Disjoint C D) ∧
    X = ⋃₀ (Cs : Set (Set α))

end Matroid
