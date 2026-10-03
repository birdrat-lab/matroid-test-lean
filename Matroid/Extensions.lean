import Mathlib.Combinatorics.Matroid.Minor.Restrict

/-! # Single-element extensions -/

namespace Matroid

/-- Manuscript: `def:single-element-extension` (N036). -/
def IsSingleElementExtension {α : Type*} (N M : Matroid α) (τ : α) : Prop :=
  τ ∉ N.E ∧ M.E = insert τ N.E ∧ M ↾ N.E = N

end Matroid
