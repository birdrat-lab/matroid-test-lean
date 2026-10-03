import Matroid.Representation

/-! # Regular matroids -/

namespace Matroid

/-- Manuscript: `def:regular-matroid` (N051). A regular matroid is
representable over every field. The universe parameters range independently
over field types and representation spaces. -/
def Regular.{u,v,w} {α : Type u} (M : Matroid α) : Prop :=
  ∀ (K : Type v) [Field K], RepresentableOver.{u,v,w} K M

end Matroid
