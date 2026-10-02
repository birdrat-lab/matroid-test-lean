import Mathlib.Combinatorics.Matroid.Basic

/-! # Colored -/

open Set

namespace Matroid

/-- Manuscript: `def:colored-matroid` (N073). The color map is defined exactly
on the ground set; no matroid operation depends on it. -/
structure Colored (α Color : Type*) where
  matroid : Matroid α
  finite : matroid.Finite
  color : matroid.E → Color

end Matroid
