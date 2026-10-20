import Mathlib.Combinatorics.Matroid.Circuit

/-! Cocircuits as minimal basis-hitting sets. -/

namespace Matroid

/-- N019: the manuscript's cocircuit is exactly an inclusion-minimal set
that meets every whole-matroid basis. This is mathlib's cocircuit
characterization on the original ground labels. -/
theorem isCocircuit_iff_minimal_basis_hitting {α : Type*}
    (M : Matroid α) (K : Set α) :
    M.IsCocircuit K ↔
      Minimal (fun X : Set α =>
        ∀ B : Set α, M.IsBase B → (X ∩ B).Nonempty) K :=
  M.isCocircuit_iff_minimal

end Matroid
