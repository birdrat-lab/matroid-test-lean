import Matroid.External.R10Transitivity

/-! N186: the cited binary automorphisms act on the manuscript's exact
ten labels, and the checked field-transfer bridge identifies that binary
matroid with `r10`. -/

namespace Matroid

theorem r10_element_transitive (a b : Fin 10) :
    ∃ σ : Equiv.Perm (Fin 10), σ a = b ∧ r10.mapEquiv σ = r10 := by
  obtain ⟨σ, hab, hσ⟩ := External.binaryR10_element_transitive a b
  exact ⟨σ, hab, by simpa [r10_eq_binary] using hσ⟩

end Matroid
