import Matroid.CocircuitSeparation

/-! The pointed-matroid form of manuscript `def:negative-support` (N107). -/

namespace Matroid

/-- Cardinalities of target cocircuits avoiding the available set,
after removing the target itself from the count. -/
def negativeSupportCandidates {α : Type*} (M : Matroid α) [M.Finite]
    (τ : α) (A : Set α) : Set ℕ :=
  {n | ∃ D : Set α,
    M.IsHyperplaneCocircuit D ∧ τ ∈ D ∧ Disjoint D A ∧ D.ncard - 1 = n}

/-- N107: negative support is defined on a genuine negative pointed input.
The proof parameters retain the domain convention of the manuscript. -/
noncomputable def negativeTargetSupport {α : Type*} (M : Matroid α) [M.Finite]
    (τ : α) (A : Set α) (_hA : A ⊆ M.E \ {τ})
    (_hτ : τ ∈ M.E) (_hneg : τ ∉ M.closure A) : ℕ :=
  sInf (negativeSupportCandidates M τ A)

/-- The defining minimum is attained; N032 supplies a candidate. -/
theorem negativeTargetSupport_spec {α : Type*} (M : Matroid α) [M.Finite]
    (τ : α) (A : Set α) (hA : A ⊆ M.E \ {τ})
    (hτ : τ ∈ M.E) (hneg : τ ∉ M.closure A) :
    ∃ D : Set α, M.IsHyperplaneCocircuit D ∧ τ ∈ D ∧ Disjoint D A ∧
      D.ncard - 1 = negativeTargetSupport M τ A hA hτ hneg := by
  have hnonempty : (negativeSupportCandidates M τ A).Nonempty := by
    obtain ⟨D, hD, hτD, hDA⟩ :=
      M.cocircuit_separates_closure_manuscript A τ
        (hA.trans Set.sdiff_subset) hτ hneg
    exact ⟨D.ncard - 1, D, hD, hτD, hDA, rfl⟩
  exact Nat.sInf_mem hnonempty

end Matroid
