import Matroid.RankClosure
import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Order.Lattice.Nat

/-! # Pointed -/

open Set

namespace Matroid

/-- Manuscript: port discussion preceding `def:target-query-matroid` and
`prop:minimal-query-circuits` (N081). A minimal set spanning the distinguished
element is exactly the non-target part of a circuit through it. -/
theorem minimal_spanning_iff_circuit {α : Type*} {M : Matroid α}
    {τ : α} {S : Set α} [M.Finite] (hS : S ⊆ M.E) (hτS : τ ∉ S) :
    (τ ∈ M.closure S ∧ ∀ T : Set α, T ⊂ S → τ ∉ M.closure T) ↔
      M.IsCircuit (insert τ S) := by
  constructor
  · rintro ⟨hcl, hmin⟩
    obtain ⟨C, hC, hτC, hCsub⟩ :=
      (M.mem_closure_iff_exists_circuit_sdiff hS hτS).mp hcl
    have hDcl : τ ∈ M.closure (C \ {τ}) :=
      hC.mem_closure_sdiff_singleton_of_mem hτC
    have hDS : C \ {τ} = S := by
      by_contra hne
      exact hmin _ (Set.ssubset_iff_subset_ne.mpr ⟨hCsub, hne⟩) hDcl
    have hCS : C = insert τ S := by
      rw [← hDS, insert_sdiff_singleton, insert_eq_of_mem hτC]
    rwa [← hCS]
  · intro hC
    have hτC : τ ∈ (insert τ S : Set α) := mem_insert τ S
    have hcl : τ ∈ M.closure S := by
      have h := hC.mem_closure_sdiff_singleton_of_mem hτC
      simpa [hτS] using h
    refine ⟨hcl, ?_⟩
    intro T hTS hclT
    have hτT : τ ∉ T := fun h => hτS (hTS.subset h)
    obtain ⟨C, hC', hτC', hDsub⟩ :=
      (M.mem_closure_iff_exists_circuit_sdiff (hTS.subset.trans hS) hτT).mp hclT
    have hCsub : C ⊆ insert τ S := by
      intro x hx
      by_cases hxτ : x = τ
      · exact hxτ ▸ mem_insert τ S
      · exact mem_insert_of_mem τ (hTS.subset (hDsub ⟨hx, by simpa using hxτ⟩))
    have hCeq : C = insert τ S := hC'.eq_of_subset_isCircuit hC hCsub
    have hST : S ⊆ T := by
      intro x hxS
      apply hDsub
      rw [hCeq]
      exact ⟨mem_insert_of_mem τ hxS, by
        intro hxτ
        exact hτS (hxτ ▸ hxS)⟩
    exact hTS.not_subset hST

/-- Manuscript: `def:positive-support` (N105), matroid-side content. The
spanning hypothesis makes the set of candidate cardinalities nonempty. -/
noncomputable def positiveTargetSupport {α : Type*} (M : Matroid α)
    [M.Finite] (τ : α) (A : Set α) (_hA : A ⊆ M.E)
    (_hspan : τ ∈ M.closure A) : ℕ :=
  sInf {n : ℕ | ∃ S : Set α, S ⊆ A ∧ τ ∈ M.closure S ∧ S.ncard = n}

end Matroid
