import Matroid.Representation
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Order.Lattice.Nat

/-! Minimum positive support equals minimum nonzero reconstruction support. -/

open Set

namespace Matroid

variable {α K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- N109: the least cardinality of a subset of available responses spanning
the target. The accepted-input hypothesis makes the defining set nonempty. -/
noncomputable def positiveSpanningSupport (M : Matroid α) (τ : α)
    (A : Set α) : ℕ :=
  sInf {n : ℕ | ∃ S : Set α, S ⊆ A ∧ τ ∈ M.closure S ∧ S.ncard = n}

/-- N109: the least number of nonzero coefficients in a reconstruction
using only available responses. -/
noncomputable def positiveReconstructionSupport (K : Type*) [Field K]
    [Module K V] (φ : α → V)
    (τ : α) (A : Set α) : ℕ :=
  sInf {n : ℕ | ∃ c : α →₀ K,
    (c.support : Set α) ⊆ A ∧
    Finsupp.linearCombination K φ c = φ τ ∧ c.support.card = n}

/-- N109: the two minima coincide for an accepted input. The finiteness
assumption and `τ ∉ A` retain the manuscript's response/target split. -/
theorem positiveSpanningSupport_eq_reconstruction
    {M : Matroid α} [M.Finite] {φ : α → V}
    (hφ : M.Represents (K := K) φ) {τ : α} {A : Set α}
    (hτ : τ ∈ M.E) (hA : A ⊆ M.E \ {τ})
    (hpos : τ ∈ M.closure A) :
    positiveSpanningSupport M τ A =
      positiveReconstructionSupport K φ τ A := by
  let S : Set ℕ := {n | ∃ B : Set α,
    B ⊆ A ∧ τ ∈ M.closure B ∧ B.ncard = n}
  let T : Set ℕ := {n | ∃ c : α →₀ K,
    (c.support : Set α) ⊆ A ∧
    Finsupp.linearCombination K φ c = φ τ ∧ c.support.card = n}
  have hAE : A ⊆ M.E := hA.trans Set.sdiff_subset
  have hS : S.Nonempty := ⟨A.ncard, A, Subset.rfl, hpos, rfl⟩
  have hspan : φ τ ∈ Submodule.span K (φ '' A) :=
    (hφ.mem_closure_iff_mem_span hAE hτ).1 hpos
  obtain ⟨c₀, hc₀, heq₀⟩ :=
    (Finsupp.mem_span_image_iff_linearCombination K).1 hspan
  have hc₀A : (c₀.support : Set α) ⊆ A :=
    (Finsupp.mem_supported K c₀).1 hc₀
  have hT : T.Nonempty := ⟨c₀.support.card, c₀, hc₀A, heq₀, rfl⟩
  change sInf S = sInf T
  rw [eq_comm]
  apply le_antisymm
  · obtain ⟨B, hBA, hτB, hnB⟩ := Nat.sInf_mem hS
    have hBE : B ⊆ M.E := hBA.trans hAE
    have hspanB : φ τ ∈ Submodule.span K (φ '' B) :=
      (hφ.mem_closure_iff_mem_span hBE hτ).1 hτB
    obtain ⟨c, hcB, hcEq⟩ :=
      (Finsupp.mem_span_image_iff_linearCombination K).1 hspanB
    have hcsub : (c.support : Set α) ⊆ B :=
      (Finsupp.mem_supported K c).1 hcB
    have hcA : (c.support : Set α) ⊆ A := hcsub.trans hBA
    have hcLe : c.support.card ≤ B.ncard := by
      simpa using Set.ncard_le_ncard hcsub
        (M.ground_finite.subset hBE)
    exact (Nat.sInf_le (show c.support.card ∈ T from
      ⟨c, hcA, hcEq, rfl⟩)).trans (hnB ▸ hcLe)
  · obtain ⟨c, hcA, hcEq, hnC⟩ := Nat.sInf_mem hT
    have hcE : (c.support : Set α) ⊆ M.E := hcA.trans hAE
    have hspanC : φ τ ∈ Submodule.span K (φ '' (c.support : Set α)) := by
      apply (Finsupp.mem_span_image_iff_linearCombination K).2
      exact ⟨c, Finsupp.mem_supported_support K c, hcEq⟩
    have hτC : τ ∈ M.closure (c.support : Set α) :=
      (hφ.mem_closure_iff_mem_span hcE hτ).2 hspanC
    have hmem : (c.support : Set α).ncard ∈ S :=
      ⟨(c.support : Set α), hcA, hτC, rfl⟩
    have hcard : (c.support : Set α).ncard = c.support.card := by simp
    exact (Nat.sInf_le hmem).trans (by rw [hcard, hnC])

end Matroid
