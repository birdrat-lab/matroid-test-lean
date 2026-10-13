import Matroid.Depth6Quotient
import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.LinearAlgebra.Finsupp.Supported

/-! Fundamental circuits of labeled free-relation presentations. -/

open Set

namespace Matroid

variable {K : Type*} [Field K] {β ρ : Type*} [Fintype β] [Fintype ρ]

/-- The relation label is spanned by a set of free generators precisely when
all its nonzero coordinates lie in that set. -/
theorem freeRelation_mem_closure_iff_support_subset
    (r : ρ → β →₀ K) (x : ρ) (S : Set β) :
    Sum.inr x ∈ (freeRelationMatroid r).closure (Sum.inl '' S) ↔
      ↑(r x).support ⊆ S := by
  have hrep := vectorMatroid_represents (K := K) Set.univ Set.finite_univ
    (freeRelationVector r)
  rw [freeRelationMatroid, hrep.mem_closure_iff_mem_span
    (by intro y hy; simp) (by simp)]
  have himage : freeRelationVector r '' (Sum.inl '' S) =
      (fun b : β => Finsupp.single b (1 : K)) '' S := by
    ext v
    simp [freeRelationVector]
  rw [himage]
  rw [← Finsupp.supported_eq_span_single, Finsupp.mem_supported]
  rfl

/-- A relation's fundamental circuit against the free coordinate basis is
exactly its label together with its nonzero coordinate labels. -/
theorem freeRelation_fundCircuit_eq_support
    (r : ρ → β →₀ K) (x : ρ) :
    (freeRelationMatroid r).fundCircuit (Sum.inr x) (Set.range Sum.inl) =
      insert (Sum.inr x) (Sum.inl '' (r x).support) := by
  let M := freeRelationMatroid r
  let B : Set (β ⊕ ρ) := Set.range Sum.inl
  have hB : M.IsBase B := freeRelation_generators_isBase r
  have hxE : Sum.inr x ∈ M.E := by simp [M, freeRelationMatroid]
  have hxcl : Sum.inr x ∈ M.closure B := by
    rw [hB.closure_eq]
    exact hxE
  have hxB : Sum.inr x ∉ B := by simp [B]
  ext y
  cases y with
  | inr z =>
      change Sum.inr z ∈ M.fundCircuit (Sum.inr x) B ↔
        Sum.inr z ∈ insert (Sum.inr x) (Sum.inl '' ((r x).support : Set β))
      by_cases h : z = x
      · subst z
        simp [M.mem_fundCircuit]
      · have hnot : Sum.inr z ∉ M.fundCircuit (Sum.inr x) B := by
          intro hy
          have hs := M.fundCircuit_subset_insert (Sum.inr x) B hy
          simp [B, h] at hs
        simp [hnot, h]
  | inl b =>
      let S : Set β := {b}ᶜ
      have hIeq : B \ {Sum.inl b} = Sum.inl '' S := by
        ext y
        cases y with
        | inl c => simp [B, S]
        | inr z => simp [B, S]
      have hI : M.Indep (Sum.inl '' S) := by
        rw [← hIeq]
        exact hB.indep.sdiff _
      have hnot : Sum.inr x ∉ Sum.inl '' S := by simp
      rw [hB.indep.mem_fundCircuit_iff hxcl hxB]
      rw [← Set.insert_sdiff_singleton_comm (by simp : Sum.inr x ≠ Sum.inl b), hIeq]
      rw [hI.insert_indep_iff_of_notMem hnot]
      rw [Set.mem_sdiff, and_iff_right hxE,
        freeRelation_mem_closure_iff_support_subset]
      simp [S]

/-- N244: for a positive relation `t - v`, the fundamental circuit contains
the relation label, the target, and exactly the nonzero response coordinates.
The target coordinate of `v` is zero, as in the manuscript's response vector. -/
theorem positiveRelation_fundCircuit
    (r v : ρ → β →₀ K) (τ : β) (x : ρ)
    (hr : r x = Finsupp.single τ 1 - v x)
    (hvτ : v x τ = 0) :
    (freeRelationMatroid r).fundCircuit (Sum.inr x) (Set.range Sum.inl) =
      insert (Sum.inr x)
        (insert (Sum.inl τ) (Sum.inl '' ((v x).support : Set β))) := by
  have hsupp : ((r x).support : Set β) =
      insert τ ((v x).support : Set β) := by
    ext b
    by_cases hb : b = τ
    · subst b
      simp [hr, hvτ, Finsupp.mem_support_iff]
    · simp [hr, hb, Finsupp.mem_support_iff, Finsupp.sub_apply]
  rw [freeRelation_fundCircuit_eq_support, hsupp, Set.image_insert_eq]

/-- The displayed support is an actual circuit, including when some
response coefficients vanish. -/
theorem positiveRelation_fundCircuit_isCircuit
    (r v : ρ → β →₀ K) (τ : β) (x : ρ)
    (hr : r x = Finsupp.single τ 1 - v x)
    (hvτ : v x τ = 0) :
    (freeRelationMatroid r).IsCircuit
      (insert (Sum.inr x)
        (insert (Sum.inl τ) (Sum.inl '' ((v x).support : Set β)))) := by
  rw [← positiveRelation_fundCircuit r v τ x hr hvτ]
  exact (freeRelation_generators_isBase r).fundCircuit_isCircuit
    (by simp [freeRelationMatroid]) (by simp)

end Matroid
