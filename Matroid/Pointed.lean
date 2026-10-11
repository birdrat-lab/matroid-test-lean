import Matroid.RankClosure
import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Order.Lattice.Nat
import Mathlib.Combinatorics.Matroid.Loop
import Matroid.WeightedBases

/-! # Pointed -/

open Set

namespace Matroid

/-- Manuscript `prop:seymour-two-sum-input-minors` (N143): when the
available elements do not span the target, the target is a coloop of
their restriction together with the target. -/
theorem nonspanned_target_isColoop_restrict {α : Type*} (M : Matroid α)
    (A : Set α) (τ : α) (hA : A ⊆ M.E \ {τ}) (hτ : τ ∈ M.E)
    (hnot : τ ∉ M.closure A) :
    (M ↾ (A ∪ {τ})).IsColoop τ := by
  have hτA : τ ∉ A := fun h => (hA h).2 (by simp)
  have hR : A ∪ {τ} ⊆ M.E :=
    Set.union_subset (hA.trans Set.sdiff_subset) (Set.singleton_subset_iff.mpr hτ)
  rw [Matroid.restrict_isColoop_iff hR]
  have hdiff : (A ∪ {τ}) \ {τ} = A := by
    ext x
    constructor
    · rintro ⟨hx, hn⟩
      rcases hx with hx | hx
      · exact hx
      · exact False.elim (hn hx)
    · intro hx
      refine ⟨Or.inl hx, ?_⟩
      intro he
      have heq : x = τ := Set.mem_singleton_iff.mp he
      exact hτA (heq ▸ hx)
  rw [hdiff]
  exact ⟨hnot, Set.mem_union_right A (Set.mem_singleton τ)⟩

/-- The exact nonspanning/coloop equivalence in the positive restriction
used by `prop:seymour-two-sum-input-minors` (N143). -/
theorem nonspanned_target_iff_isColoop_restrict {α : Type*} (M : Matroid α)
    (A : Set α) (τ : α) (hA : A ⊆ M.E \ {τ}) (hτ : τ ∈ M.E) :
    τ ∉ M.closure A ↔ (M ↾ (A ∪ {τ})).IsColoop τ := by
  constructor
  · exact M.nonspanned_target_isColoop_restrict A τ hA hτ
  · intro hcol
    have hR : A ∪ {τ} ⊆ M.E :=
      Set.union_subset (hA.trans Set.sdiff_subset) (Set.singleton_subset_iff.mpr hτ)
    have hn := (Matroid.restrict_isColoop_iff hR).1 hcol |>.1
    have hsub : A ⊆ (A ∪ {τ}) \ {τ} := by
      intro x hx
      refine ⟨Or.inl hx, ?_⟩
      intro he
      exact (hA hx).2 he
    exact fun hcl => hn (M.closure_subset_closure hsub hcl)

/-- The zero case of N143: the restriction has no target-omitting basis,
so its corresponding weighted sum is zero for every weight assignment. -/
theorem nonspanned_target_weightedBasesOut_eq_zero {α R : Type*}
    [CommSemiring R] {M : Matroid α} [M.Finite]
    (A : Set α) (τ : α) (hA : A ⊆ M.E \ {τ}) (hτ : τ ∈ M.E)
    (hnot : τ ∉ M.closure A) (w : α → R) :
    weightedBasesOut (M ↾ (A ∪ {τ}))
      (M.ground_finite.subset
        (Set.union_subset (hA.trans Set.sdiff_subset)
          (Set.singleton_subset_iff.mpr hτ))) τ w = 0 := by
  exact weightedBasesOut_eq_zero_of_isColoop _ _ τ w
    (M.nonspanned_target_isColoop_restrict A τ hA hτ hnot)

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

/-- Manuscript: `def:positive-support` (N105), matroid-side content. Available
elements exclude the target, and the spanning hypothesis makes the set of
candidate cardinalities nonempty. -/
noncomputable def positiveTargetSupport {α : Type*} (M : Matroid α)
    [M.Finite] (τ : α) (A : Set α) (_hA : A ⊆ M.E \ {τ})
    (_hspan : τ ∈ M.closure A) : ℕ :=
  sInf {n : ℕ | ∃ S : Set α, S ⊆ A ∧ τ ∈ M.closure S ∧ S.ncard = n}

end Matroid
