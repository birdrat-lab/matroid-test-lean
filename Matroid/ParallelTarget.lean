import Matroid.TwoSumProper
import Mathlib.Combinatorics.Matroid.Map

/-! The parallel-target construction in the manuscript's second R10 program. -/

namespace Matroid

universe u w

/-- Add a fresh target label whose column is parallel to the old target.
The old copy `Sum.inl τ` remains available as the later glue port. -/
def parallelTargetCopy {α : Type*} (M : Matroid α) (τ : α) :
    Matroid (α ⊕ Unit) :=
  M.comap (fun x => x.elim id (fun _ => τ))

@[simp] theorem parallelTargetCopy_old_mem_ground {α : Type*}
    (M : Matroid α) (τ e : α) :
    Sum.inl e ∈ (parallelTargetCopy M τ).E ↔ e ∈ M.E := by
  rfl

@[simp] theorem parallelTargetCopy_new_mem_ground {α : Type*}
    (M : Matroid α) (τ : α) :
    Sum.inr () ∈ (parallelTargetCopy M τ).E ↔ τ ∈ M.E := by
  rfl

/-- The two target labels form a genuine parallel pair whenever the old
target is a nonloop. -/
theorem parallelTargetCopy_target_pair_isCircuit {α : Type*}
    (M : Matroid α) (τ : α) (hτ : M.IsNonloop τ) :
    (parallelTargetCopy M τ).IsCircuit
      ({Sum.inl τ, Sum.inr ()} : Set (α ⊕ Unit)) := by
  let f : α ⊕ Unit → α := fun x => x.elim id (fun _ => τ)
  have hground : ({Sum.inl τ, Sum.inr ()} : Set (α ⊕ Unit)) ⊆
      (parallelTargetCopy M τ).E := by
    intro x hx
    rcases hx with rfl | rfl
    · exact parallelTargetCopy_old_mem_ground M τ τ |>.mpr hτ.mem_ground
    · exact parallelTargetCopy_new_mem_ground M τ |>.mpr hτ.mem_ground
  apply (Matroid.isCircuit_iff_dep_forall_sdiff_singleton_indep).2
  constructor
  · apply (Matroid.not_indep_iff hground).1
    intro hI
    have hinj : Set.InjOn f ({Sum.inl τ, Sum.inr ()} : Set (α ⊕ Unit)) :=
      (Matroid.comap_indep_iff.mp hI).2
    have heq : (Sum.inl τ : α ⊕ Unit) = Sum.inr () :=
      hinj (by simp) (by simp) (by rfl)
    cases heq
  · intro x hx
    rcases hx with rfl | rfl
    · have hsingle : (parallelTargetCopy M τ).Indep
          ({Sum.inr ()} : Set (α ⊕ Unit)) := by
        apply (Matroid.comap_indep_iff).2
        constructor
        · simpa [parallelTargetCopy, f] using hτ.indep
        · simp
      simpa using hsingle
    · have hsingle : (parallelTargetCopy M τ).Indep
          ({Sum.inl τ} : Set (α ⊕ Unit)) := by
        apply (Matroid.comap_indep_iff).2
        constructor
        · simpa [parallelTargetCopy, f] using hτ.indep
        · simp
      simpa using hsingle

/-- A finite original matroid has a finite one-label parallel extension. -/
instance parallelTargetCopy_finite {α : Type*}
    (M : Matroid α) [M.Finite] (τ : α) :
    (parallelTargetCopy M τ).Finite := by
  refine ⟨(Set.finite_preimage_inl_and_inr).mp ⟨?_, ?_⟩⟩
  · change M.E.Finite
    exact M.ground_finite
  · exact Set.toFinite _

/-- N204: the second program adjoins a fresh parallel target to the first
pointed component, glues the old target to a second component by a proper
two-sum, and keeps the fresh label as target. The second component must omit
that fresh label. This is a construction predicate; regularity and target
closure are separate later requirements. -/
def IsParallelTargetConstruction {α : Type*}
    (M : Matroid α) (τ : α) (N P : Matroid (α ⊕ Unit)) : Prop :=
  IsProperTwoSum (parallelTargetCopy M τ) N P (Sum.inl τ) ∧
  Sum.inr () ∉ N.E

/-- The fresh target survives the proper gluing on its original new label. -/
theorem IsParallelTargetConstruction.new_target_mem_ground
    {α : Type*} {M : Matroid α} {τ : α}
    {N P : Matroid (α ⊕ Unit)}
    (h : IsParallelTargetConstruction M τ N P)
    (hτ : τ ∈ M.E) : Sum.inr () ∈ P.E := by
  have hground := h.1.2.2.2.2.2.2.2.1
  rw [hground]
  apply Set.mem_symmDiff.mpr
  exact Or.inl ⟨parallelTargetCopy_new_mem_ground M τ |>.mpr hτ, h.2⟩

/-- The N065 constructor realizes the parallel-target specification once
the two finite regular factors satisfy the proper-glue conditions. -/
theorem exists_parallelTargetConstruction {α : Type u}
    (M : Matroid α) [M.Finite] (τ : α) (N : Matroid (α ⊕ Unit)) [N.Finite]
    (hE : Regular.{u, 0, w} (parallelTargetCopy M τ))
    (hN : Regular.{u, 0, w} N)
    (hinter : (parallelTargetCopy M τ).E ∩ N.E = {Sum.inl τ})
    (hlE : ¬ (parallelTargetCopy M τ).IsLoop (Sum.inl τ))
    (hlN : ¬ N.IsLoop (Sum.inl τ))
    (hcE : ¬ (parallelTargetCopy M τ).IsColoop (Sum.inl τ))
    (hcN : ¬ N.IsColoop (Sum.inl τ))
    (hnE : 3 ≤ (parallelTargetCopy M τ).E.ncard)
    (hnN : 3 ≤ N.E.ncard)
    (hnew : Sum.inr () ∉ N.E) :
    ∃ P : Matroid (α ⊕ Unit), IsParallelTargetConstruction M τ N P := by
  let E := parallelTargetCopy M τ
  exact ⟨regularTwoSum E N hE hN (Sum.inl τ) hinter
    hlE hlN hcE hcN hnE hnN,
    isProperTwoSum_regularTwoSum hE hN (Sum.inl τ) hinter
      hlE hlN hcE hcN hnE hnN,
    hnew⟩

end Matroid
