import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Combinatorics.Matroid.IndepAxioms

/-! # Representation -/

open Set

namespace Matroid

/-- Manuscript: `def:matroid-representability` (N042). The elements remain
indexed even when two elements have equal vectors. -/
def Represents {α K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (M : Matroid α) (φ : α → V) : Prop :=
  ∀ I : Set α, I ⊆ M.E →
    (M.Indep I ↔ LinearIndependent K (fun i : I => φ i.1))

/-- Manuscript: `def:matroid-representability` (N042). -/
def RepresentableOver.{u,v,w} {α : Type u} (K : Type v) [Field K]
    (M : Matroid α) : Prop :=
  ∃ (V : Type w) (g : AddCommGroup V) (m : Module K V),
    letI := g
    letI := m
    ∃ φ : α → V, Represents (K := K) M φ

private theorem ncard_le_of_linearIndepOn_of_image_subset_span
    {α K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {φ : α → V} {I J : Set α} (hI : I.Finite) (hJ : J.Finite)
    (hJli : LinearIndepOn K φ J)
    (hspan : φ '' J ⊆ Submodule.span K (φ '' I)) : J.ncard ≤ I.ncard := by
  letI := hI.fintype
  letI := hJ.fintype
  have hrangeI : Set.range (fun i : I => φ i.1) = φ '' I := by
    ext v
    simp
  have hrangeJ : Set.range (fun j : J => φ j.1) = φ '' J := by
    ext v
    simp
  have hle : Submodule.span K (φ '' J) ≤ Submodule.span K (φ '' I) :=
    Submodule.span_le.mpr hspan
  letI : Module.Finite K (Submodule.span K (φ '' I)) :=
    Module.Finite.span_of_finite K (hI.image φ)
  calc
    J.ncard = Module.finrank K (Submodule.span K (φ '' J)) := by
      rw [← Set.fintypeCard_eq_ncard]
      have h := (finrank_span_eq_card hJli).symm
      rw [hrangeJ] at h
      exact h
    _ ≤ Module.finrank K (Submodule.span K (φ '' I)) :=
      Submodule.finrank_mono hle
    _ ≤ I.ncard := by
      rw [← Set.fintypeCard_eq_ncard]
      have h := finrank_range_le_card (R := K) (fun i : I => φ i.1)
      rw [hrangeI] at h
      exact h

/-- Manuscript: `def:vector-matroid` (N043). The index set is the finite
ground set, so equal or zero vectors retain their separate element labels. -/
noncomputable def vectorMatroid {α K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (E : Set α) (hE : E.Finite) (φ : α → V) : Matroid α :=
  (IndepMatroid.ofFinite hE
    (fun I : Set α => I ⊆ E ∧ LinearIndepOn K φ I)
    (by simp)
    (by
      intro I J hJ hIJ
      exact ⟨hIJ.trans hJ.1, hJ.2.mono hIJ⟩)
    (by
      intro I J hI hJ hcard
      by_contra hn
      have hspan : φ '' J ⊆ Submodule.span K (φ '' I) := by
        rintro v ⟨j, hjJ, rfl⟩
        by_cases hjI : j ∈ I
        · exact Submodule.subset_span ⟨j, hjI, rfl⟩
        · by_contra hjspan
          have hLI : LinearIndepOn K φ (insert j I) := hI.2.insert hjspan
          exact hn ⟨j, hjJ, hjI, ⟨insert_subset (hJ.1 hjJ) hI.1, hLI⟩⟩
      exact (ncard_le_of_linearIndepOn_of_image_subset_span
        (hE.subset hI.1) (hE.subset hJ.1) hJ.2 hspan).not_gt hcard)
    (fun _ hI => hI.1)).matroid

/-- Manuscript: `def:vector-matroid` (N043). This is its exact indexed
independence predicate. -/
theorem vectorMatroid_indep_iff {α K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (E : Set α) (hE : E.Finite) (φ : α → V) (I : Set α) :
    (vectorMatroid (K := K) E hE φ).Indep I ↔
      I ⊆ E ∧ LinearIndependent K (fun i : I => φ i.1) := by
  rfl

/-- Manuscript: `def:vector-matroid` (N043). -/
@[simp] theorem vectorMatroid_ground {α K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (E : Set α) (hE : E.Finite) (φ : α → V) :
    (vectorMatroid (K := K) E hE φ).E = E := rfl

/-- Manuscript: `def:vector-matroid` (N043). -/
instance vectorMatroid_finite {α K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (E : Set α) (hE : E.Finite) (φ : α → V) :
    (vectorMatroid (K := K) E hE φ).Finite := by
  unfold vectorMatroid
  infer_instance

/-- Manuscript: `def:vector-matroid` and `def:matroid-representability`
(N043, N042). The generating family represents its vector matroid. -/
theorem vectorMatroid_represents {α K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (E : Set α) (hE : E.Finite) (φ : α → V) :
    Represents (K := K) (vectorMatroid (K := K) E hE φ) φ := by
  intro I hI
  change I ⊆ E at hI
  simp [vectorMatroid_indep_iff, hI]

end Matroid
