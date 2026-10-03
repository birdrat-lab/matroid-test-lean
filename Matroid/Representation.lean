import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Combinatorics.Matroid.Loop
import Mathlib.LinearAlgebra.LinearIndependent.Basic

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

/-- Manuscript: prose after `def:vector-matroid` (N046). Minimal dependence
is tested on element indices, including distinct equal or zero columns. -/
theorem vectorMatroid_isCircuit_iff {α K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (E : Set α) (hE : E.Finite) (φ : α → V) (C : Set α)
    (hC : C ⊆ E) :
    (vectorMatroid (K := K) E hE φ).IsCircuit C ↔
      Minimal (fun I : Set α =>
        ¬ LinearIndependent K (fun i : I => φ i.1)) C := by
  rw [Matroid.isCircuit_iff_minimal_not_indep (by simpa using hC)]
  simp only [minimal_iff_forall_ssubset]
  constructor
  · rintro ⟨hdep, hproper⟩
    refine ⟨?_, ?_⟩
    · simpa [vectorMatroid_indep_iff, hC] using hdep
    · intro I hIC
      have hIE : I ⊆ E := hIC.subset.trans hC
      simpa [vectorMatroid_indep_iff, hIE] using hproper hIC
  · rintro ⟨hdep, hproper⟩
    refine ⟨?_, ?_⟩
    · simpa [vectorMatroid_indep_iff, hC] using hdep
    · intro I hIC
      have hIE : I ⊆ E := hIC.subset.trans hC
      simpa [vectorMatroid_indep_iff, hIE] using hproper hIC

/-- Manuscript: `def:projective-equivalence` (N047). The linear isomorphism
acts only on column spans. Scalars are required to be nonzero only for
nonloop elements; representing loop columns are zero. -/
def ProjectivelyEquivalent {α K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (M : Matroid α) (φ : α → V) (ψ : α → W) : Prop :=
  Represents (K := K) M φ ∧ Represents (K := K) M ψ ∧
    ∃ T : Submodule.span K (φ '' M.E) ≃ₗ[K] Submodule.span K (ψ '' M.E),
      ∃ c : α → K,
        (∀ e ∈ M.E, ¬ M.IsLoop e → c e ≠ 0) ∧
        ∀ e (he : e ∈ M.E), ¬ M.IsLoop e →
          ψ e = c e • (T ⟨φ e, Submodule.subset_span ⟨e, he, rfl⟩⟩).1

/-- Manuscript `def:projective-equivalence` (N047): a represented loop has
zero column, so no scalar datum is needed for it. -/
theorem Represents.loop_column_eq_zero {α K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] {M : Matroid α} {φ : α → V}
    (hφ : Represents (K := K) M φ) {e : α} (he : M.IsLoop e) :
    φ e = 0 := by
  have hground : e ∈ M.E := he.mem_ground
  have hnot := (M.singleton_not_indep hground).2 he
  by_contra hne
  apply hnot
  exact (hφ {e} (Set.singleton_subset_iff.mpr hground)).2
    ((linearIndepOn_singleton_iff K).2 hne)

/-- Manuscript ledger N111; used in `prop:representation-scaling`. Independent
nonzero column scalings preserve the indexed vector matroid. -/
theorem vectorMatroid_smul_eq {α K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (E : Set α) (hE : E.Finite) (φ : α → V)
    (c : α → K) (hc : ∀ e ∈ E, c e ≠ 0) :
    vectorMatroid (K := K) E hE (fun e => c e • φ e) =
      vectorMatroid (K := K) E hE φ := by
  refine Matroid.ext_indep (by simp) (fun I hI => ?_)
  change I ⊆ E at hI
  simp only [vectorMatroid_indep_iff, hI, true_and]
  let u : I → Kˣ := fun i => Units.mk0 (c i.1) (hc i.1 (hI i.2))
  simpa only [u, Pi.smul_def', Units.smul_def, Units.val_mk0] using
    (LinearIndependent.units_smul_iff (fun i : I => φ i.1) u)

/-- Manuscript ledger N112; used in `prop:representation-coordinate-invariance`.
An ambient linear equivalence preserves indexed vector-matroid independence. -/
theorem vectorMatroid_map_linearEquiv_eq {α K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (E : Set α) (hE : E.Finite) (φ : α → V) (T : V ≃ₗ[K] W) :
    vectorMatroid (K := K) E hE (T ∘ φ) =
      vectorMatroid (K := K) E hE φ := by
  refine Matroid.ext_indep (by simp) (fun I hI => ?_)
  change I ⊆ E at hI
  simp only [vectorMatroid_indep_iff, hI, true_and]
  exact T.toLinearMap.linearIndependent_iff
    (LinearMap.ker_eq_bot.mpr T.injective)

end Matroid
