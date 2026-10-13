import Matroid.TotallyUnimodular
import Matroid.Regular
import Mathlib.Algebra.Field.ZMod
import Matroid.External.TutteRegularTU

/-! # Exact labeled target for Tutte's regular-to-TU converse

Oxley's Lemma 4.4 gives the mathematical converse for finite matroids.
The ground-indexed converse is the cited premise in
`Matroid.External.TutteRegularTU`; the ambient-label transport is proved here.
-/

namespace Matroid

universe u v

/-- A finite real TU matrix whose columns retain the original element labels.
The row type is finite; columns outside `M.E` are harmless because the vector
matroid restricts to `M.E`. -/
def HasLabeledRealTU {α : Type u} (M : Matroid α) [M.Finite] : Prop :=
  ∃ (r : Type) (_ : Fintype r) (A : Matrix r α ℝ),
    A.IsTotallyUnimodular ∧
      M = vectorMatroid (K := ℝ) M.E M.ground_finite A.col

/-- The already proved easy direction of Tutte's characterization, with the
same indexed columns over every field. -/
theorem HasLabeledRealTU.regular {α : Type u} {M : Matroid α}
    [M.Finite] (hM : HasLabeledRealTU M) : Regular.{u,v,v} M := by
  classical
  obtain ⟨r, hr, A, hTU, hEq⟩ := hM
  letI : Fintype r := hr
  intro K _
  obtain ⟨B, _, _, hCast⟩ :=
    vectorMatroid_realTU_represents_over_field (K := K) A hTU M.E M.ground_finite
  refine ⟨r → K, inferInstance, inferInstance,
    (B.map fun z : ℤ => (z : K)).col, ?_⟩
  rw [hEq, hCast]
  exact vectorMatroid_represents M.E M.ground_finite _

/-- What regularity directly supplies before the unproved TU normalization.
The arbitrary coordinate space and indexed element map are explicit. -/
theorem Regular.exists_real_representation {α : Type u} {M : Matroid α}
    (hM : Regular.{u,0,0} M) :
    ∃ (V : Type) (g : AddCommGroup V) (m : Module ℝ V),
      letI := g
      letI := m
      ∃ φ : α → V, M.Represents (K := ℝ) φ :=
  hM ℝ

/-- Any representation of a finite matroid can be converted into finitely
many coordinates while preserving every original element label. -/
theorem RepresentableOver.exists_labeled_matrix {α : Type u} {K : Type}
    [Field K] {M : Matroid α} [M.Finite]
    (hM : RepresentableOver.{u,0,0} K M) :
    ∃ (r : Type) (_ : Fintype r) (A : Matrix r α K),
      M = vectorMatroid (K := K) M.E M.ground_finite A.col := by
  classical
  obtain ⟨V, g, m, φ, hφ⟩ := hM
  letI : AddCommGroup V := g
  letI : Module K V := m
  let S : Submodule K V := Submodule.span K (φ '' M.E)
  letI : FiniteDimensional K S :=
    FiniteDimensional.span_of_finite K (M.ground_finite.image φ)
  let b := Module.Basis.ofVectorSpace K S
  let r := Module.Basis.ofVectorSpaceIndex K S
  letI : Fintype r := inferInstance
  let T : S ≃ₗ[K] (r → K) :=
    b.repr.trans (Finsupp.linearEquivFunOnFinite K K r)
  let ψ : α → r → K := fun e =>
    if he : e ∈ M.E then T ⟨φ e, Submodule.subset_span ⟨e, he, rfl⟩⟩ else 0
  let A : Matrix r α K := fun i e => ψ e i
  refine ⟨r, inferInstance, A, ?_⟩
  apply Matroid.ext_indep (by simp)
  intro I hI
  rw [vectorMatroid_indep_iff]
  simp only [hI, true_and]
  rw [hφ I hI]
  change LinearIndependent K (fun i : I => φ i.1) ↔
    LinearIndependent K (fun i : I => ψ i.1)
  let vS : I → S := fun i => ⟨φ i.1,
    Submodule.subset_span ⟨i.1, hI i.2, rfl⟩⟩
  have hφS : LinearIndependent K (fun i : I => φ i.1) ↔
      LinearIndependent K vS := by
    change LinearIndependent K ((Submodule.subtype S) ∘ vS) ↔ _
    exact (Submodule.subtype S).linearIndependent_iff_of_injOn
      (Submodule.subtype_injective S).injOn
  rw [hφS]
  have hψ : (fun i : I => ψ i.1) = (fun i : I => T (vS i)) := by
    funext i
    simp [ψ, vS, hI i.2]
  rw [hψ]
  exact (T.toLinearMap.linearIndependent_iff_of_injOn T.injective.injOn).symm

/-- A finite regular matroid has a labeled real matrix. The remaining Tutte
converse asks for a choice of coordinates making this matrix TU. -/
theorem Regular.exists_labeled_real_matrix {α : Type u} {M : Matroid α}
    [M.Finite] (hM : Regular.{u,0,0} M) :
    ∃ (r : Type) (_ : Fintype r) (A : Matrix r α ℝ),
      M = vectorMatroid (K := ℝ) M.E M.ground_finite A.col :=
  (hM ℝ).exists_labeled_matrix

/-- The second normalization route supplies labeled binary and ternary
matrices. A compatible sign assignment between these and the real matrix is
the still-open part of the regular-to-TU converse. -/
theorem Regular.exists_labeled_binary_ternary_matrices
    {α : Type u} {M : Matroid α} [M.Finite]
    (hM : Regular.{u,0,0} M) :
    (∃ (r : Type) (_ : Fintype r) (A : Matrix r α (ZMod 2)),
      M = vectorMatroid (K := ZMod 2) M.E M.ground_finite A.col) ∧
    (∃ (r : Type) (_ : Fintype r) (A : Matrix r α (ZMod 3)),
      M = vectorMatroid (K := ZMod 3) M.E M.ground_finite A.col) :=
  ⟨(hM (ZMod 2)).exists_labeled_matrix,
   (hM (ZMod 3)).exists_labeled_matrix⟩

/-- Transport the cited ground-indexed TU matrix to the ambient label type
by adding zero columns outside the finite ground set. -/
theorem Regular.hasLabeledRealTU {α : Type u} {M : Matroid α}
    [M.Finite] (hM : Regular.{u,0,0} M) : HasLabeledRealTU M := by
  classical
  obtain ⟨r, hr, A, hTU, hRep⟩ :=
    External.regular_ground_exists_realTU hM
  letI : Fintype r := hr
  let B : Matrix r (M.E ⊕ (M.Eᶜ : Set α)) ℝ :=
    Matrix.fromCols A (Matrix.replicateCol (M.Eᶜ : Set α) 0)
  let e : M.E ⊕ (M.Eᶜ : Set α) ≃ α := Equiv.Set.sumCompl M.E
  let Aext : Matrix r α ℝ := B.reindex (Equiv.refl r) e
  have hB : B.IsTotallyUnimodular :=
    (Matrix.fromCols_replicateCol0_isTotallyUnimodular_iff A).2 hTU
  have hAext : Aext.IsTotallyUnimodular :=
    (Matrix.reindex_isTotallyUnimodular B (Equiv.refl r) e).2 hB
  refine ⟨r, hr, Aext, hAext, ?_⟩
  apply Matroid.ext_indep (by simp)
  intro I hI
  rw [vectorMatroid_indep_iff]
  simp only [hI, true_and]
  let J : Set M.E := {j | j.1 ∈ I}
  have hJimage : Subtype.val '' J = I := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact hj
    · intro hx
      exact ⟨⟨x, hI hx⟩, hx, rfl⟩
  have hLI := hRep J
  rw [hJimage] at hLI
  rw [hLI]
  let q : J ≃ I := {
    toFun := fun j => ⟨j.1.1, j.2⟩
    invFun := fun i => ⟨⟨i.1, hI i.2⟩, i.2⟩
    left_inv := by intro j; rfl
    right_inv := by intro i; rfl }
  have hcol (i : I) : Aext.col i.1 = A.col ⟨i.1, hI i.2⟩ := by
    funext j
    change B j (e.symm i.1) = A j ⟨i.1, hI i.2⟩
    rw [Equiv.Set.sumCompl_symm_apply_of_mem (hI i.2)]
    rfl
  have hfun : (fun i : I => Aext.col i.1) ∘ q =
      (fun j : J => A.col j.1) := by
    funext j
    simpa [q] using hcol (q j)
  exact linearIndependent_equiv' q hfun

end Matroid
