import Matroid.RankClosure
import Matroid.Representation
import Matroid.Minors
import Matroid.Regular
import Mathlib.Combinatorics.Matroid.Loop

/-! Basic flat, contraction, and represented-flat interfaces at depth six. -/

open Set

universe u v w

namespace Matroid

variable {α : Type u} (M : Matroid α)

/-- N013: the manuscript's closure definition of a flat. -/
theorem isFlat_iff_closure_eq_manuscript (F : Set α) :
    M.IsFlat F ↔ M.closure F = F := M.isFlat_iff_closure_eq

/-- N013: every ground element outside a finite flat raises its rank. -/
theorem IsFlat.eRk_lt_eRk_insert [M.Finite] {F : Set α}
    (hF : M.IsFlat F) {e : α} (he : e ∈ M.E \ F) :
    M.eRk F < M.eRk (insert e F) := by
  have hnot : e ∉ M.closure F := by simpa [hF.closure] using he.2
  rw [M.eRk_insert_eq_add_one ⟨he.1, hnot⟩]
  exact (ENat.lt_add_one_iff
    (M.isRkFinite_of_finite (M.set_finite F hF.subset_ground)).eRk_lt_top.ne).2 le_rfl

/-- N013: the full finite flat/rank test, with ground membership explicit. -/
theorem isFlat_iff_forall_eRk_lt_insert [M.Finite] {F : Set α}
    (hFE : F ⊆ M.E) :
    M.IsFlat F ↔ ∀ e ∈ M.E \ F, M.eRk F < M.eRk (insert e F) := by
  constructor
  · intro hF e he
    exact IsFlat.eRk_lt_eRk_insert M hF he
  · intro h
    apply M.isFlat_iff_closure_eq.mpr
    apply subset_antisymm
    · intro e hecl
      by_contra heF
      have heE := M.mem_ground_of_mem_closure hecl
      have hr := h e ⟨heE, heF⟩
      exact hr.ne ((M.mem_closure_iff_eRk_insert_eq hFE heE).1 hecl).symm
    · exact M.subset_closure F

/-- N014: a flat containing an actual basis is the whole ground set. -/
theorem IsFlat.eq_ground_of_isBase_subset {F B : Set α}
    (hF : M.IsFlat F) (hB : M.IsBase B) (hBF : B ⊆ F) : F = M.E := by
  calc
    F = M.closure F := hF.closure.symm
    _ = M.E := hB.closure_of_superset hBF

/-- N017: a hyperplane is a maximal proper flat on the actual ground set. -/
def IsHyperplane (H : Set α) : Prop :=
  M.IsFlat H ∧ H ≠ M.E ∧
    ∀ F : Set α, M.IsFlat F → H ⊆ F → F = H ∨ F = M.E

/-- N030: contracting a set makes each surviving element it spans a loop. -/
theorem isLoop_contract_of_mem_closure {A : Set α} {e : α}
    (he : e ∈ M.closure A) (heA : e ∉ A) :
    (M ／ A).IsLoop e :=
  M.contract_isLoop_iff_mem_closure.mpr ⟨he, heA⟩

/-- N033: the finite-rank equation defining a modular pair of flats. -/
def IsModularPair [M.Finite] (F G : Set α) : Prop :=
  M.IsFlat F ∧ M.IsFlat G ∧
    (M.eRk F).toNat + (M.eRk G).toNat =
      (M.eRk (F ∩ G)).toNat + (M.eRk (M.closure (F ∪ G))).toNat

/-- N097: closure of a union is a flat containing both flats. -/
theorem flat_join_isFlat {F G : Set α} (_hF : M.IsFlat F) (_hG : M.IsFlat G) :
    M.IsFlat (M.closure (F ∪ G)) := M.isFlat_closure _

/-- N097: closure of a union is the least flat containing the two inputs. -/
theorem flat_join_least {F G H : Set α} (_hF : M.IsFlat F) (_hG : M.IsFlat G)
    (hH : M.IsFlat H) :
    F ⊆ H → G ⊆ H → M.closure (F ∪ G) ⊆ H := by
  intro hFH hGH
  rw [← hH.closure]
  exact M.closure_subset_closure (union_subset hFH hGH)

/-- N097: both flat inputs lie below their join. -/
theorem flat_join_upper {F G : Set α} (hF : M.IsFlat F) (hG : M.IsFlat G) :
    F ⊆ M.closure (F ∪ G) ∧ G ⊆ M.closure (F ∪ G) := by
  exact ⟨(subset_union_left).trans (M.subset_closure _),
    (subset_union_right).trans (M.subset_closure _)⟩

/-- N050: the zero set of a linear functional on an indexed representation
is a flat, including for the zero functional. -/
theorem Represents.isFlat_functional_zero
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [M.Finite] {φ : α → V} (hφ : M.Represents (K := K) φ)
    (ℓ : V →ₗ[K] K) :
    M.IsFlat {e ∈ M.E | ℓ (φ e) = 0} := by
  apply M.isFlat_iff_closure_eq.mpr
  apply Set.Subset.antisymm
  · intro e he
    have heE : e ∈ M.E := M.mem_ground_of_mem_closure he
    have hspan : φ e ∈ Submodule.span K
        (φ '' {x ∈ M.E | ℓ (φ x) = 0}) :=
      (hφ.mem_closure_iff_mem_span (by intro x hx; exact hx.1) heE).1 he
    have hker : Submodule.span K
        (φ '' {x ∈ M.E | ℓ (φ x) = 0}) ≤ LinearMap.ker ℓ := by
      apply Submodule.span_le.mpr
      rintro v ⟨x, hx, rfl⟩
      exact hx.2
    exact ⟨heE, hker hspan⟩
  · exact M.subset_closure _

/-- N054: deleting any set preserves representation over every field. -/
theorem Regular.delete [M.Finite] (hM : M.Regular.{u, v, w}) (D : Set α) :
    (M ＼ D).Regular.{u, v, w} := by
  intro K _
  obtain ⟨V, g, m, φ, hφ⟩ := hM K
  letI := g
  letI := m
  exact ⟨V, g, m, φ, hφ.delete D⟩

/-- N054: contraction preserves representation over every field, even
when the contracted columns are dependent. -/
theorem Regular.contract [M.Finite] (hM : M.Regular.{u, v, w})
    (C : Set α) (hC : C ⊆ M.E) :
    (M ／ C).Regular.{u, v, w} := by
  intro K _
  obtain ⟨V, g, m, φ, hφ⟩ := hM K
  letI := g
  letI := m
  let U := Submodule.span K (φ '' C)
  exact ⟨V ⧸ U, inferInstance, inferInstance,
    (fun e => Submodule.Quotient.mk (p := U) (φ e)), hφ.contract hC⟩

/-- N054 without a redundant assumption that the contraction set lies in
the ground set. -/
theorem Regular.contract_any [M.Finite] (hM : M.Regular.{u, v, w})
    (C : Set α) : (M ／ C).Regular.{u, v, w} := by
  rw [← M.contract_inter_ground_eq C]
  exact Regular.contract M hM (C ∩ M.E) inter_subset_right

end Matroid
