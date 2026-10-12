import Matroid.Uniform
import Matroid.TotallyUnimodular
import Matroid.Regular

/-! The one-row totally unimodular representation of rank-one uniform matroids. -/

namespace Matroid

universe u v

/-- N257: the all-ones integer row on arbitrary finite column labels. -/
def oneRowOnes (α : Type*) : Matrix (Fin 1) α ℤ := fun _ _ => 1

/-- Every square minor of a one-row all-ones matrix has order zero or one. -/
theorem oneRowOnes_isTotallyUnimodular (α : Type*) :
    (oneRowOnes α).IsTotallyUnimodular := by
  intro k f g hf hg
  have hk : k ≤ 1 := by
    simpa using Fintype.card_le_of_injective f hf
  interval_cases k
  · exact ⟨1, by simp [oneRowOnes]⟩
  · exact ⟨1, by simp [oneRowOnes, Matrix.det_fin_one]⟩

/-- The same all-ones row over the reals has a TU certificate. -/
def oneRowOnesReal (α : Type*) : Matrix (Fin 1) α ℝ := fun _ _ => 1

theorem oneRowOnesReal_isTotallyUnimodular (α : Type*) :
    (oneRowOnesReal α).IsTotallyUnimodular := by
  intro k f g hf hg
  have hk : k ≤ 1 := by
    simpa using Fintype.card_le_of_injective f hf
  interval_cases k
  · exact ⟨1, by simp⟩
  · exact ⟨1, by simp [oneRowOnesReal]⟩

/-- An indexed constant nonzero column family is independent exactly when
the index set has at most one element. -/
theorem oneRowOnesReal_linearIndependent_iff {α : Type*}
    (I : Set α) [Finite I] :
    LinearIndependent ℝ (fun i : I => (oneRowOnesReal α).col i.1) ↔
      I.ncard ≤ 1 := by
  constructor
  · intro hli
    rw [Set.ncard_le_one_iff_subsingleton]
    intro x hx y hy
    have heq : (⟨x, hx⟩ : I) = ⟨y, hy⟩ :=
      hli.injective (by funext j; rfl)
    exact congrArg Subtype.val heq
  · intro hcard
    have hs : I.Subsingleton := Set.ncard_le_one_iff_subsingleton.mp hcard
    letI : Subsingleton I := ⟨fun x y => Subtype.ext (hs x.2 y.2)⟩
    rw [linearIndependent_subsingleton_index_iff]
    intro i
    change (fun _ : Fin 1 => (1 : ℝ)) ≠ 0
    intro h
    exact one_ne_zero (congrFun h 0)

/-- The one-row real vector matroid has exactly the independent sets of
the rank-one uniform matroid, on the same finite labeled ground set. -/
theorem uniformOn_one_eq_oneRowVectorMatroid {α : Type*}
    (E : Set α) (hE : E.Finite) :
    uniformOn E hE 1 =
      vectorMatroid (K := ℝ) E hE (oneRowOnesReal α).col := by
  apply Matroid.ext_indep (by simp [uniformOn])
  intro I hI
  have hIE : I ⊆ E := by simpa [uniformOn] using hI
  rw [uniformOn_indep_iff, vectorMatroid_indep_iff]
  haveI : Finite I := (hE.subset hIE).to_subtype
  simpa [hIE] using (oneRowOnesReal_linearIndependent_iff I).symm

/-- N257: the all-ones TU row and N053 transfer certify regularity of the
rank-one uniform matroid over arbitrary fields. -/
theorem uniformOn_one_regular {α : Type u}
    (E : Set α) (hE : E.Finite) :
    (uniformOn E hE 1).Regular.{u, v, v} := by
  rw [uniformOn_one_eq_oneRowVectorMatroid E hE]
  intro K _
  obtain ⟨B, hB, hBA, hEq⟩ :=
    vectorMatroid_realTU_represents_over_field (K := K)
      (oneRowOnesReal α) (oneRowOnesReal_isTotallyUnimodular α) E hE
  refine ⟨Fin 1 → K, inferInstance, inferInstance,
    (B.map fun z : ℤ => (z : K)).col, ?_⟩
  rw [hEq]
  exact vectorMatroid_represents E hE _

end Matroid
