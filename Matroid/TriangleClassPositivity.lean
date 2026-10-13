import Matroid.Depth6TriangleWeights
import Matroid.OneSumWeights
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.ENNReal.Inv
import Mathlib.Tactic.Positivity

/-! Strict positivity of weighted triangle closure classes. -/

open Set
open scoped NNReal

namespace Matroid

/-- N162: coindependence of the distinguished triangle supplies an actual
nontriangle basis in the all-spanned class. Its product is strictly positive
under positive weights. -/
theorem weightedTriangle_a_pos {α : Type*}
    (M : Matroid α) [M.Finite]
    (a b c : α) (_hT : M.IsCircuit ({a, b, c} : Set α))
    (hco : M.Coindep ({a, b, c} : Set α))
    (w : α → ℝ≥0)
    (hw : ∀ e ∈ M.E \ ({a, b, c} : Set α), 0 < w e) :
    0 < weightedTrianglePhi M M.ground_finite
      {a, b, c} {a, b, c} w := by
  classical
  let T : Set α := {a, b, c}
  let X : Set α := M.E \ T
  obtain ⟨S, hS⟩ := M.exists_isBasis' X
  have hSsub : S ⊆ X := hS.subset
  have hSfin : S.Finite := M.ground_finite.subset
    (hSsub.trans Set.sdiff_subset)
  let s := hSfin.toFinset
  have hsEq : (s : Set α) = S := by simp [s]
  have hclX : M.closure X = M.E :=
    (M.spanning_iff_closure_eq Set.sdiff_subset).1 hco.compl_spanning
  have hclS : M.closure S = M.E := hS.closure_eq_closure.trans hclX
  have hclST : M.closure (S ∪ T) = M.E := by
    apply Set.Subset.antisymm (M.closure_subset_ground _)
    rw [← hclS]
    exact M.closure_subset_closure Set.subset_union_left
  have hclass : M.closure S ∩ T = T := by
    rw [hclS]
    exact Set.inter_eq_right.mpr hco.subset_ground
  unfold weightedTrianglePhi
  apply Finset.sum_pos' (by intros; positivity)
  refine ⟨s, ?_, ?_⟩
  · apply Finset.mem_powerset.mpr
    intro e he
    have heS : e ∈ S := by simpa [s] using he
    have heX := hSsub heS
    simp [X, T] at heX
    simp [heX.1, heX.2]
  have hterm : M.Indep (s : Set α) ∧
      M.closure ((s : Set α) ∪ T) = M.E ∧
      M.closure (s : Set α) ∩ T = T := by
    simpa only [hsEq] using ⟨hS.indep, hclST, hclass⟩
  have hterm' : M.Indep (s : Set α) ∧
      M.closure ((s : Set α) ∪ {a, b, c}) = M.E ∧
      M.closure (s : Set α) ∩ {a, b, c} = {a, b, c} := by
    simpa only [T] using hterm
  rw [if_pos hterm']
  apply Finset.prod_pos
  intro e he
  have heS : e ∈ S := by simpa [s] using he
  exact hw e (hSsub heS)

/-- N163: extend two triangle elements to a basis and remove the triangle.
The independent-union closure intersection lemma excludes every triangle
element from the closure of the remaining basis elements. -/
theorem weightedTriangle_c_pos {α : Type*}
    (M : Matroid α) [M.Finite]
    (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hT : M.IsCircuit ({a, b, c} : Set α))
    (_hco : M.Coindep ({a, b, c} : Set α))
    (w : α → ℝ≥0)
    (hw : ∀ e ∈ M.E \ ({a, b, c} : Set α), 0 < w e) :
    0 < weightedTrianglePhi M M.ground_finite
      {a, b, c} ∅ w := by
  classical
  let T : Set α := {a, b, c}
  let I : Set α := {a, b}
  have hcT : c ∈ T := by simp [T]
  have hTdel : T \ {c} = I := by
    ext x
    simp only [T, I, Set.mem_sdiff, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨h, hc⟩
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (hc h)
    · intro h
      rcases h with rfl | rfl
      · exact ⟨Or.inl rfl, hac⟩
      · exact ⟨Or.inr (Or.inl rfl), hbc⟩
  have hI : M.Indep I := by
    have h := hT.sdiff_singleton_indep hcT
    change M.Indep (T \ {c}) at h
    rwa [hTdel] at h
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  have hcB : c ∉ B := by
    intro hcB
    have hTB : T ⊆ B := by
      intro x hx
      simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hIB (by simp [I])
      · exact hIB (by simp [I])
      · exact hcB
    exact hT.not_indep (hB.indep.subset hTB)
  let S : Set α := B \ T
  have hSsub : S ⊆ M.E \ T := by
    intro x hx
    exact ⟨hB.subset_ground hx.1, hx.2⟩
  have hSI : S ∪ I ⊆ B := by
    intro x hx
    rcases hx with hx | hx
    · exact hx.1
    · exact hIB hx
  have hSIindep : M.Indep (S ∪ I) := hB.indep.subset hSI
  have hdisj : S ∩ I = ∅ := by
    have hIT : I ⊆ T := by
      intro x hx
      simp only [I, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · simp [T]
      · simp [T]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hxS, hxI⟩
    exact hxS.2 (hIT hxI)
  have hclI : T ⊆ M.closure I := by
    intro x hx
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hxa | hxb | hxc
    · rw [hxa]
      exact M.mem_closure_of_mem (by simp [I]) hI.subset_ground
    · rw [hxb]
      exact M.mem_closure_of_mem (by simp [I]) hI.subset_ground
    · rw [hxc]
      have hclc := hT.mem_closure_sdiff_singleton_of_mem hcT
      change c ∈ M.closure (T \ {c}) at hclc
      rwa [hTdel] at hclc
  have hclSI : M.closure S ∩ M.closure I = M.closure ∅ := by
    rw [← hSIindep.closure_inter_eq_inter_closure, hdisj]
  have haNL : M.IsNonloop a :=
    (hI.subset (by simp [I] : ({a} : Set α) ⊆ I)).isNonloop
  have hbNL : M.IsNonloop b :=
    (hI.subset (by simp [I] : ({b} : Set α) ⊆ I)).isNonloop
  have hcNL : M.IsNonloop c := by
    have haT : a ∈ T := by simp [T]
    have hcsub : ({c} : Set α) ⊆ T \ {a} := by
      intro x hx
      have hxc : x = c := by simpa using hx
      subst x
      exact ⟨by simp [T], by simpa using hac.symm⟩
    exact ((hT.sdiff_singleton_indep haT).subset hcsub).isNonloop
  have hclass : M.closure S ∩ T = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    intro hx
    have hxloop : x ∈ M.closure ∅ := hclSI ▸ ⟨hx.1, hclI hx.2⟩
    have hxT : x = a ∨ x = b ∨ x = c := by simpa [T] using hx.2
    rcases hxT with hxa | hxb | hxc
    · exact haNL.not_isLoop (by simpa only [hxa, Matroid.IsLoop, Matroid.loops] using hxloop)
    · exact hbNL.not_isLoop (by simpa only [hxb, Matroid.IsLoop, Matroid.loops] using hxloop)
    · exact hcNL.not_isLoop (by simpa only [hxc, Matroid.IsLoop, Matroid.loops] using hxloop)
  have hBsub : B ⊆ S ∪ T := by
    intro x hx
    by_cases hxT : x ∈ T
    · exact Or.inr hxT
    · exact Or.inl ⟨hx, hxT⟩
  have hclST : M.closure (S ∪ T) = M.E := by
    apply Set.Subset.antisymm (M.closure_subset_ground _)
    rw [← hB.closure_eq]
    exact M.closure_subset_closure hBsub
  have hSfin : S.Finite := M.ground_finite.subset
    (hSsub.trans Set.sdiff_subset)
  let s := hSfin.toFinset
  have hsEq : (s : Set α) = S := by simp [s]
  unfold weightedTrianglePhi
  apply Finset.sum_pos' (by intros; positivity)
  refine ⟨s, ?_, ?_⟩
  · apply Finset.mem_powerset.mpr
    intro e he
    have heS : e ∈ S := by simpa [s] using he
    have heX := hSsub heS
    simp [T] at heX
    simp [heX.1, heX.2]
  have hterm : M.Indep (s : Set α) ∧
      M.closure ((s : Set α) ∪ {a, b, c}) = M.E ∧
      M.closure (s : Set α) ∩ {a, b, c} = ∅ := by
    simpa only [hsEq, T] using
      ⟨hB.indep.subset Set.sdiff_subset, hclST, hclass⟩
  rw [if_pos hterm]
  apply Finset.prod_pos
  intro e he
  have heS : e ∈ S := by simpa [s] using he
  exact hw e (hSsub heS)

end Matroid
