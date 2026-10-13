import Matroid.TwoSumCycles

/-! Independence direction of the proper two-sum basis correspondence. -/

namespace Matroid

open Set

universe u w

/-- If the first summand basis contains the shared port, the union
with that port removed is independent in the proper two-sum. This is the
independence half of manuscript N138; maximality and the converse are
separate remaining obligations. -/
theorem regularTwoSum_indep_of_bases_first_port {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p : α) (hinter : M.E ∩ N.E = {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard)
    {B₁ B₂ : Set α} (hB₁ : M.IsBase B₁) (hB₂ : N.IsBase B₂)
    (hp₁ : p ∈ B₁) :
    (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN).Indep
      ((B₁ ∪ B₂) \ {p}) := by
  let P := regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN
  let S := (B₁ ∪ B₂) \ {p}
  have hcommon {x : α} (hxM : x ∈ M.E) (hxN : x ∈ N.E) : x = p := by
    have h : x ∈ M.E ∩ N.E := ⟨hxM, hxN⟩
    simpa [hinter] using h
  have hSE : S ⊆ P.E := by
    rw [regularTwoSum_ground]
    intro x hx
    obtain ⟨hxU, hxp⟩ : x ∈ B₁ ∪ B₂ ∧ x ≠ p := by simpa [S] using hx
    rcases (show x ∈ B₁ ∨ x ∈ B₂ from hxU) with hx₁ | hx₂
    · have hxM := hB₁.subset_ground hx₁
      apply Set.mem_symmDiff.mpr
      left
      refine ⟨hxM, ?_⟩
      intro hxN
      exact hxp (hcommon hxM hxN)
    · have hxN := hB₂.subset_ground hx₂
      apply Set.mem_symmDiff.mpr
      right
      refine ⟨hxN, ?_⟩
      intro hxM
      exact hxp (hcommon hxM hxN)
  apply (P.indep_iff_forall_subset_not_isCircuit hSE).2
  intro K hKS hK
  obtain ⟨C, D, hC, hD, hEq, _⟩ :=
    (regularTwoSum_isCircuitUnion_iff M N hM hN p hinter
      hlM hlN hcM hcN hnM hnN K).1 hK.isCircuitUnion
  have hCsub : C ⊆ B₁ := by
    intro x hxC
    by_cases hxp : x = p
    · simpa [hxp] using hp₁
    have hxM := hC.subset_ground hxC
    have hxNnot : x ∉ N.E := by
      intro hxN
      exact hxp (hcommon hxM hxN)
    have hxDnot : x ∉ D := fun hxD => hxNnot (hD.subset_ground hxD)
    have hxK : x ∈ K := by
      rw [hEq]
      exact Set.mem_symmDiff.mpr (Or.inl ⟨hxC, hxDnot⟩)
    have hxS := hKS hxK
    have hxU : x ∈ B₁ ∪ B₂ := (show x ∈ B₁ ∪ B₂ ∧ x ≠ p from by
      simpa [S] using hxS).1
    rcases (show x ∈ B₁ ∨ x ∈ B₂ from hxU) with hx₁ | hx₂
    · exact hx₁
    · exact False.elim (hxNnot (hB₂.subset_ground hx₂))
  have hCempty : C = ∅ := hC.eq_empty_of_subset_indep hB₁.indep hCsub
  have hKEqD : K = D := by
    ext x
    have h := congrArg (fun T : Set α => x ∈ T) hEq
    simpa [hCempty, Set.mem_symmDiff] using h
  have hDsub : D ⊆ B₂ := by
    intro x hxD
    have hxS := hKS (hKEqD.symm ▸ hxD)
    have hxN := hD.subset_ground hxD
    have hxS' : x ∈ B₁ ∪ B₂ ∧ x ≠ p := by simpa [S] using hxS
    rcases (show x ∈ B₁ ∨ x ∈ B₂ from hxS'.1) with hx₁ | hx₂
    · have hxM := hB₁.subset_ground hx₁
      exact False.elim (hxS'.2 (hcommon hxM hxN))
    · exact hx₂
  have hDempty : D = ∅ := hD.eq_empty_of_subset_indep hB₂.indep hDsub
  exact hK.nonempty.ne_empty (hKEqD.trans hDempty)

end Matroid
