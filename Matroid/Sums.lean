import Matroid.Cycles
import Mathlib.Combinatorics.Matroid.Sum

/-! # Disjoint-ground-set matroid sums -/

namespace Matroid

/-- Manuscript `def:regular-matroid-sums` (N064), one-sum construction.
The ground sets are required to be disjoint and nonempty as in the manuscript.
The cycle characterization is proved below. -/
noncomputable def oneSum {α : Type*} (M N : Matroid α)
    (hdisj : Disjoint M.E N.E) (_hM : M.E.Nonempty) (_hN : N.E.Nonempty) :
    Matroid α :=
  M.disjointSum N hdisj

/-- The one-sum has the union of the two manuscript ground sets. -/
theorem oneSum_ground {α : Type*} (M N : Matroid α)
    (hdisj : Disjoint M.E N.E) (hM : M.E.Nonempty) (hN : N.E.Nonempty) :
    (oneSum M N hdisj hM hN).E = M.E ∪ N.E := by
  simp [oneSum]

/-- The direct-sum independence interface underlying the one-sum. -/
theorem oneSum_indep_iff {α : Type*} (M N : Matroid α)
    (hdisj : Disjoint M.E N.E) (hM : M.E.Nonempty) (hN : N.E.Nonempty)
    (I : Set α) :
    (oneSum M N hdisj hM hN).Indep I ↔
      M.Indep (I ∩ M.E) ∧ N.Indep (I ∩ N.E) ∧ I ⊆ M.E ∪ N.E := by
  simp [oneSum]

/-- A circuit of the left summand is a circuit of the one-sum. This is one
direction of the cycle characterization in manuscript N064. -/
theorem IsCircuit.oneSum_left {α : Type*} {M N : Matroid α}
    {C : Set α} (hC : M.IsCircuit C)
    (hdisj : Disjoint M.E N.E) (hM : M.E.Nonempty) (hN : N.E.Nonempty) :
    (oneSum M N hdisj hM hN).IsCircuit C := by
  have hground : C ⊆ (oneSum M N hdisj hM hN).E := by
    rw [oneSum_ground]
    exact hC.subset_ground.trans Set.subset_union_left
  apply (isCircuit_iff_forall_ssubset).2
  refine ⟨?_, ?_⟩
  · apply (not_indep_iff hground).1
    intro hi
    have hleft := (oneSum_indep_iff M N hdisj hM hN C).1 hi |>.1
    have hCE : C ∩ M.E = C := Set.inter_eq_left.mpr hC.subset_ground
    exact hC.not_indep (hCE ▸ hleft)
  · intro J hJC
    have hJM : J ∩ M.E = J :=
      Set.inter_eq_left.mpr (hJC.subset.trans hC.subset_ground)
    have hJN : J ∩ N.E = ∅ :=
      Set.disjoint_iff_inter_eq_empty.mp
        (hdisj.mono_left (hJC.subset.trans hC.subset_ground))
    apply (oneSum_indep_iff M N hdisj hM hN J).2
    refine ⟨?_, ?_, ?_⟩
    · simpa [hJM] using hC.ssubset_indep hJC
    · simp [hJN]
    · exact (hJC.subset.trans hC.subset_ground).trans Set.subset_union_left

/-- Circuits of the right summand remain circuits of the one-sum. -/
theorem IsCircuit.oneSum_right {α : Type*} {M N : Matroid α}
    {C : Set α} (hC : N.IsCircuit C)
    (hdisj : Disjoint M.E N.E) (hM : M.E.Nonempty) (hN : N.E.Nonempty) :
    (oneSum M N hdisj hM hN).IsCircuit C := by
  have h := hC.oneSum_left hdisj.symm hN hM
  change (N.disjointSum M hdisj.symm).IsCircuit C at h
  change (M.disjointSum N hdisj).IsCircuit C
  rw [Matroid.disjointSum_comm]
  exact h

/-- Every one-sum circuit comes entirely from one summand. -/
theorem oneSum_isCircuit_iff {α : Type*} (M N : Matroid α)
    (hdisj : Disjoint M.E N.E) (hM : M.E.Nonempty) (hN : N.E.Nonempty)
    (C : Set α) :
    (oneSum M N hdisj hM hN).IsCircuit C ↔
      M.IsCircuit C ∨ N.IsCircuit C := by
  constructor
  · intro hC
    have hCE : C ⊆ M.E ∪ N.E := by
      simpa only [oneSum_ground] using hC.subset_ground
    have hdep : ¬ M.Indep (C ∩ M.E) ∨ ¬ N.Indep (C ∩ N.E) := by
      by_contra hn
      push Not at hn
      exact hC.not_indep
        ((oneSum_indep_iff M N hdisj hM hN C).2 ⟨hn.1, hn.2, hCE⟩)
    rcases hdep with hleft | hright
    · obtain ⟨D, hDC, hD⟩ :=
        ((not_indep_iff Set.inter_subset_right).1 hleft).exists_isCircuit_subset
      have hDsum := hD.oneSum_left hdisj hM hN
      have hDC' : D ⊆ C := hDC.trans Set.inter_subset_left
      have hEq : D = C := hDsum.eq_of_subset_isCircuit hC hDC'
      exact Or.inl (hEq ▸ hD)
    · obtain ⟨D, hDC, hD⟩ :=
        ((not_indep_iff Set.inter_subset_right).1 hright).exists_isCircuit_subset
      have hDsum := hD.oneSum_right hdisj hM hN
      have hDC' : D ⊆ C := hDC.trans Set.inter_subset_left
      have hEq : D = C := hDsum.eq_of_subset_isCircuit hC hDC'
      exact Or.inr (hEq ▸ hD)
  · rintro (hC | hC)
    · exact hC.oneSum_left hdisj hM hN
    · exact hC.oneSum_right hdisj hM hN

private theorem symmDiff_eq_union_of_disjoint {α : Type*}
    {X Y : Set α} (h : Disjoint X Y) : symmDiff X Y = X ∪ Y :=
  h.symmDiff_eq_sup

/-- Manuscript `def:regular-matroid-sums` (N064): for disjoint nonempty
ground sets, one-sum cycles are exactly symmetric differences of cycles
from the two summands. -/
theorem oneSum_isCircuitUnion_iff {α : Type*} (M N : Matroid α)
    (hdisj : Disjoint M.E N.E) (hM : M.E.Nonempty) (hN : N.E.Nonempty)
    (X : Set α) :
    (oneSum M N hdisj hM hN).IsCircuitUnion X ↔
      ∃ X₁ X₂ : Set α,
        M.IsCircuitUnion X₁ ∧ N.IsCircuitUnion X₂ ∧
          X = symmDiff X₁ X₂ := by
  classical
  constructor
  · rintro ⟨Cs, hCs, hpair, rfl⟩
    let L := Cs.filter M.IsCircuit
    let R := Cs.filter (fun C => ¬ M.IsCircuit C)
    let X₁ : Set α := ⋃₀ (L : Set (Set α))
    let X₂ : Set α := ⋃₀ (R : Set (Set α))
    have hL : ∀ C ∈ L, M.IsCircuit C := by
      intro C hC
      exact (Finset.mem_filter.mp hC).2
    have hR : ∀ C ∈ R, N.IsCircuit C := by
      intro C hC
      obtain ⟨hCC, hn⟩ := Finset.mem_filter.mp hC
      exact (oneSum_isCircuit_iff M N hdisj hM hN C).1 (hCs C hCC) |>.resolve_left hn
    have hLpair : ∀ C ∈ L, ∀ D ∈ L, C ≠ D → Disjoint C D := by
      intro C hC D hD hne
      exact hpair C (Finset.mem_filter.mp hC).1 D (Finset.mem_filter.mp hD).1 hne
    have hRpair : ∀ C ∈ R, ∀ D ∈ R, C ≠ D → Disjoint C D := by
      intro C hC D hD hne
      exact hpair C (Finset.mem_filter.mp hC).1 D (Finset.mem_filter.mp hD).1 hne
    have hX₁ : X₁ ⊆ M.E := by
      intro x hx
      obtain ⟨C, hC, hxC⟩ := Set.mem_sUnion.mp hx
      exact (hL C (by simpa using hC)).subset_ground hxC
    have hX₂ : X₂ ⊆ N.E := by
      intro x hx
      obtain ⟨C, hC, hxC⟩ := Set.mem_sUnion.mp hx
      exact (hR C (by simpa using hC)).subset_ground hxC
    have hunion : (⋃₀ (Cs : Set (Set α))) = X₁ ∪ X₂ := by
      ext x
      simp only [Set.mem_sUnion, Set.mem_union]
      constructor
      · rintro ⟨C, hCC, hxC⟩
        by_cases hm : M.IsCircuit C
        · exact Or.inl ⟨C, Finset.mem_filter.mpr ⟨hCC, hm⟩, hxC⟩
        · exact Or.inr ⟨C, Finset.mem_filter.mpr ⟨hCC, hm⟩, hxC⟩
      · rintro (⟨C, hC, hxC⟩ | ⟨C, hC, hxC⟩)
        · exact ⟨C, (Finset.mem_filter.mp hC).1, hxC⟩
        · exact ⟨C, (Finset.mem_filter.mp hC).1, hxC⟩
    refine ⟨X₁, X₂, ⟨L, hL, hLpair, rfl⟩,
      ⟨R, hR, hRpair, rfl⟩, ?_⟩
    rw [symmDiff_eq_union_of_disjoint (hdisj.mono hX₁ hX₂)]
    exact hunion
  · rintro ⟨X₁, X₂, ⟨L, hL, hLpair, hXL⟩,
        ⟨R, hR, hRpair, hXR⟩, rfl⟩
    have hX₁ : X₁ ⊆ M.E :=
      IsCircuitUnion.subset_ground ⟨L, hL, hLpair, hXL⟩
    have hX₂ : X₂ ⊆ N.E :=
      IsCircuitUnion.subset_ground ⟨R, hR, hRpair, hXR⟩
    refine ⟨L ∪ R, ?_, ?_, ?_⟩
    · intro C hC
      rcases Finset.mem_union.mp hC with hC | hC
      · exact (hL C hC).oneSum_left hdisj hM hN
      · exact (hR C hC).oneSum_right hdisj hM hN
    · intro C hC D hD hne
      rcases Finset.mem_union.mp hC with hCL | hCR <;>
        rcases Finset.mem_union.mp hD with hDL | hDR
      · exact hLpair C hCL D hDL hne
      · exact hdisj.mono (hL C hCL).subset_ground (hR D hDR).subset_ground
      · exact (hdisj.mono (hL D hDL).subset_ground
          (hR C hCR).subset_ground).symm
      · exact hRpair C hCR D hDR hne
    · rw [symmDiff_eq_union_of_disjoint (hdisj.mono hX₁ hX₂), hXL, hXR]
      ext x
      simp only [Set.mem_union, Set.mem_sUnion, Finset.coe_union]
      constructor
      · rintro (⟨C, hC, hx⟩ | ⟨C, hC, hx⟩)
        · exact ⟨C, Or.inl hC, hx⟩
        · exact ⟨C, Or.inr hC, hx⟩
      · rintro ⟨C, (hC | hC), hx⟩
        · exact Or.inl ⟨C, hC, hx⟩
        · exact Or.inr ⟨C, hC, hx⟩

end Matroid
