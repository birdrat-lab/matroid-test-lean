import Matroid.R10Connected
import Matroid.Pointed
import Mathlib.Tactic.FinCases

/-! Certificates toward the pointed R10 target-circuit enumeration (N195). -/

namespace Matroid

/-- The six four-element target circuits in manuscript edge-label order. -/
def r10TargetFourCircuit (i : Fin 6) : Finset (Fin 10) :=
  r10CircuitCandidate (i.castLE (by decide : 6 ≤ 15))

theorem r10TargetFourCircuit_isCircuit (i : Fin 6) :
    r10.IsCircuit (r10TargetFourCircuit i : Set (Fin 10)) :=
  r10CircuitCandidate_isCircuit _

/-- The nine six-element target dependencies. The manuscript identifies
their non-target parts as row-column double stars. -/
def r10TargetSixCandidate : Fin 9 → Finset (Fin 10)
  | 0 => {0, 1, 2, 3, 5, 8}
  | 1 => {0, 1, 2, 4, 7, 9}
  | 2 => {0, 1, 3, 4, 6, 8}
  | 3 => {0, 1, 3, 7, 8, 9}
  | 4 => {0, 1, 5, 6, 7, 9}
  | 5 => {0, 2, 3, 4, 5, 7}
  | 6 => {0, 2, 3, 5, 6, 9}
  | 7 => {0, 2, 4, 6, 7, 8}
  | 8 => {0, 4, 5, 6, 8, 9}

theorem r10TargetSixCandidate_sum_zero (i : Fin 9) :
    ∑ e ∈ r10TargetSixCandidate i, r10BinaryMatrix.col e = 0 := by
  fin_cases i <;> decide

theorem r10TargetSixCandidate_card (i : Fin 9) :
    (r10TargetSixCandidate i).card = 6 := by
  fin_cases i <;> decide

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 16384 in
private theorem r10_target_zeroSum_enumeration :
    ∀ s : Finset (Fin 10),
      0 ∈ s →
      (s.card = 4 ∨ s.card = 6) →
      (∑ e ∈ s, r10BinaryMatrix.col e = 0) →
      (∃ i : Fin 6, s = r10TargetFourCircuit i) ∨
      (∃ i : Fin 9, s = r10TargetSixCandidate i) := by
  decide

private theorem r10_small_cycle_isCircuit (S : Finset (Fin 10))
    (hne : S.Nonempty) (hcard : S.card < 8)
    (hcycle : r10.IsCircuitUnion (S : Set (Fin 10))) :
    r10.IsCircuit (S : Set (Fin 10)) := by
  obtain ⟨Cs, hCs, hdisj, hUnion⟩ := hcycle
  have hCsne : Cs.Nonempty := by
    by_contra hn
    have hempty : Cs = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hSempty : (S : Set (Fin 10)) = ∅ := by simpa [hempty] using hUnion
    obtain ⟨e, he⟩ := hne
    have : e ∈ (∅ : Set (Fin 10)) := hSempty ▸ he
    simp at this
  obtain ⟨C, hCmem⟩ := hCsne
  have hC : r10.IsCircuit C := hCs C hCmem
  have hCsub : C ⊆ (S : Set (Fin 10)) := by
    rw [hUnion]
    intro e he
    exact Set.mem_sUnion.mpr ⟨C, by simpa using hCmem, he⟩
  by_cases hEq : C = (S : Set (Fin 10))
  · rwa [← hEq]
  have hDexists : ∃ D, D ∈ Cs ∧ D ≠ C := by
    by_contra hn
    push Not at hn
    have hsub : Cs ⊆ {C} := by
      intro D hD
      simpa using hn D hD
    have hCsEq : Cs = {C} :=
      Finset.Subset.antisymm hsub (by simpa using hCmem)
    have hS : (S : Set (Fin 10)) = C := by
      simpa [hCsEq] using hUnion
    exact hEq hS.symm
  obtain ⟨D, hDmem, hDC⟩ := hDexists
  have hD : r10.IsCircuit D := hCs D hDmem
  have hDsub : D ⊆ (S : Set (Fin 10)) := by
    rw [hUnion]
    intro e he
    exact Set.mem_sUnion.mpr ⟨D, by simpa using hDmem, he⟩
  have hCD : Disjoint C D := hdisj C hCmem D hDmem (Ne.symm hDC)
  have hUcard : (C ∪ D).ncard = C.ncard + D.ncard :=
    Set.ncard_union_eq hCD
  have hUsub : C ∪ D ⊆ (S : Set (Fin 10)) :=
    Set.union_subset hCsub hDsub
  have hUle : (C ∪ D).ncard ≤ S.card := by
    simpa using Set.ncard_le_ncard hUsub
  have hCge := r10_circuit_card_ge_four hC
  have hDge := r10_circuit_card_ge_four hD
  omega

/-- The nine six-element zero-sum sets are minimal dependencies. -/
theorem r10TargetSixCandidate_isCircuit (i : Fin 9) :
    r10.IsCircuit (r10TargetSixCandidate i : Set (Fin 10)) := by
  have hground : (r10TargetSixCandidate i : Set (Fin 10)) ⊆ r10.E := by simp
  have hrep : r10.Represents (K := ZMod 2) r10BinaryMatrix.col := by
    rw [r10_eq_binary]
    exact vectorMatroid_represents _ _ _
  have hsum :
      ∑ e ∈ (r10.ground_finite.subset hground).toFinset,
        r10BinaryMatrix.col e = 0 := by
    simpa [Set.Finite.toFinset] using r10TargetSixCandidate_sum_zero i
  have hcycle : r10.IsCircuitUnion (r10TargetSixCandidate i : Set (Fin 10)) :=
    (isCircuitUnion_iff_binary_sum_eq_zero r10BinaryMatrix.col hrep hground).2 hsum
  have hne : (r10TargetSixCandidate i).Nonempty := by
    fin_cases i <;> decide
  apply r10_small_cycle_isCircuit _ hne
  · rw [r10TargetSixCandidate_card]
    omega
  · exact hcycle

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 16384 in
private theorem r10_target_zeroSum_has_classified_or_subcircuit :
    ∀ s : Finset (Fin 10),
      0 ∈ s →
      (∑ e ∈ s, r10BinaryMatrix.col e = 0) →
      (∃ i : Fin 6, s = r10TargetFourCircuit i) ∨
      (∃ i : Fin 9, s = r10TargetSixCandidate i) ∨
      (∃ i : Fin 15, r10CircuitCandidate i ⊂ s) := by
  decide

theorem r10TargetFourCircuit_target (i : Fin 6) :
    0 ∈ r10TargetFourCircuit i := by
  fin_cases i <;> decide

theorem r10TargetSixCandidate_target (i : Fin 9) :
    0 ∈ r10TargetSixCandidate i := by
  fin_cases i <;> decide

/-- The exact target-circuit classification of the displayed R10. -/
theorem r10_targetCircuit_iff (C : Set (Fin 10)) :
    (r10.IsCircuit C ∧ 0 ∈ C) ↔
      (∃ i : Fin 6, C = (r10TargetFourCircuit i : Set (Fin 10))) ∨
      (∃ i : Fin 9, C = (r10TargetSixCandidate i : Set (Fin 10))) := by
  constructor
  · rintro ⟨hC, h0⟩
    let hfin : C.Finite := r10.ground_finite.subset hC.subset_ground
    let s : Finset (Fin 10) := hfin.toFinset
    have h0s : 0 ∈ s := by simpa [s] using h0
    have hrep : r10.Represents (K := ZMod 2) r10BinaryMatrix.col := by
      rw [r10_eq_binary]
      exact vectorMatroid_represents _ _ _
    have hsum : ∑ e ∈ s, r10BinaryMatrix.col e = 0 :=
      hrep.binaryCircuit_sum_zero r10BinaryMatrix.col hC
    rcases r10_target_zeroSum_has_classified_or_subcircuit s h0s hsum with
      ⟨i, hEq⟩ | ⟨i, hEq⟩ | ⟨i, hproper⟩
    · exact Or.inl ⟨i, by simpa [s] using congrArg (fun t : Finset (Fin 10) =>
        (t : Set (Fin 10))) hEq⟩
    · exact Or.inr ⟨i, by simpa [s] using congrArg (fun t : Finset (Fin 10) =>
        (t : Set (Fin 10))) hEq⟩
    · have hsub : (r10CircuitCandidate i : Set (Fin 10)) ⊆ C := by
        intro e he
        have hes : e ∈ s := hproper.subset he
        simpa [s] using hes
      have hSetEq : C = (r10CircuitCandidate i : Set (Fin 10)) :=
        ((r10CircuitCandidate_isCircuit i).eq_of_subset_isCircuit hC hsub).symm
      have hFinEq : s = r10CircuitCandidate i := by
        ext e
        simpa [s] using (Set.ext_iff.mp hSetEq e)
      exact False.elim (hproper.ne hFinEq.symm)
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨r10TargetFourCircuit_isCircuit i, r10TargetFourCircuit_target i⟩
    · exact ⟨r10TargetSixCandidate_isCircuit i, r10TargetSixCandidate_target i⟩

/-- The manuscript's edge table for the displayed K3,3 deletion. -/
def r10Edge : Matrix (Fin 3) (Fin 3) (Fin 10) :=
  !![1, 3, 8;
     7, 2, 4;
     9, 5, 6]

def r10Row (i : Fin 3) : Finset (Fin 10) :=
  Finset.univ.image (r10Edge i)

def r10Column (j : Fin 3) : Finset (Fin 10) :=
  Finset.univ.image (fun i => r10Edge i j)

def r10PerfectMatching (σ : Equiv.Perm (Fin 3)) : Finset (Fin 10) :=
  Finset.univ.image (fun i => r10Edge i (σ i))

theorem r10TargetFourCircuit_is_matching (i : Fin 6) :
    ∃ σ : Equiv.Perm (Fin 3),
      (r10TargetFourCircuit i).erase 0 = r10PerfectMatching σ := by
  fin_cases i <;> decide

theorem r10PerfectMatching_is_targetFour (σ : Equiv.Perm (Fin 3)) :
    ∃ i : Fin 6, (r10TargetFourCircuit i).erase 0 = r10PerfectMatching σ := by
  exact (by decide : ∀ σ : Equiv.Perm (Fin 3),
    ∃ i : Fin 6, (r10TargetFourCircuit i).erase 0 = r10PerfectMatching σ) σ

theorem r10TargetSixCandidate_is_doubleStar (k : Fin 9) :
    ∃ i j : Fin 3,
      (r10TargetSixCandidate k).erase 0 = r10Row i ∪ r10Column j := by
  fin_cases k <;> decide

theorem r10DoubleStar_is_targetSix (i j : Fin 3) :
    ∃ k : Fin 9,
      (r10TargetSixCandidate k).erase 0 = r10Row i ∪ r10Column j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem insert_erase_zero (s : Finset (Fin 10)) (h0 : 0 ∈ s) :
    insert 0 ((s.erase 0 : Finset (Fin 10)) : Set (Fin 10)) = (s : Set (Fin 10)) := by
  ext e
  by_cases he : e = 0
  · subst e
    simp [h0]
  · simp [he]

private theorem eq_erase_zero_of_insert_eq (S : Set (Fin 10))
    (h0S : 0 ∉ S) (s : Finset (Fin 10))
    (hEq : insert 0 S = (s : Set (Fin 10))) :
    S = ((s.erase 0 : Finset (Fin 10)) : Set (Fin 10)) := by
  ext e
  by_cases he : e = 0
  · subst e
    simp [h0S]
  · have hh := Set.ext_iff.mp hEq e
    simpa [he] using hh

/-- N195: exactly the six perfect matchings and nine row-column double
stars minimally span the displayed target `0`. -/
theorem r10_minimalTargetSpanning_iff (S : Set (Fin 10))
    (hS : S ⊆ r10.E \ {0}) :
    (0 ∈ r10.closure S ∧
      ∀ T : Set (Fin 10), T ⊂ S → 0 ∉ r10.closure T) ↔
      (∃ σ : Equiv.Perm (Fin 3), S = (r10PerfectMatching σ : Set (Fin 10))) ∨
      (∃ i j : Fin 3, S = ((r10Row i ∪ r10Column j) : Set (Fin 10))) := by
  have h0S : 0 ∉ S := by
    intro h
    exact (hS h).2 rfl
  have hiff := minimal_spanning_iff_circuit (M := r10)
    (fun e he => (hS he).1) h0S
  constructor
  · intro hmin
    have hC : r10.IsCircuit (insert 0 S) := hiff.mp hmin
    rcases (r10_targetCircuit_iff (insert 0 S)).mp ⟨hC, Set.mem_insert 0 S⟩ with
      ⟨k, hEq⟩ | ⟨k, hEq⟩
    · have hSEq := eq_erase_zero_of_insert_eq S h0S _ hEq
      obtain ⟨σ, hMatch⟩ := r10TargetFourCircuit_is_matching k
      exact Or.inl ⟨σ, by simpa [hMatch] using hSEq⟩
    · have hSEq := eq_erase_zero_of_insert_eq S h0S _ hEq
      obtain ⟨i, j, hStar⟩ := r10TargetSixCandidate_is_doubleStar k
      exact Or.inr ⟨i, j, by simpa [hStar] using hSEq⟩
  · rintro (⟨σ, rfl⟩ | ⟨i, j, rfl⟩)
    · obtain ⟨k, hk⟩ := r10PerfectMatching_is_targetFour σ
      apply hiff.mpr
      have h0 := r10TargetFourCircuit_target k
      have hInsert := insert_erase_zero (r10TargetFourCircuit k) h0
      change r10.IsCircuit (insert 0 ((r10PerfectMatching σ : Finset (Fin 10)) : Set (Fin 10)))
      rw [← hk, hInsert]
      exact r10TargetFourCircuit_isCircuit k
    · obtain ⟨k, hk⟩ := r10DoubleStar_is_targetSix i j
      apply hiff.mpr
      have h0 := r10TargetSixCandidate_target k
      have hInsert := insert_erase_zero (r10TargetSixCandidate k) h0
      have hTarget : r10.IsCircuit
          (insert 0 (((r10Row i ∪ r10Column j) : Finset (Fin 10)) : Set (Fin 10))) := by
        rw [← hk, hInsert]
        exact r10TargetSixCandidate_isCircuit k
      simpa only [Finset.coe_union] using hTarget

end Matroid
