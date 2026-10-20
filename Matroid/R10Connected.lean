import Matroid.R10CircuitParity
import Mathlib.Tactic.FinCases

/-! Finite matrix certificates for the manuscript's R10 connectedness assertion (N255). -/

namespace Matroid

/-- Fifteen displayed four-column dependencies covering every pair of labels. -/
def r10CircuitCandidate : Fin 15 → Finset (Fin 10)
  | 0 => {0, 1, 2, 6}
  | 1 => {0, 3, 4, 9}
  | 2 => {0, 1, 4, 5}
  | 3 => {0, 3, 6, 7}
  | 4 => {0, 2, 8, 9}
  | 5 => {0, 5, 7, 8}
  | 6 => {1, 2, 3, 7}
  | 7 => {1, 3, 5, 9}
  | 8 => {1, 4, 7, 8}
  | 9 => {1, 6, 8, 9}
  | 10 => {2, 3, 4, 8}
  | 11 => {2, 4, 5, 6}
  | 12 => {2, 5, 7, 9}
  | 13 => {3, 5, 6, 8}
  | 14 => {4, 6, 7, 9}

theorem r10CircuitCandidate_sum_zero (i : Fin 15) :
    ∑ e ∈ r10CircuitCandidate i, r10BinaryMatrix.col e = 0 := by
  fin_cases i <;> decide

theorem r10CircuitCandidate_covers (e : Fin 10) :
    ∃ i : Fin 15, 0 ∈ r10CircuitCandidate i ∧ e ∈ r10CircuitCandidate i := by
  fin_cases e <;> decide

theorem r10CircuitCandidate_covers_pair (e f : Fin 10) :
    ∃ i : Fin 15, e ∈ r10CircuitCandidate i ∧ f ∈ r10CircuitCandidate i := by
  fin_cases e <;> fin_cases f <;> decide

private theorem r10BinaryMatrix_col_injective :
    Function.Injective r10BinaryMatrix.col := by
  decide

private theorem r10_no_two_circuit {C : Set (Fin 10)}
    (hC : r10.IsCircuit C) : C.ncard ≠ 2 := by
  intro htwo
  obtain ⟨e, f, hef, rfl⟩ := Set.ncard_eq_two.mp htwo
  have hrep : r10.Represents (K := ZMod 2) r10BinaryMatrix.col := by
    rw [r10_eq_binary]
    exact vectorMatroid_represents _ _ _
  have hsum := hrep.binaryCircuit_sum_zero r10BinaryMatrix.col hC
  have heq : r10BinaryMatrix.col e = r10BinaryMatrix.col f := by
    simpa [Set.Finite.toFinset, hef, add_eq_zero_iff_eq_neg,
      ZModModule.neg_eq_self] using hsum
  exact hef (r10BinaryMatrix_col_injective heq)

private theorem r10_no_one_circuit {C : Set (Fin 10)}
    (hC : r10.IsCircuit C) : C.ncard ≠ 1 := by
  intro hone
  obtain ⟨e, rfl⟩ := Set.ncard_eq_one.mp hone
  have hrep : r10.Represents (K := ZMod 2) r10BinaryMatrix.col := by
    rw [r10_eq_binary]
    exact vectorMatroid_represents _ _ _
  have hsum := hrep.binaryCircuit_sum_zero r10BinaryMatrix.col hC
  have hcol : r10BinaryMatrix.col e = 0 := by
    simpa [Set.Finite.toFinset] using hsum
  have hnonzero : ∀ f : Fin 10, r10BinaryMatrix.col f ≠ 0 := by decide
  exact hnonzero e hcol

theorem r10_circuit_card_ge_four {C : Set (Fin 10)}
    (hC : r10.IsCircuit C) : 4 ≤ C.ncard := by
  have hzero : C.ncard ≠ 0 := by
    intro hz
    have hempty : C = ∅ :=
      (Set.ncard_eq_zero (r10.ground_finite.subset hC.subset_ground)).mp hz
    exact hC.nonempty.ne_empty hempty
  have hone := r10_no_one_circuit hC
  have htwo := r10_no_two_circuit hC
  have hthree := r10_circuit_card_ne_three hC
  omega

/-- Each finite zero-sum witness is a genuine circuit: its four distinct
columns admit no smaller nonempty binary circuit. -/
theorem r10CircuitCandidate_isCircuit (i : Fin 15) :
    r10.IsCircuit (r10CircuitCandidate i : Set (Fin 10)) := by
  have hrep : r10.Represents (K := ZMod 2) r10BinaryMatrix.col := by
    rw [r10_eq_binary]
    exact vectorMatroid_represents _ _ _
  have hground : (r10CircuitCandidate i : Set (Fin 10)) ⊆ r10.E := by
    simp
  have hsum :
      ∑ e ∈ (r10.ground_finite.subset hground).toFinset,
        r10BinaryMatrix.col e = 0 := by
    simpa [Set.Finite.toFinset] using r10CircuitCandidate_sum_zero i
  have hcycle : r10.IsCircuitUnion (r10CircuitCandidate i : Set (Fin 10)) :=
    (isCircuitUnion_iff_binary_sum_eq_zero r10BinaryMatrix.col hrep hground).2 hsum
  obtain ⟨Cs, hCs, _, hUnion⟩ := hcycle
  have hnonempty : Cs.Nonempty := by
    by_contra hn
    have hempty : Cs = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hSempty : (r10CircuitCandidate i : Set (Fin 10)) = ∅ := by
      simpa [hempty] using hUnion
    have hSne : (r10CircuitCandidate i).Nonempty := by
      fin_cases i <;> decide
    obtain ⟨e, he⟩ := hSne
    have : e ∈ (∅ : Set (Fin 10)) := hSempty ▸ he
    simp at this
  obtain ⟨C, hCmem⟩ := hnonempty
  have hC : r10.IsCircuit C := hCs C hCmem
  have hCsubset : C ⊆ (r10CircuitCandidate i : Set (Fin 10)) := by
    rw [hUnion]
    intro e he
    exact Set.mem_sUnion.mpr ⟨C, by simpa using hCmem, he⟩
  have hcard : (r10CircuitCandidate i : Set (Fin 10)).ncard = 4 := by
    fin_cases i <;> simp [r10CircuitCandidate]
  have hEq : C = (r10CircuitCandidate i : Set (Fin 10)) :=
    Set.eq_of_subset_of_ncard_le hCsubset (by
      rw [hcard]
      exact r10_circuit_card_ge_four hC)
  rwa [← hEq]

/-- N255: every two labels of the displayed R10 belong to a common
matroid circuit. This is the connectedness property used in the manuscript. -/
theorem r10_common_circuit (e f : Fin 10) :
    ∃ C : Set (Fin 10), r10.IsCircuit C ∧ e ∈ C ∧ f ∈ C := by
  obtain ⟨i, he, hf⟩ := r10CircuitCandidate_covers_pair e f
  exact ⟨r10CircuitCandidate i, r10CircuitCandidate_isCircuit i, he, hf⟩

end Matroid
