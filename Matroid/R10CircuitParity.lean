import Matroid.R10Certificate
import Matroid.Cycles
import Mathlib.Tactic.FinCases

/-! Binary parity certificate for the absence of R10 triangles. -/

namespace Matroid

/-- The exact displayed R10 matrix, reduced modulo two. -/
def r10BinaryMatrix : Matrix (Fin 5) (Fin 10) (ZMod 2) :=
  r10IntegerMatrix.map (fun z : ℤ => (z : ZMod 2))

/-- The manuscript's signed real TU matrix and Oxley's binary `A₁₀`
have exactly the same labeled column matroid. -/
theorem r10_eq_binary :
    r10 = vectorMatroid (K := ZMod 2) Set.univ
      Set.finite_univ r10BinaryMatrix.col := by
  simpa [r10, r10Matrix, r10BinaryMatrix] using
    (vectorMatroid_intCast_eq_of_totallyUnimodular
      (K := ℝ) (L := ZMod 2) r10IntegerMatrix
      r10IntegerMatrix_isTotallyUnimodular Set.univ Set.finite_univ)

/-- Every displayed column has odd coordinate parity. -/
theorem r10BinaryMatrix_column_parity (e : Fin 10) :
    (∑ i : Fin 5, r10BinaryMatrix i e) = 1 := by
  fin_cases e <;> decide

/-- N170: R10 has no three-element circuit. More strongly, all its
circuits have even size, by field transfer to characteristic two. -/
theorem r10_circuit_card_ne_three {C : Set (Fin 10)}
    (hC : r10.IsCircuit C) : C.ncard ≠ 3 := by
  have hEq : r10 = vectorMatroid (K := ZMod 2) Set.univ
      Set.finite_univ r10BinaryMatrix.col := r10_eq_binary
  have hC₂ : (vectorMatroid (K := ZMod 2) Set.univ
      Set.finite_univ r10BinaryMatrix.col).IsCircuit C := by
    rwa [← hEq]
  let M := vectorMatroid (K := ZMod 2) Set.univ
    Set.finite_univ r10BinaryMatrix.col
  let s := (M.ground_finite.subset hC₂.subset_ground).toFinset
  have hrep : M.Represents (K := ZMod 2) r10BinaryMatrix.col :=
    vectorMatroid_represents _ _ _
  have hsum : ∑ e ∈ s, r10BinaryMatrix.col e = 0 :=
    hrep.binaryCircuit_sum_zero r10BinaryMatrix.col hC₂
  have hzero : (∑ e ∈ s, (1 : ZMod 2)) = 0 := by
    calc
      ∑ e ∈ s, (1 : ZMod 2) =
          ∑ e ∈ s, ∑ i : Fin 5, r10BinaryMatrix i e := by
            simp_rw [r10BinaryMatrix_column_parity]
      _ = ∑ i : Fin 5, ∑ e ∈ s, r10BinaryMatrix i e := by
            rw [Finset.sum_comm]
      _ = ∑ i : Fin 5, (∑ e ∈ s, r10BinaryMatrix.col e) i := by
            simp [Matrix.col_apply, Finset.sum_apply]
      _ = 0 := by rw [hsum]; simp
  have hmod : (s.card : ZMod 2) = 0 := by simpa using hzero
  have hcard : s.card = C.ncard := by
    let hfin : C.Finite := M.ground_finite.subset hC₂.subset_ground
    simpa [s] using (Set.ncard_eq_toFinset_card C hfin).symm
  intro hthree
  rw [hcard, hthree] at hmod
  exact (by decide : (3 : ZMod 2) ≠ 0) hmod

end Matroid
