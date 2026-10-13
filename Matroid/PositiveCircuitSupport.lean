import Matroid.Depth6Support
import Mathlib.Combinatorics.Matroid.Circuit

/-! The minimum positive target support is a minimum target-circuit size. -/

namespace Matroid

/-- Circuit version of the manuscript's positive support quantity. -/
noncomputable def positiveCircuitSupport {α : Type*} (M : Matroid α)
    (τ : α) (A : Set α) : ℕ :=
  sInf {n : ℕ | ∃ C : Set α, M.IsCircuit C ∧ τ ∈ C ∧
    C \ {τ} ⊆ A ∧ C.ncard - 1 = n}

/-- N106: for an accepted input, least spanning-response support is exactly
least target-circuit size minus one. The target is excluded from availability. -/
theorem positiveSpanningSupport_eq_circuitSupport {α : Type*}
    (M : Matroid α) [M.Finite] (τ : α) (A : Set α)
    (hτ : τ ∈ M.E) (hA : A ⊆ M.E \ {τ})
    (hpos : τ ∈ M.closure A) :
    positiveSpanningSupport M τ A = positiveCircuitSupport M τ A := by
  let S : Set ℕ := {n | ∃ B : Set α, B ⊆ A ∧ τ ∈ M.closure B ∧ B.ncard = n}
  let T : Set ℕ := {n | ∃ C : Set α, M.IsCircuit C ∧ τ ∈ C ∧
    C \ {τ} ⊆ A ∧ C.ncard - 1 = n}
  have hτA : τ ∉ A := fun h => (hA h).2 (by simp)
  have hS : S.Nonempty := ⟨A.ncard, A, Set.Subset.rfl, hpos, rfl⟩
  obtain ⟨C₀, hC₀insert, hC₀, hτC₀⟩ :=
    M.exists_isCircuit_of_mem_closure hpos hτA
  have hC₀A : C₀ \ {τ} ⊆ A := by
    intro x hx
    rcases hC₀insert hx.1 with h | h
    · exact False.elim (hx.2 (by simpa using h))
    · exact h
  have hT : T.Nonempty := ⟨C₀.ncard - 1, C₀, hC₀, hτC₀, hC₀A, rfl⟩
  change sInf S = sInf T
  apply le_antisymm
  · obtain ⟨C, hC, hτC, hCA, hcard⟩ := Nat.sInf_mem hT
    have hCfin : C.Finite := M.ground_finite.subset hC.subset_ground
    have hCdel : C \ {τ} ⊆ M.E := hCA.trans (hA.trans Set.sdiff_subset)
    have hcl : τ ∈ M.closure (C \ {τ}) :=
      hC.mem_closure_sdiff_singleton_of_mem hτC
    have hmem : (C \ {τ}).ncard ∈ S := ⟨C \ {τ}, hCA, hcl, rfl⟩
    have hcard' : (C \ {τ}).ncard = C.ncard - 1 :=
      Set.ncard_sdiff_singleton_of_mem hτC
    exact (Nat.sInf_le hmem).trans (by rw [hcard', hcard])
  · obtain ⟨B, hBA, hcl, hcard⟩ := Nat.sInf_mem hS
    have hτB : τ ∉ B := fun h => hτA (hBA h)
    obtain ⟨C, hCB, hC, hτC⟩ :=
      M.exists_isCircuit_of_mem_closure hcl hτB
    have hCfin : C.Finite := M.ground_finite.subset hC.subset_ground
    have hCBA : C \ {τ} ⊆ B := by
      intro x hx
      rcases hCB hx.1 with h | h
      · exact False.elim (hx.2 (by simpa using h))
      · exact h
    have hmem : C.ncard - 1 ∈ T :=
      ⟨C, hC, hτC, hCBA.trans hBA, rfl⟩
    have hcard' : (C \ {τ}).ncard = C.ncard - 1 :=
      Set.ncard_sdiff_singleton_of_mem hτC
    have hle : C.ncard - 1 ≤ B.ncard := by
      rw [← hcard']
      exact Set.ncard_le_ncard hCBA
        ((M.ground_finite.subset (hBA.trans (hA.trans Set.sdiff_subset))))
    exact (Nat.sInf_le hmem).trans (hcard ▸ hle)

end Matroid
