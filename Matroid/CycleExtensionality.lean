import Matroid.Cycles
import Mathlib.Combinatorics.Matroid.Circuit

/-! Recovering a matroid from the manuscript's finite disjoint-circuit cycles. -/

namespace Matroid

/-- Circuits are exactly the minimal nonempty members of the manuscript's
cycle family. This permits a cycle-specified sum to inherit circuit facts. -/
theorem isCircuit_iff_minimal_nonempty_cycle {α : Type*}
    {M : Matroid α} {C : Set α} :
    M.IsCircuit C ↔
      M.IsCircuitUnion C ∧ C.Nonempty ∧
      ∀ D : Set α, M.IsCircuitUnion D → D.Nonempty → D ⊆ C → C ⊆ D := by
  constructor
  · intro hC
    refine ⟨hC.isCircuitUnion, hC.nonempty, ?_⟩
    intro D hD hDne hDC
    obtain ⟨Cs, hCs, _, hUnion⟩ := hD
    have hCsne : Cs.Nonempty := by
      by_contra hn
      have hempty : Cs = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      have hDempty : D = ∅ := by simpa [hempty] using hUnion
      obtain ⟨x, hx⟩ := hDne
      simp [hDempty] at hx
    obtain ⟨E, hECs⟩ := hCsne
    have hE : M.IsCircuit E := hCs E hECs
    have hED : E ⊆ D := by
      rw [hUnion]
      intro x hx
      exact Set.mem_sUnion.mpr ⟨E, by simpa using hECs, hx⟩
    have hEq : E = C := hC.eq_of_not_indep_subset hE.not_indep (hED.trans hDC)
    exact hEq ▸ hED
  · rintro ⟨⟨Cs, hCs, _, hUnion⟩, hCne, hmin⟩
    have hCsne : Cs.Nonempty := by
      by_contra hn
      have hempty : Cs = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      have hCempty : C = ∅ := by simpa [hempty] using hUnion
      obtain ⟨x, hx⟩ := hCne
      simp [hCempty] at hx
    obtain ⟨E, hECs⟩ := hCsne
    have hE : M.IsCircuit E := hCs E hECs
    have hEC : E ⊆ C := by
      rw [hUnion]
      intro x hx
      exact Set.mem_sUnion.mpr ⟨E, by simpa using hECs, hx⟩
    have hCE : C ⊆ E := hmin E hE.isCircuitUnion hE.nonempty hEC
    have hEq : C = E := Set.Subset.antisymm hCE hEC
    exact hEq ▸ hE

/-- Matroids with the same labeled ground and the same manuscript cycles
are equal, without assuming a binary representation. -/
theorem ext_isCircuitUnion {α : Type*} {M N : Matroid α}
    (hE : M.E = N.E)
    (h : ∀ X : Set α, M.IsCircuitUnion X ↔ N.IsCircuitUnion X) : M = N := by
  apply ext_isCircuit hE
  intro C _
  rw [isCircuit_iff_minimal_nonempty_cycle,
      isCircuit_iff_minimal_nonempty_cycle]
  constructor
  · rintro ⟨hC, hne, hmin⟩
    refine ⟨(h C).mp hC, hne, ?_⟩
    intro D hD hDne hDC
    exact hmin D ((h D).mpr hD) hDne hDC
  · rintro ⟨hC, hne, hmin⟩
    refine ⟨(h C).mpr hC, hne, ?_⟩
    intro D hD hDne hDC
    exact hmin D ((h D).mp hD) hDne hDC

end Matroid
