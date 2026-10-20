import Matroid.Cycles
import Mathlib.Combinatorics.Matroid.Map

/-! Relabeling bridge needed by the two-element-circuit attachment. -/

namespace Matroid

theorem mapEquiv_isCircuit_iff {α β : Type*} (M : Matroid α)
    (f : α ≃ β) (C : Set β) :
    (M.mapEquiv f).IsCircuit C ↔ M.IsCircuit (f.symm '' C) := by
  constructor
  · intro hC
    apply (M.isCircuit_iff).2
    refine ⟨(M.mapEquiv_dep_iff).mp hC.dep, ?_⟩
    intro D hD hDsub
    have hDdep : (M.mapEquiv f).Dep (f '' D) := by
      simpa using hD
    have hDsub' : f '' D ⊆ C := by
      calc
        f '' D ⊆ f '' (f.symm '' C) := Set.image_mono hDsub
        _ = C := f.image_symm_image C
    have hEq := hC.eq_of_dep_subset hDdep hDsub'
    have hEq' := congrArg (fun S : Set β => f.symm '' S) hEq
    simpa using hEq'
  · intro hC
    apply ((M.mapEquiv f).isCircuit_iff).2
    refine ⟨(M.mapEquiv_dep_iff).2 hC.dep, ?_⟩
    intro D hD hDsub
    have hDdep : M.Dep (f.symm '' D) := (M.mapEquiv_dep_iff).mp hD
    have hDsub' : f.symm '' D ⊆ f.symm '' C := Set.image_mono hDsub
    have hEq := hC.eq_of_dep_subset hDdep hDsub'
    exact f.symm.injective.image_injective hEq

/-- A bijective relabeling transports the manuscript's finite disjoint
circuit unions. This construction is independent of representability. -/
private theorem circuitUnion_image_of_circuit_iff {α β : Type*}
    {M : Matroid α} {N : Matroid β} (f : α ≃ β)
    (hC : ∀ C : Set α, M.IsCircuit C ↔ N.IsCircuit (f '' C))
    {X : Set α} (hX : M.IsCircuitUnion X) :
    N.IsCircuitUnion (f '' X) := by
  obtain ⟨Cs, hCs, hdisj, hUnion⟩ := hX
  refine ⟨Cs.image (fun C => f '' C), ?_, ?_, ?_⟩
  · intro D hD
    obtain ⟨C, hCmem, rfl⟩ := Finset.mem_image.mp hD
    exact (hC C).mp (hCs C hCmem)
  · intro D hD F hF hne
    obtain ⟨C, hCmem, rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨E, hEmem, rfl⟩ := Finset.mem_image.mp hF
    apply Set.disjoint_image_of_injective f.injective
    apply hdisj C hCmem E hEmem
    intro hCE
    exact hne (congrArg (fun S : Set α => f '' S) hCE)
  · rw [hUnion]
    simp only [Set.image_sUnion, Finset.coe_image]

theorem mapEquiv_isCircuitUnion_iff {α β : Type*} (M : Matroid α)
    (f : α ≃ β) (X : Set β) :
    (M.mapEquiv f).IsCircuitUnion X ↔
      M.IsCircuitUnion (f.symm '' X) := by
  constructor
  · intro hX
    exact circuitUnion_image_of_circuit_iff f.symm
      (fun C => mapEquiv_isCircuit_iff M f C) hX
  · intro hX
    have hC : ∀ C : Set α,
        M.IsCircuit C ↔ (M.mapEquiv f).IsCircuit (f '' C) := by
      intro C
      simpa using (mapEquiv_isCircuit_iff M f (f '' C)).symm
    have h := circuitUnion_image_of_circuit_iff f hC hX
    simpa using h

end Matroid
