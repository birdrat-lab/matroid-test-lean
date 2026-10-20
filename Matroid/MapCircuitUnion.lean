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

end Matroid
