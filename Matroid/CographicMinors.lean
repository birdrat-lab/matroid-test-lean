import Matroid.GraphicMinors

/-! Cographic minor closure through the dual of labeled graphic minors. -/

namespace Matroid

/-- A cographic matroid has a finite graph realization on its exact edge
labels. The witness vertex type is allowed to change under contraction. -/
def IsCographic.{u,v} {β : Type v} (M : Matroid β) : Prop :=
  ∃ (α : Type u) (G : Graph α β) (hE : G.edgeSet.Finite), M = cographic G hE

theorem isCographic_cographic {α : Type u} {β : Type v}
    (G : Graph α β) (hE : G.edgeSet.Finite) :
    (cographic G hE).IsCographic.{u,v} :=
  ⟨α, G, hE, rfl⟩

theorem isCographic_iff_dual_isGraphic {β : Type v} (M : Matroid β) :
    M.IsCographic.{u,v} ↔ M✶.IsGraphic.{u,v} := by
  constructor
  · rintro ⟨α, G, hE, rfl⟩
    simpa [cographic] using isGraphic_graphic G hE
  · rintro ⟨α, G, hE, hEq⟩
    refine ⟨α, G, hE, ?_⟩
    have h := congrArg Matroid.dual hEq
    simpa [cographic] using h

private theorem dual_isMinor {β : Type v} {M N : Matroid β}
    (hNM : N ≤m M) : N✶ ≤m M✶ := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hNM.exists_eq_contract_delete_disjoint
  refine ⟨D, C, ?_⟩
  rw [M.dual_contract_delete]
  exact ((M✶).contract_delete_comm hCD.symm).symm

/-- N175: all minors of a finite labeled cographic matroid remain
cographic on the surviving original edge labels. -/
theorem IsCographic.minor {β : Type v} {M N : Matroid β}
    (hM : M.IsCographic.{u,v}) (hNM : N ≤m M) :
    N.IsCographic.{u,v} := by
  apply (isCographic_iff_dual_isGraphic N).2
  exact ((isCographic_iff_dual_isGraphic M).1 hM).minor (dual_isMinor hNM)

end Matroid
