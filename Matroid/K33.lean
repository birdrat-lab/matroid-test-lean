import Matroid.Graphic

/-! The nine-edge complete bipartite graph K3,3 with separate edge labels. -/

namespace Matroid.K33

abbrev Vertex := Fin 3 ⊕ Fin 3
abbrev Edge := Fin 3 × Fin 3

def ends (e : Edge) : Vertex × Vertex := (Sum.inl e.1, Sum.inr e.2)

def graph : Graph Vertex Edge where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink e u v := (u, v) = ends e ∨ (v, u) = ends e
  isLink_symm := by simp [symm_def, or_comm]
  eq_or_eq_of_isLink_of_isLink := by
    intro e x y v w hxy hvw
    rcases hxy with hxy | hxy <;> rcases hvw with hvw | hvw
    · exact Or.inl ((Prod.mk.inj (hxy.trans hvw.symm)).1)
    · exact Or.inr ((Prod.mk.inj (hxy.trans hvw.symm)).1)
    · exact Or.inr ((Prod.mk.inj (hxy.trans hvw.symm)).2)
    · exact Or.inl ((Prod.mk.inj (hxy.trans hvw.symm)).2)
  edge_mem_iff_exists_isLink := by
    intro e
    constructor
    · intro _
      exact ⟨(ends e).1, (ends e).2, Or.inl rfl⟩
    · simp

theorem edge_count : Fintype.card Edge = 9 := by decide

@[simp] theorem graph_edgeSet : graph.edgeSet = Set.univ := rfl

noncomputable def cycleMatroid : Matroid Edge :=
  Matroid.graphic graph Set.finite_univ

@[simp] theorem cycleMatroid_ground : cycleMatroid.E = Set.univ := by
  simpa [cycleMatroid] using Matroid.graphic_ground graph Set.finite_univ

noncomputable def bondMatroid : Matroid Edge := cycleMatroid✶

end Matroid.K33
