import Matroid.Graphic
import Matroid.Depth6TriangleWeights

/-! The exact six-edge graph and weight indexing for N267. -/

namespace Matroid.K4Triangle

abbrev Vertex := Fin 4
abbrev Edge := Fin 6

/-- Edges 0,1,2 form the common triangle. Edge 3 meets the vertex
opposite 0, edge 4 the vertex opposite 1, and edge 5 the vertex
opposite 2. The new vertex is 3. -/
def ends : Edge → Vertex × Vertex
  | 0 => (1, 2)
  | 1 => (0, 2)
  | 2 => (0, 1)
  | 3 => (0, 3)
  | 4 => (1, 3)
  | _ => (2, 3)

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

@[simp] theorem graph_edgeSet : graph.edgeSet = Set.univ := rfl

noncomputable def cycleMatroid : Matroid Edge :=
  Matroid.graphic graph Set.finite_univ

@[simp] theorem cycleMatroid_ground : cycleMatroid.E = Set.univ := by
  simpa [cycleMatroid] using Matroid.graphic_ground graph Set.finite_univ

/-- The full N266 five-class expression for this exact graphic object.
The polynomial evaluation is the outstanding N267 goal. -/
noncomputable def signature {R : Type*} [CommSemiring R]
    (α₁ α₂ α₃ : R) : R × R × R × R × R :=
  Matroid.weightedTriangleSignature cycleMatroid cycleMatroid.ground_finite
    0 1 2 (fun e => if e = 3 then α₁ else if e = 4 then α₂ else if e = 5 then α₃ else 1)

end Matroid.K4Triangle
