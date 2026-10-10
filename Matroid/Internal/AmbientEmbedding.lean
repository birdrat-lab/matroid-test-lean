import Matroid.PlanarDuality

/-! # Transport of a labeled drawing by an ambient homeomorphism

An ambient change of coordinates transports the full drawing, its complementary
faces, and edge incidence. This is the bridge needed to use relative Schoenflies
on a cycle without replacing the original faces by unrelated redrawn faces.
-/

open Set unitInterval

namespace Graph
variable {α β : Type*} {G : Graph α β}

instance PlaneEmbedding.faceTopologicalSpace (P : PlaneEmbedding G) :
    TopologicalSpace P.Face :=
  inferInstanceAs (TopologicalSpace
    (ConnectedComponents {x : ℝ × ℝ // x ∉ P.drawnSet}))

/-- Apply an ambient homeomorphism to every vertex and labeled edge path. -/
def PlaneEmbedding.reembed (P : PlaneEmbedding G) (F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) :
    PlaneEmbedding G where
  ends := P.ends
  ends_valid := P.ends_valid
  vertexPoint := F ∘ P.vertexPoint
  vertex_injective := fun _ hx _ hy h => P.vertex_injective hx hy (F.injective h)
  edgePath e := (P.edgePath e).map F.continuous
  interior_injective := fun e f t s ht hs h =>
    P.interior_injective e f t s ht hs (F.injective h)
  interior_avoids_vertices := fun e t v ht hv h =>
    P.interior_avoids_vertices e t v ht hv (F.injective h)

@[simp] theorem PlaneEmbedding.reembed_edgePath
    (P : PlaneEmbedding G) (F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) (e : G.EdgeIndex) (t : I) :
    (P.reembed F).edgePath e t = F (P.edgePath e t) := rfl

theorem PlaneEmbedding.reembed_drawnSet
    (P : PlaneEmbedding G) (F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) :
    (P.reembed F).drawnSet = F '' P.drawnSet := by
  change (F ∘ P.vertexPoint) '' G.vertexSet ∪
    (⋃ e : G.EdgeIndex, Set.range (F ∘ P.edgePath e)) =
      F '' (P.vertexPoint '' G.vertexSet ∪ ⋃ e : G.EdgeIndex, Set.range (P.edgePath e))
  simp only [Set.range_comp, Set.image_union, Set.image_image, Set.image_iUnion]
  rfl

theorem PlaneEmbedding.reembed_edgeSupport
    (P : PlaneEmbedding G) (F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) (C : Set β) :
    (P.reembed F).edgeSupport C = F '' P.edgeSupport C := by
  change (⋃ e : G.EdgeIndex, ⋃ (_ : (e : β) ∈ C), Set.range (F ∘ P.edgePath e)) =
    F '' (⋃ e : G.EdgeIndex, ⋃ (_ : (e : β) ∈ C), Set.range (P.edgePath e))
  simp only [Set.range_comp, Set.image_iUnion]

@[simp] theorem PlaneEmbedding.reembed_mem_drawnSet
    (P : PlaneEmbedding G) (F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) (x : ℝ × ℝ) :
    F x ∈ (P.reembed F).drawnSet ↔ x ∈ P.drawnSet := by
  rw [P.reembed_drawnSet F]
  exact F.injective.mem_set_image

/-- The complements of the original and transported full drawings are homeomorphic. -/
def PlaneEmbedding.reembedComplementHomeomorph
    (P : PlaneEmbedding G) (F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) :
    {x : ℝ × ℝ // x ∉ P.drawnSet} ≃ₜ
      {x : ℝ × ℝ // x ∉ (P.reembed F).drawnSet} where
  toFun x := ⟨F x, fun hx => x.2 ((P.reembed_mem_drawnSet F x.1).mp hx)⟩
  invFun x := ⟨F.symm x, fun hx => x.2 (by
    simpa only [F.apply_symm_apply] using
      (P.reembed_mem_drawnSet F (F.symm x.1)).mpr hx)⟩
  left_inv x := Subtype.ext (F.symm_apply_apply x.1)
  right_inv x := Subtype.ext (F.apply_symm_apply x.1)
  continuous_toFun := (F.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (F.symm.continuous.comp continuous_subtype_val).subtype_mk _

private theorem homeomorph_connected_fibers {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (E : X ≃ₜ Y) (y : Y) :
    IsConnected (E ⁻¹' {y}) := by
  have heq : E ⁻¹' {y} = {E.symm y} := by
    ext x
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using
      (E.eq_symm_apply (x := x) (y := y)).symm
  rw [heq]
  exact isConnected_singleton

/-- In particular the actual full-drawing face types, not just cycle sides, correspond. -/
noncomputable def PlaneEmbedding.reembedFaceHomeomorph
    (P : PlaneEmbedding G) (F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) :
    P.Face ≃ₜ (P.reembed F).Face :=
  ((P.reembedComplementHomeomorph F).isQuotientMap.isCoinducing).connectedComponentsHomeomorph
      (homeomorph_connected_fibers (P.reembedComplementHomeomorph F))

@[simp] theorem PlaneEmbedding.reembedFaceHomeomorph_mk
    (P : PlaneEmbedding G) (F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ))
    (x : {x : ℝ × ℝ // x ∉ P.drawnSet}) :
    P.reembedFaceHomeomorph F (ConnectedComponents.mk x) =
      ConnectedComponents.mk (P.reembedComplementHomeomorph F x) := rfl

theorem PlaneEmbedding.reembed_facePoints
    (P : PlaneEmbedding G) (F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) (f : P.Face) :
    (P.reembed F).facePoints (P.reembedFaceHomeomorph F f) = F '' P.facePoints f := by
  ext y
  constructor
  · rintro ⟨hy, hface⟩
    let x := (P.reembedComplementHomeomorph F).symm ⟨y, hy⟩
    refine ⟨x.1, ⟨x.2, ?_⟩, ?_⟩
    · apply (P.reembedFaceHomeomorph F).injective
      rw [P.reembedFaceHomeomorph_mk F]
      change ConnectedComponents.mk ((P.reembedComplementHomeomorph F)
        ((P.reembedComplementHomeomorph F).symm ⟨y, hy⟩)) = _
      simpa only [Homeomorph.apply_symm_apply] using hface
    · exact F.apply_symm_apply y
  · rintro ⟨x, ⟨hx, hface⟩, rfl⟩
    refine ⟨by simpa using hx, ?_⟩
    exact (P.reembedFaceHomeomorph_mk F ⟨x, hx⟩).symm.trans
      (congrArg (P.reembedFaceHomeomorph F) hface)

/-- Incidence is transported in both directions, with the same interior parameter. -/
theorem PlaneEmbedding.reembed_faceIncident_iff
    (P : PlaneEmbedding G) (F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) (e : G.EdgeIndex) (f : P.Face) :
    (P.reembed F).FaceIncident e (P.reembedFaceHomeomorph F f) ↔ P.FaceIncident e f := by
  simp only [FaceIncident, reembed_edgePath, P.reembed_facePoints F, ← F.image_closure]
  simp only [F.injective.mem_set_image]

/-- Transport the endpoints of a proposed dual edge without changing its label. -/
noncomputable def PlaneEmbedding.reembedSides
    (P : PlaneEmbedding G) (F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ))
    (sides : G.EdgeIndex → P.Face × P.Face) :
    G.EdgeIndex → (P.reembed F).Face × (P.reembed F).Face :=
  fun e => (P.reembedFaceHomeomorph F (sides e).1,
    P.reembedFaceHomeomorph F (sides e).2)

theorem PlaneEmbedding.reembed_faceBoundary_preimage
    (P : PlaneEmbedding G) (F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ))
    (sides : G.EdgeIndex → P.Face × P.Face) (S : Set (P.reembed F).Face) :
    (P.reembed F).faceBoundary (P.reembedSides F sides) S =
      P.faceBoundary sides (P.reembedFaceHomeomorph F ⁻¹' S) := rfl

theorem PlaneEmbedding.reembed_faceBoundary_image
    (P : PlaneEmbedding G) (F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ))
    (sides : G.EdgeIndex → P.Face × P.Face) (S : Set P.Face) :
    (P.reembed F).faceBoundary (P.reembedSides F sides)
      (P.reembedFaceHomeomorph F '' S) = P.faceBoundary sides S := by
  rw [P.reembed_faceBoundary_preimage F]
  rw [Set.preimage_image_eq _ (P.reembedFaceHomeomorph F).injective]

theorem PlaneEmbedding.reembed_exists_faceBoundary_iff
    (P : PlaneEmbedding G) (F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ))
    (sides : G.EdgeIndex → P.Face × P.Face) (C : Set β) :
    (∃ S, (P.reembed F).faceBoundary (P.reembedSides F sides) S = C) ↔
      ∃ S, P.faceBoundary sides S = C := by
  constructor
  · rintro ⟨S, h⟩
    exact ⟨P.reembedFaceHomeomorph F ⁻¹' S,
      (P.reembed_faceBoundary_preimage F sides S).symm.trans h⟩
  · rintro ⟨S, h⟩
    exact ⟨P.reembedFaceHomeomorph F '' S,
      (P.reembed_faceBoundary_image F sides S).trans h⟩

theorem PlaneEmbedding.reembed_minimalFaceBoundary_iff
    (P : PlaneEmbedding G) (F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ))
    (sides : G.EdgeIndex → P.Face × P.Face) (C : Set β) :
    (P.reembed F).IsMinimalFaceBoundary (P.reembedSides F sides) C ↔
      P.IsMinimalFaceBoundary sides C := by
  simp only [IsMinimalFaceBoundary, Minimal, P.reembed_exists_faceBoundary_iff F]

/-- N268 for a finite drawing is invariant under ambient changes of coordinates.
This reduction preserves the original face incidence, loops, and all edge labels. -/
theorem PlaneEmbedding.reembed_hasCycleBondFaceDual_iff
    (P : PlaneEmbedding G) (F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) (hE : G.edgeSet.Finite) :
    (P.reembed F).HasCycleBondFaceDual ↔ P.HasCycleBondFaceDual := by
  rw [(P.reembed F).hasCycleBondFaceDual_iff_minimalFaceBoundary hE,
    P.hasCycleBondFaceDual_iff_minimalFaceBoundary hE]
  constructor
  · rintro ⟨sides', hinc, hcycles⟩
    let sides : G.EdgeIndex → P.Face × P.Face := fun e =>
      ((P.reembedFaceHomeomorph F).symm (sides' e).1,
        (P.reembedFaceHomeomorph F).symm (sides' e).2)
    have hsides : P.reembedSides F sides = sides' := by
      funext e
      simp [reembedSides, sides]
    refine ⟨sides, ?_, ?_⟩
    · intro e
      have h := hinc e
      rw [← hsides] at h
      simpa only [reembedSides, P.reembed_faceIncident_iff F] using h
    · intro C
      rw [← P.reembed_minimalFaceBoundary_iff F, hsides]
      exact hcycles C
  · rintro ⟨sides, hinc, hcycles⟩
    refine ⟨P.reembedSides F sides, ?_, ?_⟩
    · intro e
      simpa only [reembedSides, P.reembed_faceIncident_iff F] using hinc e
    · intro C
      rw [P.reembed_minimalFaceBoundary_iff F]
      exact hcycles C

end Graph
