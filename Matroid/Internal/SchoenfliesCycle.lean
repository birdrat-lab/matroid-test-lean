import Matroid.Internal.CycleFaceBoundary
import Matroid.Internal.AmbientEmbedding
import Schoenflies.JordanSchoenflies

/-! # Ambient standardization of a drawn graph cycle

The external relative Schoenflies theorem carries every labeled graph cycle
onto the standard square by a homeomorphism of the whole plane. The graph
cycle and its edge paths retain their original hypotheses and labels.
-/

open Set unitInterval

theorem JordanPath.isJordanCurve_of_sphere_trace
    (r : Metric.sphere (0 : JordanCurve.Plane) 1 → Schoenflies.Plane)
    (hc : Continuous r) (hi : Function.Injective r) :
    Schoenflies.IsJordanCurve (Set.range r) := by
  let E : AddCircle (1 : ℝ) ≃ₜ Metric.sphere (0 : JordanCurve.Plane) 1 :=
    (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).trans
      JordanCurve.Arcs.circleHomeoSphere
  let f : ℝ → Schoenflies.Plane := fun t => r (E (t : AddCircle (1 : ℝ)))
  refine ⟨f, ⟨?_, ?_, ?_⟩, ?_⟩
  · have hf : Continuous f := hc.comp (E.continuous.comp (by fun_prop))
    exact hf.continuousOn
  · dsimp [f]
    simp only [AddCircle.coe_period]
  · intro s hs t ht heq
    have hcoe : (s : AddCircle (1 : ℝ)) = (t : AddCircle (1 : ℝ)) :=
      E.injective (hi heq)
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := (0 : ℝ))
      (by simpa using hs) (by simpa using ht)).mp hcoe
  · ext z
    constructor
    · rintro ⟨t, _, rfl⟩
      exact ⟨E (t : AddCircle (1 : ℝ)), rfl⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨a, ha⟩ := E.surjective x
      let t := (AddCircle.equivIco (1 : ℝ) 0) a
      have ht : (t : ℝ) ∈ I :=
        ⟨t.property.1, le_of_lt (by simpa using t.property.2)⟩
      refine ⟨t, ht, ?_⟩
      have hcoe : ((t : ℝ) : AddCircle (1 : ℝ)) = a := AddCircle.coe_equivIco
      dsimp only [f]
      rw [hcoe, ha]

namespace Graph
variable {α β : Type*} {G : Graph α β}

/-- Coordinate identification with the plane in the imported Schoenflies theorem. -/
noncomputable def schoenfliesPlaneHomeomorph : (ℝ × ℝ) ≃ₜ Schoenflies.Plane :=
  (Homeomorph.finTwoArrow (X := ℝ)).symm.trans
    (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.symm

theorem PlaneEmbedding.graphCycle_isJordanCurve
    (P : PlaneEmbedding G) (E : (ℝ × ℝ) ≃ₜ Schoenflies.Plane)
    {C : Set β} (hC : G.IsGraphCycle C) :
    Schoenflies.IsJordanCurve (E '' P.edgeSupport C) := by
  obtain ⟨r, hc, hi, hr⟩ := P.graphCycle_hasJordanTrace hC
  rw [← hr, ← Set.range_comp]
  exact JordanPath.isJordanCurve_of_sphere_trace (E ∘ r)
    (E.continuous.comp hc) (E.injective.comp hi)

/-- A cycle in the actual drawing can be carried to the standard square by an
ambient homeomorphism, with no polygonality assumption on its edge paths. -/
theorem PlaneEmbedding.graphCycle_hasAmbientModelCurve
    (P : PlaneEmbedding G) {C : Set β} (hC : G.IsGraphCycle C) :
    ∃ F : (ℝ × ℝ) ≃ₜ Schoenflies.Plane,
      F '' P.edgeSupport C = Schoenflies.modelCurve := by
  let E := schoenfliesPlaneHomeomorph
  have hj := P.graphCycle_isJordanCurve E hC
  obtain ⟨e⟩ := hj.homeomorph_modelCurve
  obtain ⟨H, hH⟩ := Schoenflies.jordan_schoenflies_of_homeomorph hj
    Schoenflies.isJordanCurve_modelCurve e
  refine ⟨E.trans H, ?_⟩
  change (fun x => H (E x)) '' P.edgeSupport C = Schoenflies.modelCurve
  rw [← Set.image_image]
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [hH ⟨x, hx⟩]
    exact (e ⟨x, hx⟩).2
  · intro hz
    obtain ⟨x, hx⟩ := e.surjective ⟨z, hz⟩
    refine ⟨x.1, x.2, ?_⟩
    rw [hH x]
    exact congrArg Subtype.val hx

/-- Relative Schoenflies can also send a specified point of a drawn cycle to
the midpoint of the model square's top edge. This avoids exceptional corner
cases when identifying the two local faces at an edge-interior point. -/
theorem PlaneEmbedding.graphCycle_hasAmbientModelCurve_at
    (P : PlaneEmbedding G) {C : Set β} (hC : G.IsGraphCycle C)
    (x : ℝ × ℝ) (hx : x ∈ P.edgeSupport C) :
    ∃ F : (ℝ × ℝ) ≃ₜ Schoenflies.Plane,
      F '' P.edgeSupport C = Schoenflies.modelCurve ∧ F x = Schoenflies.Plane.mk 0 1 := by
  let E := schoenfliesPlaneHomeomorph
  obtain ⟨r, hc, hi, hr⟩ := P.graphCycle_hasJordanTrace hC
  have hRange : Set.range (E ∘ r) = E '' P.edgeSupport C := by
    rw [Set.range_comp, hr]
  let A : AddCircle (1 : ℝ) ≃ₜ Metric.sphere (0 : JordanCurve.Plane) 1 :=
    (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).trans
      JordanCurve.Arcs.circleHomeoSphere
  let q : AddCircle (1 : ℝ) ≃ₜ ↥(E '' P.edgeSupport C) :=
    A.trans ((JordanCurve.jordanCurveHomeo (E ∘ r)
      (E.continuous.comp hc) (E.injective.comp hi)).trans (Homeomorph.setCongr hRange))
  let u : ↥(E '' P.edgeSupport C) := ⟨E x, ⟨x, hx, rfl⟩⟩
  let y : ↥Schoenflies.modelCurve := ⟨Schoenflies.Plane.mk 0 1, by
    norm_num [Schoenflies.modelCurve, Schoenflies.Plane.supNorm]⟩
  obtain ⟨e⟩ := (P.graphCycle_isJordanCurve E hC).homeomorph_modelCurve
  let a := q.symm u
  let b := q.symm (e.symm y)
  let e' := q.symm.trans ((Homeomorph.addLeft (b - a)).trans (q.trans e))
  have hpoint : e' u = y := by
    change e (q ((b - a) + q.symm u)) = y
    have hshift : (b - a) + q.symm u = b := by dsimp [a]; abel
    rw [hshift]
    dsimp only [b]
    rw [q.apply_symm_apply]
    exact e.apply_symm_apply y
  obtain ⟨H, hH⟩ := Schoenflies.jordan_schoenflies_of_homeomorph
    (P.graphCycle_isJordanCurve E hC) Schoenflies.isJordanCurve_modelCurve e'
  refine ⟨E.trans H, ?_, ?_⟩
  · change (fun z => H (E z)) '' P.edgeSupport C = Schoenflies.modelCurve
    rw [← Set.image_image]
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hH ⟨w, hw⟩]
      exact (e' ⟨w, hw⟩).2
    · intro hz
      obtain ⟨w, hw⟩ := e'.surjective ⟨z, hz⟩
      refine ⟨w.1, w.2, ?_⟩
      rw [hH w]
      exact congrArg Subtype.val hw
  · exact (hH u).trans (congrArg Subtype.val hpoint)

/-- Standardize the selected cycle by moving the whole drawing. The generic
`reembedFaceHomeomorph` and `reembed_faceIncident_iff` identify all its faces
and incident edges with the original ones. Other edges need not become polygonal. -/
theorem PlaneEmbedding.graphCycle_hasAmbientModelEmbedding
    (P : PlaneEmbedding G) {C : Set β} (hC : G.IsGraphCycle C) :
    ∃ F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ),
      schoenfliesPlaneHomeomorph '' (P.reembed F).edgeSupport C =
        Schoenflies.modelCurve := by
  obtain ⟨H, hH⟩ := P.graphCycle_hasAmbientModelCurve hC
  let F := H.trans schoenfliesPlaneHomeomorph.symm
  refine ⟨F, ?_⟩
  rw [P.reembed_edgeSupport F, Set.image_image]
  have hcomp : (fun x => schoenfliesPlaneHomeomorph (F x)) = H := by
    funext x
    exact schoenfliesPlaneHomeomorph.apply_symm_apply (H x)
  rw [hcomp]
  exact hH

/-- The support of any chosen subset of a finite drawing's edge labels is compact. -/
theorem PlaneEmbedding.isCompact_edgeSupport
    (P : PlaneEmbedding G) (hE : G.edgeSet.Finite) (C : Set β) :
    IsCompact (P.edgeSupport C) := by
  let _ : _root_.Finite G.EdgeIndex := hE.to_subtype
  exact isCompact_iUnion fun e => isCompact_iUnion fun _ =>
    isCompact_range (P.edgePath e).continuous

/-- At an interior point of a selected edge, the other edges and vertices of
a finite drawing can be excluded by an open neighborhood. For a selected cycle
this makes the full support locally equal to that cycle's support. -/
theorem PlaneEmbedding.edgeInterior_has_support_neighborhood
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    (C : Set β) (e : G.EdgeIndex) (he : (e : β) ∈ C)
    (t : I) (ht : IsInteriorTime t) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ P.edgePath e t ∈ U ∧
      ∀ x ∈ U, (x ∈ P.drawnSet ↔ x ∈ P.edgeSupport C) := by
  let K := P.vertexPoint '' G.vertexSet ∪ P.edgeSupport (G.edgeSet \ C)
  have hK : IsCompact K :=
    (hV.image P.vertexPoint).isCompact.union (P.isCompact_edgeSupport hE _)
  have hnot : P.edgePath e t ∉ K := by
    rintro (⟨v, hv, hval⟩ | hoff)
    · exact P.interior_avoids_vertices e t v ht hv hval.symm
    · simp only [edgeSupport, Set.mem_iUnion] at hoff
      obtain ⟨f, hf, s, hs⟩ := hoff
      have hef : e = f := (P.interior_unique_preimage e f t s ht hs.symm).1
      exact hf.2 (hef ▸ he)
  refine ⟨Kᶜ, hK.isClosed.isOpen_compl, hnot, ?_⟩
  intro x hx
  refine ⟨?_, fun h => P.edgeSupport_subset_drawnSet C h⟩
  rintro (hvertex | hedge)
  · exact False.elim (hx (Or.inl hvertex))
  · obtain ⟨f, s, rfl⟩ := Set.mem_iUnion.mp hedge
    by_cases hf : (f : β) ∈ C
    · simp only [edgeSupport, Set.mem_iUnion]
      exact ⟨f, hf, s, rfl⟩
    · apply False.elim
      apply hx
      refine Or.inr ?_
      simp only [edgeSupport, Set.mem_iUnion]
      exact ⟨f, ⟨f.2, hf⟩, s, rfl⟩

end Graph
