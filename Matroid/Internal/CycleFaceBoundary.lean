import Matroid.Internal.PlaneArcDensity

/-! # Jordan sides and boundaries of full-drawing faces

An edge outside a cycle cannot have incident faces on different Jordan sides.
Consequently, an incident-face assignment that straddles each cycle edge
makes that cycle exactly the boundary of its Jordan-side partition. A complete
pair of incident faces suffices, conditional on finiteness of the full face type.
-/

open Set unitInterval

namespace Graph
variable {α β : Type*} {G : Graph α β}

/-- An edge outside a selected support has its whole interior outside that support. -/
theorem PlaneEmbedding.interior_not_mem_edgeSupport
    (P : PlaneEmbedding G) (C : Set β) (e : G.EdgeIndex) (he : (e : β) ∉ C)
    (t : I) (ht : IsInteriorTime t) : P.edgePath e t ∉ P.edgeSupport C := by
  intro h
  simp only [PlaneEmbedding.edgeSupport, Set.mem_iUnion] at h
  obtain ⟨f, hf, s, hs⟩ := h
  have hef : e = f := (P.interior_unique_preimage e f t s ht hs.symm).1
  exact he (hef ▸ hf)

/-- A full face approaching a point off a cycle has the same Jordan side as that point. -/
theorem PlaneEmbedding.faceMap_edgeSupport_eq_of_mem_closure
    (P : PlaneEmbedding G) {C : Set β} (hC : G.IsGraphCycle C)
    (f : P.Face) (x : ℝ × ℝ) (hx : x ∈ (P.edgeSupport C)ᶜ)
    (hxf : x ∈ closure (P.facePoints f)) :
    P.faceMap_edgeSupport C f = ConnectedComponents.mk ⟨x, hx⟩ := by
  let U := connectedComponentIn (P.edgeSupport C)ᶜ x
  have hUopen : IsOpen U :=
    (P.isClosed_edgeSupport_of_graphCycle hC).isOpen_compl.connectedComponentIn
  obtain ⟨y, hyU, hyf⟩ := mem_closure_iff.mp hxf U hUopen (mem_connectedComponentIn hx)
  obtain ⟨hyD, hyface⟩ := hyf
  rw [← hyface]
  exact P.faceMap_edgeSupport_mk_eq_of_mem_component C x hx y hyD hyU

/-- Interior points of an edge outside a cycle all lie on the same Jordan side. -/
theorem PlaneEmbedding.edge_interior_same_cycleSide
    (P : PlaneEmbedding G) {C : Set β} (e : G.EdgeIndex) (he : (e : β) ∉ C)
    (s t : I) (hs : IsInteriorTime s) (ht : IsInteriorTime t) :
    connectedComponentIn (P.edgeSupport C)ᶜ (P.edgePath e s) =
      connectedComponentIn (P.edgeSupport C)ᶜ (P.edgePath e t) := by
  let A := P.edgePath e '' Set.Ioo (0 : I) 1
  have hA : IsPreconnected A :=
    isPreconnected_Ioo.image _ (P.edgePath e).continuous.continuousOn
  have hAsub : A ⊆ (P.edgeSupport C)ᶜ := by
    rintro x ⟨u, hu, rfl⟩
    exact P.interior_not_mem_edgeSupport C e he u hu
  have hsmem : P.edgePath e s ∈ A := ⟨s, hs, rfl⟩
  have htmem : P.edgePath e t ∈ A := ⟨t, ht, rfl⟩
  exact connectedComponentIn_eq (hA.subset_connectedComponentIn hsmem hAsub htmem)

/-- Any two faces incident with an edge outside a cycle occupy the same side of it. -/
theorem PlaneEmbedding.incidentFaces_same_cycleSide_of_not_mem
    (P : PlaneEmbedding G) {C : Set β} (hC : G.IsGraphCycle C)
    (e : G.EdgeIndex) (he : (e : β) ∉ C)
    (f g : P.Face) (hf : P.FaceIncident e f) (hg : P.FaceIncident e g) :
    P.faceMap_edgeSupport C f = P.faceMap_edgeSupport C g := by
  obtain ⟨s, hs, hsf⟩ := hf
  obtain ⟨t, ht, htg⟩ := hg
  have hsJ := P.interior_not_mem_edgeSupport C e he s hs
  have htJ := P.interior_not_mem_edgeSupport C e he t ht
  rw [P.faceMap_edgeSupport_eq_of_mem_closure hC f _ hsJ hsf,
    P.faceMap_edgeSupport_eq_of_mem_closure hC g _ htJ htg]
  apply ConnectedComponents.coe_eq_coe.mpr
  apply Set.image_injective.mpr Subtype.val_injective
  rw [← connectedComponentIn_eq_image hsJ, ← connectedComponentIn_eq_image htJ]
  exact P.edge_interior_same_cycleSide e he s t hs ht

/-- Partitioning full faces by a Jordan side creates no boundary edge outside the cycle. -/
theorem PlaneEmbedding.faceBoundary_cycleSide_subset
    (P : PlaneEmbedding G) {C : Set β} (hC : G.IsGraphCycle C)
    (sides : G.EdgeIndex → P.Face × P.Face)
    (hinc : ∀ e, P.FaceIncident e (sides e).1 ∧ P.FaceIncident e (sides e).2)
    (a : ConnectedComponents ((P.edgeSupport C)ᶜ : Set (ℝ × ℝ))) :
    P.faceBoundary sides {f | P.faceMap_edgeSupport C f = a} ⊆ C := by
  rintro e ⟨he, hdiff⟩
  by_contra hnot
  have heq := P.incidentFaces_same_cycleSide_of_not_mem hC ⟨e, he⟩ hnot
    _ _ (hinc ⟨e, he⟩).1 (hinc ⟨e, he⟩).2
  apply hdiff
  change (P.faceMap_edgeSupport C (sides ⟨e, he⟩).1 = a) =
    (P.faceMap_edgeSupport C (sides ⟨e, he⟩).2 = a)
  rw [heq]

/-- Opposite-side incidence on the cycle makes its Jordan partition have exactly
that cycle as boundary. -/
theorem PlaneEmbedding.faceBoundary_cycleSide_eq_of_opposite
    (P : PlaneEmbedding G) {C : Set β} (hC : G.IsGraphCycle C)
    (sides : G.EdgeIndex → P.Face × P.Face)
    (hinc : ∀ e, P.FaceIncident e (sides e).1 ∧ P.FaceIncident e (sides e).2)
    (hopposite : ∀ e : G.EdgeIndex, (e : β) ∈ C →
      P.faceMap_edgeSupport C (sides e).1 ≠ P.faceMap_edgeSupport C (sides e).2)
    (a : ConnectedComponents ((P.edgeSupport C)ᶜ : Set (ℝ × ℝ))) :
    P.faceBoundary sides {f | P.faceMap_edgeSupport C f = a} = C := by
  apply Set.Subset.antisymm (P.faceBoundary_cycleSide_subset hC sides hinc a)
  intro e heC
  have he : e ∈ G.edgeSet := hC.1 heC
  refine ⟨he, ?_⟩
  change (P.faceMap_edgeSupport C (sides ⟨e, he⟩).1 = a) ≠
    (P.faceMap_edgeSupport C (sides ⟨e, he⟩).2 = a)
  have hne := hopposite ⟨e, he⟩ heC
  obtain ⟨b, hb, huniq⟩ := (Nat.card_eq_two_iff' a).mp (P.graphCycle_complement_card hC)
  by_cases hleft : P.faceMap_edgeSupport C (sides ⟨e, he⟩).1 = a
  · have hright : P.faceMap_edgeSupport C (sides ⟨e, he⟩).2 ≠ a :=
      fun h => hne (hleft.trans h.symm)
    simp [hleft, hright]
  · have hright : P.faceMap_edgeSupport C (sides ⟨e, he⟩).2 = a := by
      by_contra hn
      exact hne ((huniq _ hleft).trans (huniq _ hn).symm)
    simp [hleft, hright]

/-- A complete pair of incident faces straddles every cycle containing the edge.
Face finiteness is used only to produce the opposite-side incident faces. -/
theorem PlaneEmbedding.faceBoundary_cycleSide_eq_of_complete_incidence
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    (hfaces : Finite P.Face) {C : Set β} (hC : G.IsGraphCycle C)
    (sides : G.EdgeIndex → P.Face × P.Face)
    (hinc : ∀ e, P.FaceIncident e (sides e).1 ∧ P.FaceIncident e (sides e).2)
    (hcomplete : ∀ e f, P.FaceIncident e f → f = (sides e).1 ∨ f = (sides e).2)
    (a : ConnectedComponents ((P.edgeSupport C)ᶜ : Set (ℝ × ℝ))) :
    P.faceBoundary sides {f | P.faceMap_edgeSupport C f = a} = C := by
  apply P.faceBoundary_cycleSide_eq_of_opposite hC sides hinc
  intro e he
  obtain ⟨x, _⟩ := ConnectedComponents.surjective_coe a
  obtain ⟨f, g, _, hf, hg, hfg⟩ :=
    P.graphCycle_exists_two_incidentFaces_of_finite hV hE hC hfaces e he x.1 x.2
  intro heq
  apply hfg
  rcases hcomplete e f hf with rfl | rfl <;>
    rcases hcomplete e g hg with rfl | rfl
  · rfl
  · exact heq
  · exact heq.symm
  · rfl

/-- Once a single complete incident-face assignment is supplied, every primal
cycle is the boundary of its Jordan-side partition in that same face graph. -/
theorem PlaneEmbedding.graphCycles_are_faceBoundaries_of_complete_incidence
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    (hfaces : Finite P.Face)
    (sides : G.EdgeIndex → P.Face × P.Face)
    (hinc : ∀ e, P.FaceIncident e (sides e).1 ∧ P.FaceIncident e (sides e).2)
    (hcomplete : ∀ e f, P.FaceIncident e f → f = (sides e).1 ∨ f = (sides e).2) :
    ∀ C, G.IsGraphCycle C → ∃ S : Set P.Face, P.faceBoundary sides S = C := by
  intro C hC
  obtain ⟨a, _, _, _⟩ := Nat.card_eq_two_iff.mp (P.graphCycle_complement_card hC)
  exact ⟨{f | P.faceMap_edgeSupport C f = a},
    P.faceBoundary_cycleSide_eq_of_complete_incidence hV hE hfaces hC sides hinc hcomplete a⟩

end Graph
