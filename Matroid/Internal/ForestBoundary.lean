import Matroid.Internal.EdgeLocalSides

/-! # Face boundaries separate the retained drawing

Complete local incidence extends a face-partition color over every edge
outside its boundary. This translates the remaining forest-boundary
obligation to connectivity of the complement of an embedded forest.
-/

open Set unitInterval

namespace Graph
variable {α β : Type*} {G : Graph α β}

/-- A nonempty boundary of actual faces separates the plane after retaining
only its labeled edges and the original vertices. This uses the checked local
edge models, not a new forest-complement connectivity theorem. -/
theorem PlaneEmbedding.faceBoundary_complement_not_isPreconnected
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    (sides : G.EdgeIndex → P.Face × P.Face)
    (hcomplete : ∀ e f, P.FaceIncident e f → f = (sides e).1 ∨ f = (sides e).2)
    (S : Set P.Face) (hS : (P.faceBoundary sides S).Nonempty) :
    ¬ IsPreconnected (P.vertexPoint '' G.vertexSet ∪
      P.edgeSupport (P.faceBoundary sides S))ᶜ := by
  classical
  let A : Set (ℝ × ℝ) := {z | ∃ f ∈ S, z ∈ P.facePoints f}
  let B : Set (ℝ × ℝ) := {z | ∃ f ∉ S, z ∈ P.facePoints f}
  have hAB : Disjoint A B := by
    apply Set.disjoint_left.mpr
    rintro z ⟨f, hfS, hzf⟩ ⟨g, hgS, hzg⟩
    obtain ⟨hzD, hzf⟩ := hzf
    obtain ⟨_, hzg⟩ := hzg
    exact hgS (hzf.symm.trans hzg ▸ hfS)
  have hAD : A ⊆ P.drawnSetᶜ := by
    rintro z ⟨f, _, hz⟩
    exact hz.1
  have hBD : B ⊆ P.drawnSetᶜ := by
    rintro z ⟨f, _, hz⟩
    exact hz.1
  have hface : ∀ z (hz : z ∉ P.drawnSet),
      z ∈ P.facePoints (ConnectedComponents.mk ⟨z, hz⟩) := fun z hz => ⟨hz, rfl⟩
  have hcover : ∀ z, z ∉ P.drawnSet → z ∈ A ∨ z ∈ B := by
    intro z hz
    by_cases hf : (ConnectedComponents.mk ⟨z, hz⟩ : P.Face) ∈ S
    · exact Or.inl ⟨_, hf, hface z hz⟩
    · exact Or.inr ⟨_, hf, hface z hz⟩
  have hlocal : ∀ x ∈ (P.vertexPoint '' G.vertexSet ∪
      P.edgeSupport (P.faceBoundary sides S))ᶜ,
      ∃ U : Set (ℝ × ℝ), IsOpen U ∧ x ∈ U ∧
        ((∀ z ∈ U, z ∉ P.drawnSet → z ∈ A) ∨
          (∀ z ∈ U, z ∉ P.drawnSet → z ∈ B)) := by
    intro x hx
    by_cases hxD : x ∈ P.drawnSet
    · rcases hxD with hxV | hxE
      · exact False.elim (hx (Or.inl hxV))
      · obtain ⟨e, t, htx⟩ := Set.mem_iUnion.mp hxE
        have ht : IsInteriorTime t := by
          constructor
          · apply lt_of_le_of_ne t.2.1
            intro ht0
            have ht0' : t = 0 := Subtype.ext ht0.symm
            have hxV : x ∈ P.vertexPoint '' G.vertexSet := by
              rw [← htx, ht0', Path.source]
              exact ⟨_, G.left_mem_of_isLink (P.ends_valid e), rfl⟩
            exact hx (Or.inl hxV)
          · apply lt_of_le_of_ne t.2.2
            intro ht1
            have ht1' : t = 1 := Subtype.ext ht1
            have hxV : x ∈ P.vertexPoint '' G.vertexSet := by
              rw [← htx, ht1', Path.target]
              exact ⟨_, G.left_mem_of_isLink (P.ends_valid e).symm, rfl⟩
            exact hx (Or.inl hxV)
        have heD : (e : β) ∉ P.faceBoundary sides S := by
          intro he
          apply hx
          right
          simp only [PlaneEmbedding.edgeSupport, Set.mem_iUnion]
          exact ⟨e, he, t, htx⟩
        have hsides : (sides e).1 ∈ S ↔ (sides e).2 ∈ S := by
          apply iff_of_eq
          by_contra hne
          exact heD ⟨e.2, hne⟩
        obtain ⟨U, f, g, hU, htU, happroach, hcompleteU⟩ :=
          P.edge_local_faces hV hE e t ht
        have hf : P.FaceIncident e f := ⟨t, ht, (happroach t htU).1⟩
        have hg : P.FaceIncident e g := ⟨t, ht, (happroach t htU).2⟩
        have hcolor : ∀ k, P.FaceIncident e k → (k ∈ S ↔ (sides e).1 ∈ S) := by
          intro k hk
          rcases hcomplete e k hk with rfl | rfl
          · rfl
          · exact hsides.symm
        refine ⟨U, hU, htx ▸ htU, ?_⟩
        by_cases heS : (sides e).1 ∈ S
        · left
          intro z hz hzD
          have hp := hcompleteU z hz (ConnectedComponents.mk ⟨z, hzD⟩)
            (subset_closure (hface z hzD))
          refine ⟨_, ?_, hface z hzD⟩
          rcases hp with hp | hp
          · rw [hp]; exact (hcolor f hf).mpr heS
          · rw [hp]; exact (hcolor g hg).mpr heS
        · right
          intro z hz hzD
          have hp := hcompleteU z hz (ConnectedComponents.mk ⟨z, hzD⟩)
            (subset_closure (hface z hzD))
          refine ⟨_, ?_, hface z hzD⟩
          rcases hp with hp | hp
          · rw [hp]; exact fun h => heS ((hcolor f hf).mp h)
          · rw [hp]; exact fun h => heS ((hcolor g hg).mp h)
    · let f : P.Face := ConnectedComponents.mk ⟨x, hxD⟩
      refine ⟨P.facePoints f, P.isOpen_facePoints hV hE f, hface x hxD, ?_⟩
      by_cases hfS : f ∈ S
      · exact Or.inl (fun z hz _ => ⟨f, hfS, hz⟩)
      · exact Or.inr (fun z hz _ => ⟨f, hfS, hz⟩)
  have hlocalClosure : ∀ x ∈ (P.vertexPoint '' G.vertexSet ∪
      P.edgeSupport (P.faceBoundary sides S))ᶜ,
      ∃ U : Set (ℝ × ℝ), IsOpen U ∧ x ∈ U ∧
        (U ⊆ closure A ∨ U ⊆ (closure A)ᶜ) := by
    intro x hx
    obtain ⟨U, hU, hxU, hcolor⟩ := hlocal x hx
    refine ⟨U, hU, hxU, ?_⟩
    rcases hcolor with hcolor | hcolor
    · left
      intro z hz
      apply mem_closure_iff.mpr
      intro W hW hzW
      obtain ⟨w, hwU, hwD⟩ := (P.dense_compl_drawnSet hV hE).inter_open_nonempty
        (U ∩ W) (hU.inter hW) ⟨z, hz, hzW⟩
      exact ⟨w, hwU.2, hcolor w hwU.1 hwD⟩
    · right
      intro z hz hcl
      obtain ⟨w, hwU, hwA⟩ := mem_closure_iff.mp hcl U hU hz
      exact Set.disjoint_left.mp hAB hwA (hcolor w hwU (hAD hwA))
  let T := (P.vertexPoint '' G.vertexSet ∪ P.edgeSupport (P.faceBoundary sides S))ᶜ
  let K : Set T := Subtype.val ⁻¹' closure A
  have hKclosed : IsClosed K := isClosed_closure.preimage continuous_subtype_val
  have hKopen : IsOpen K := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨U, hU, hxU, hsub | hsub⟩ := hlocalClosure x.1 x.2
    · exact Filter.mem_of_superset
        ((hU.preimage continuous_subtype_val).mem_nhds hxU) (fun z hz => hsub hz)
    · exact False.elim (hsub hxU hx)
  have hRsub : P.vertexPoint '' G.vertexSet ∪ P.edgeSupport (P.faceBoundary sides S) ⊆
      P.drawnSet := Set.union_subset Set.subset_union_left
        (P.edgeSupport_subset_drawnSet _)
  have hsample : ∀ f : P.Face, ∃ x : T,
      (f ∈ S → x ∈ K) ∧ (f ∉ S → x ∉ K) := by
    intro f
    obtain ⟨p, hp⟩ := ConnectedComponents.surjective_coe f
    have hpf : p.1 ∈ P.facePoints f := ⟨p.2, hp⟩
    let x : T := ⟨p.1, fun h => p.2 (hRsub h)⟩
    refine ⟨x, ?_, ?_⟩
    · intro hfS
      exact subset_closure ⟨f, hfS, hpf⟩
    · intro hfS hxK
      obtain ⟨z, hzf, hzA⟩ := mem_closure_iff.mp hxK (P.facePoints f)
        (P.isOpen_facePoints hV hE f) hpf
      exact Set.disjoint_left.mp hAB hzA ⟨f, hfS, hzf⟩
  obtain ⟨e, he, hdiff⟩ := hS
  have hsplit : ((sides ⟨e, he⟩).1 ∈ S ∧ (sides ⟨e, he⟩).2 ∉ S) ∨
      ((sides ⟨e, he⟩).2 ∈ S ∧ (sides ⟨e, he⟩).1 ∉ S) := by
    by_cases h₁ : (sides ⟨e, he⟩).1 ∈ S <;>
      by_cases h₂ : (sides ⟨e, he⟩).2 ∈ S <;> simp_all
  have hKne : K.Nonempty ∧ Kᶜ.Nonempty := by
    rcases hsplit with ⟨hf, hg⟩ | ⟨hg, hf⟩
    · obtain ⟨x, hx, _⟩ := hsample (sides ⟨e, he⟩).1
      obtain ⟨y, _, hy⟩ := hsample (sides ⟨e, he⟩).2
      exact ⟨⟨x, hx hf⟩, ⟨y, hy hg⟩⟩
    · obtain ⟨x, hx, _⟩ := hsample (sides ⟨e, he⟩).2
      obtain ⟨y, _, hy⟩ := hsample (sides ⟨e, he⟩).1
      exact ⟨⟨x, hx hg⟩, ⟨y, hy hf⟩⟩
  intro hconn
  let _ : PreconnectedSpace T := isPreconnected_iff_preconnectedSpace.mp hconn
  have hKuniv := IsClopen.eq_univ ⟨hKclosed, hKopen⟩ hKne.1
  simpa [hKuniv] using hKne.2

/-- Connectivity of every retained embedded forest is sufficient for N268.
Complete incidence and both cycle-boundary directions otherwise follow from
the already checked bridges. -/
theorem PlaneEmbedding.hasCycleBondFaceDual_of_forest_complement
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    (hforest : ∀ D : Set β, D ⊆ G.edgeSet → G.IsForestIn D →
      IsPreconnected (P.vertexPoint '' G.vertexSet ∪ P.edgeSupport D)ᶜ) :
    P.HasCycleBondFaceDual := by
  obtain ⟨sides, hinc, hcomplete⟩ := P.exists_complete_incidence hV hE
  apply P.hasCycleBondFaceDual_of_complete_incidence_and_forestBoundary hV hE sides
    hinc hcomplete
  intro S hS
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hne
  exact P.faceBoundary_complement_not_isPreconnected hV hE sides hcomplete S hne
    (hforest _ (P.faceBoundary_subset_edgeSet sides S) hS)

end Graph
