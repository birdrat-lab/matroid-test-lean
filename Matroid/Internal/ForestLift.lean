import Matroid.Internal.ArcBoundary

/-! # Gluing circle lifts over a finite embedded forest

The forest condition supplies independent edge cuts. Their indicator
potentials correct the integer discrepancies between endpoint lifts, so
the imported covering-space path lifts agree at every graph vertex.
-/

open Set unitInterval

namespace Graph

variable {α β : Type*} {G : Graph α β}

/-- Arbitrary additive edge increments integrate to vertex potentials on
a finite forest. The proof uses the already checked isolating-cut
characterization of graphic independence, retaining the edge labels. -/
theorem forest_exists_vertex_potential {K : Type*} [AddCommGroup K]
    (hE : G.edgeSet.Finite) (ends : G.EdgeIndex → α × α)
    (hends : ∀ e : G.EdgeIndex, G.IsLink (e : β) (ends e).1 (ends e).2)
    (D : Set β) (hf : G.IsForestIn D) (w : G.EdgeIndex → K) :
    ∃ p : α → K, ∀ e : G.EdgeIndex, (e : β) ∈ D →
      p (ends e).2 - p (ends e).1 = w e := by
  classical
  let _ : Fintype G.EdgeIndex := hE.fintype
  let A := G.edgeEmbedding ⁻¹' D
  have hind : (G.edgeCutMatroid hE).Indep A :=
    (G.edgeCutMatroid_indep_iff_noEdgeCycle hE A).mpr hf
  have hcuts : ∀ e : A, ∃ S : Set α,
      (ends e).1 ∉ S ∧ (ends e).2 ∈ S ∧
      ∀ f ∈ A, f ≠ e → ((ends f).1 ∈ S ↔ (ends f).2 ∈ S) := by
    intro e
    obtain ⟨C, ⟨S, rfl⟩, hdisj, heC⟩ :=
      (G.edgeCutMatroid_indep_iff hE A).mp hind e e.2
    have hsame : ∀ f ∈ A, f ≠ e → ((ends f).1 ∈ S ↔ (ends f).2 ∈ S) := by
      intro f hf hfe
      have hn : (f : β) ∉ G.edgeCut S := fun h =>
        disjoint_left.mp hdisj ⟨hf, hfe⟩ h
      have h := (hends f).mem_edgeCut_iff (S := S)
      tauto
    rcases (hends e).mem_edgeCut_iff.mp heC with h | h
    · exact ⟨Sᶜ, by simpa using h.1, h.2,
        fun f hf hfe => not_congr (hsame f hf hfe)⟩
    · exact ⟨S, h.2, h.1, hsame⟩
  choose S hS using hcuts
  let q : A → α → K := fun e x => if x ∈ S e then w e else 0
  refine ⟨fun x => ∑ e : A, q e x, ?_⟩
  intro e he
  let e' : A := ⟨e, he⟩
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single e']
  · simp [q, e', (hS e').1, (hS e').2.1]
  · intro f _ hfe
    have hne : e ≠ (f : G.EdgeIndex) := fun h => hfe (Subtype.ext h.symm)
    have h := (hS f).2.2 e he hne
    by_cases hx : (ends e).1 ∈ S f
    · simp [q, hx, h.mp hx]
    · simp [q, hx, mt h.mpr hx]
  · simp

/-- Covering-space lifts of maps on the selected forest edges can be chosen
to agree at every common vertex. Integer endpoint errors are integrated by
the forest's isolating cuts, with no assumption on connectedness or degree. -/
theorem forest_exists_compatible_lifts
    (hE : G.edgeSet.Finite) (ends : G.EdgeIndex → α × α)
    (hends : ∀ e : G.EdgeIndex, G.IsLink (e : β) (ends e).1 (ends e).2)
    (D : Set β) (hf : G.IsForestIn D)
    (v : α → AddCircle (1 : ℝ))
    (c : ∀ e : G.EdgeIndex, (e : β) ∈ D → C(I, AddCircle (1 : ℝ)))
    (hc0 : ∀ e he, c e he 0 = v (ends e).1)
    (hc1 : ∀ e he, c e he 1 = v (ends e).2) :
    ∃ (p : α → ℝ) (l : ∀ e : G.EdgeIndex, (e : β) ∈ D → C(I, ℝ)),
      (∀ x, (p x : AddCircle (1 : ℝ)) = v x) ∧
      (∀ e he t, (l e he t : AddCircle (1 : ℝ)) = c e he t) ∧
      (∀ e he, l e he 0 = p (ends e).1) ∧
      (∀ e he, l e he 1 = p (ends e).2) := by
  classical
  let a : α → ℝ := fun x => (AddCircle.equivIco (1 : ℝ) 0 (v x)).1
  have ha : ∀ x, (a x : AddCircle (1 : ℝ)) = v x :=
    fun _ => AddCircle.coe_equivIco
  let cov := JordanCurve.Brouwer.cover
  let b (e : G.EdgeIndex) (he : (e : β) ∈ D) : C(I, ℝ) :=
    cov.liftPath (c e he) (a (ends e).1) ((hc0 e he).trans (ha _).symm)
  have hb : ∀ e he t, (b e he t : AddCircle (1 : ℝ)) = c e he t :=
    fun e he t => congr_fun (cov.liftPath_lifts (c e he) _ _) t
  have hb0 : ∀ e he, b e he 0 = a (ends e).1 :=
    fun e he => cov.liftPath_zero (c e he) _ _
  have herr : ∀ e he, ∃ n : ℤ, (n : ℝ) = b e he 1 - a (ends e).2 := by
    intro e he
    have hz : ((b e he 1 - a (ends e).2 : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      rw [AddCircle.coe_sub, hb, ha, hc1, sub_self]
    simpa using ((AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz)
  let w : G.EdgeIndex → ℤ := fun e => if he : (e : β) ∈ D then (herr e he).choose else 0
  obtain ⟨q, hq⟩ := G.forest_exists_vertex_potential hE ends hends D hf w
  have hw : ∀ e he, (q (ends e).2 : ℝ) - (q (ends e).1 : ℝ) =
      b e he 1 - a (ends e).2 := by
    intro e he
    rw [← Int.cast_sub, hq e he]
    simpa [w, he] using (herr e he).choose_spec
  have hi : ∀ n : ℤ, ((n : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    intro n
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    exact ⟨n, by simp⟩
  refine ⟨fun x => a x + q x,
    fun e he => b e he + ContinuousMap.const I (q (ends e).1 : ℝ), ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [AddCircle.coe_add, hi, add_zero, ha]
  · intro e he t
    change ((b e he t + (q (ends e).1 : ℝ) : ℝ) : AddCircle (1 : ℝ)) = _
    rw [AddCircle.coe_add, hi, add_zero, hb]
  · intro e he
    change b e he 0 + (q (ends e).1 : ℝ) = _
    rw [hb0]
  · intro e he
    change b e he 1 + (q (ends e).1 : ℝ) = _
    linarith [hw e he]

/-- A circle-valued continuous map on the actual support of a finite forest
has a real lift. The quotient only identifies endpoints at the same drawn
vertex; joint edge-interior injectivity retains every original edge label. -/
theorem PlaneEmbedding.forest_circle_lift
    (P : PlaneEmbedding G) (hE : G.edgeSet.Finite)
    (D : Set β) (hf : G.IsForestIn D)
    (f : (ℝ × ℝ) → AddCircle (1 : ℝ))
    (hc : ContinuousOn f (P.edgeSupport D)) :
    ∃ l : C(P.edgeSupport D, ℝ),
      ∀ x : P.edgeSupport D, (l x : AddCircle (1 : ℝ)) = f x := by
  classical
  let _ : Fintype G.EdgeIndex := hE.fintype
  let B := {e : G.EdgeIndex // (e : β) ∈ D}
  let _ : TopologicalSpace B := ⊥
  let _ : DiscreteTopology B := ⟨rfl⟩
  have hmem : ∀ e : B, ∀ t : I, P.edgePath e.1 t ∈ P.edgeSupport D := by
    intro e t
    exact mem_iUnion.mpr ⟨e.1, mem_iUnion.mpr ⟨e.2, mem_range_self t⟩⟩
  let c (e : G.EdgeIndex) (he : (e : β) ∈ D) : C(I, AddCircle (1 : ℝ)) :=
    ⟨f ∘ P.edgePath e,
      hc.comp_continuous (P.edgePath e).continuous (hmem ⟨e, he⟩)⟩
  obtain ⟨p, l, _, hl, hl0, hl1⟩ :=
    G.forest_exists_compatible_lifts hE P.ends P.ends_valid D hf
      (f ∘ P.vertexPoint) c (fun _ _ => by simp [c]) (fun _ _ => by simp [c])
  let q : B × I → P.edgeSupport D := fun x => ⟨P.edgePath x.1.1 x.2, hmem x.1 x.2⟩
  have hq : Function.Surjective q := by
    rintro ⟨z, hz⟩
    obtain ⟨e, he⟩ := mem_iUnion.mp hz
    obtain ⟨heD, t, rfl⟩ := mem_iUnion.mp he
    exact ⟨(⟨e, heD⟩, t), rfl⟩
  have hqc : Continuous q := by
    apply continuous_prod_of_discrete_left.mpr
    intro e
    exact (P.edgePath e.1).continuous.subtype_mk _
  let L : B × I → ℝ := fun x => l x.1.1 x.1.2 x.2
  have hLc : Continuous L := continuous_prod_of_discrete_left.mpr
    (fun e => (l e.1 e.2).continuous)
  have hend : ∀ t : I, ¬ IsInteriorTime t → t = 0 ∨ t = 1 := by
    intro t ht
    have ht' : (t : ℝ) = 0 ∨ (t : ℝ) = 1 := by
      have := t.property
      dsimp [IsInteriorTime] at ht
      rcases le_or_gt (t : ℝ) 0 with h | h
      · exact Or.inl (le_antisymm h this.1)
      · exact Or.inr (le_antisymm this.2 (not_lt.mp (fun h1 => ht ⟨h, h1⟩)))
    exact ht'.imp (fun h => Subtype.ext h) (fun h => Subtype.ext h)
  have hfiber : L.FactorsThrough q := by
    rintro ⟨e, t⟩ ⟨g, s⟩ heq
    have heq' : P.edgePath e.1 t = P.edgePath g.1 s := congrArg Subtype.val heq
    by_cases ht : IsInteriorTime t
    · obtain ⟨heg, hts⟩ := P.interior_unique_preimage e.1 g.1 t s ht heq'
      have hegg : e = g := Subtype.ext heg
      subst g
      subst s
      rfl
    by_cases hs : IsInteriorTime s
    · obtain ⟨hge, hst⟩ := P.interior_unique_preimage g.1 e.1 s t hs heq'.symm
      have hgee : g = e := Subtype.ext hge
      subst g
      subst s
      rfl
    rcases hend t ht with rfl | rfl <;> rcases hend s hs with rfl | rfl
    · change l e.1 e.2 0 = l g.1 g.2 0
      rw [hl0, hl0]
      exact congrArg p (P.vertex_injective (G.left_mem_of_isLink (P.ends_valid e.1))
        (G.left_mem_of_isLink (P.ends_valid g.1)) (by simpa using heq'))
    · change l e.1 e.2 0 = l g.1 g.2 1
      rw [hl0, hl1]
      exact congrArg p (P.vertex_injective (G.left_mem_of_isLink (P.ends_valid e.1))
        (G.left_mem_of_isLink (P.ends_valid g.1).symm) (by simpa using heq'))
    · change l e.1 e.2 1 = l g.1 g.2 0
      rw [hl1, hl0]
      exact congrArg p (P.vertex_injective (G.left_mem_of_isLink (P.ends_valid e.1).symm)
        (G.left_mem_of_isLink (P.ends_valid g.1)) (by simpa using heq'))
    · change l e.1 e.2 1 = l g.1 g.2 1
      rw [hl1, hl1]
      exact congrArg p (P.vertex_injective (G.left_mem_of_isLink (P.ends_valid e.1).symm)
        (G.left_mem_of_isLink (P.ends_valid g.1).symm) (by simpa using heq'))
  obtain ⟨g, hg⟩ := (Function.factorsThrough_iff L).mp hfiber
  have hgc : Continuous g :=
    (Topology.IsQuotientMap.of_surjective_continuous hq hqc).continuous_iff.mpr (hg ▸ hLc)
  refine ⟨⟨g, hgc⟩, ?_⟩
  intro x
  obtain ⟨⟨e, t⟩, rfl⟩ := hq x
  change (g (q (e, t)) : AddCircle (1 : ℝ)) = f (P.edgePath e.1 t)
  have hgt : g (q (e, t)) = l e.1 e.2 t := (congr_fun hg (e, t)).symm
  rw [hgt]
  exact hl e.1 e.2 t

/-- Every circle-valued map on a finite drawn forest extends to the plane.
This is the graph-specific input to the imported disk no-retraction theorem. -/
theorem PlaneEmbedding.forest_sphere_extension
    (P : PlaneEmbedding G) (hE : G.edgeSet.Finite)
    (D : Set β) (hf : G.IsForestIn D)
    (f : C(P.edgeSupport D, Metric.sphere (0 : JordanCurve.Plane) 1)) :
    ∃ g : C(ℝ × ℝ, Metric.sphere (0 : JordanCurve.Plane) 1),
      ∀ x : P.edgeSupport D, g x = f x := by
  classical
  let E := JordanCurve.Brouwer.acToSphere
  let F : (ℝ × ℝ) → AddCircle (1 : ℝ) := fun z =>
    if hz : z ∈ P.edgeSupport D then E.symm (f ⟨z, hz⟩) else 0
  have hF : ContinuousOn F (P.edgeSupport D) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert E.symm.continuous.comp f.continuous using 1
    funext x
    exact dite_eq_left x.property
  obtain ⟨l, hl⟩ := P.forest_circle_lift hE D hf F hF
  obtain ⟨a, ha⟩ := l.exists_restrict_eq (P.isCompact_edgeSupport hE D).isClosed
  refine ⟨⟨fun x => E (a x : AddCircle (1 : ℝ)),
    E.continuous.comp (JordanCurve.Brouwer.cover.continuous.comp a.continuous)⟩, ?_⟩
  intro x
  change E (a x : AddCircle (1 : ℝ)) = f x
  have hax : a x = l x := DFunLike.congr_fun ha x
  rw [hax, hl]
  simp [F, x.property]

end Graph
