import Matroid.Internal.CycleLocalSides

/-! # Complete incidence for arbitrary embedded edges

For a nonloop edge, imported accessibility and arc-complement results close
a subarc around an interior point into an auxiliary Jordan curve. Relative
Schoenflies gives a local model for the original full drawing there. The
auxiliary curve is used only locally; it need not be a graph cycle.
-/

open Set unitInterval

private theorem ambientModelCurve_at {J : Set Schoenflies.Plane}
    (hJ : Schoenflies.IsJordanCurve J) (x : Schoenflies.Plane) (hx : x ∈ J) :
    ∃ H : Schoenflies.Plane ≃ₜ Schoenflies.Plane,
      H '' J = Schoenflies.modelCurve ∧ H x = Schoenflies.Plane.mk 0 1 := by
  have hS : Schoenflies.IsJordanCurve (Metric.sphere (0 : Schoenflies.Plane) 1) := by
    have h := JordanPath.isJordanCurve_of_sphere_trace
      (Subtype.val : Metric.sphere (0 : JordanCurve.Plane) 1 → Schoenflies.Plane)
      continuous_subtype_val Subtype.val_injective
    have hrange : Set.range (Subtype.val : Metric.sphere (0 : JordanCurve.Plane) 1 →
        Schoenflies.Plane) = Metric.sphere (0 : Schoenflies.Plane) 1 := by
      ext z; exact ⟨fun ⟨w, hw⟩ => hw ▸ w.2, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩
    rwa [hrange] at h
  obtain ⟨v⟩ := hS.homeomorph_modelCurve
  let q : AddCircle (1 : ℝ) ≃ₜ ↥Schoenflies.modelCurve :=
    ((AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).trans
      JordanCurve.Arcs.circleHomeoSphere).trans v
  obtain ⟨e⟩ := hJ.homeomorph_modelCurve
  let u : J := ⟨x, hx⟩
  let y : ↥Schoenflies.modelCurve := ⟨Schoenflies.Plane.mk 0 1, by
    norm_num [Schoenflies.modelCurve, Schoenflies.Plane.supNorm]⟩
  let a := q.symm (e u)
  let b := q.symm y
  let e' := e.trans (q.symm.trans ((Homeomorph.addLeft (b - a)).trans q))
  have hpoint : e' u = y := by
    change q ((b - a) + q.symm (e u)) = y
    have hshift : (b - a) + q.symm (e u) = b := by dsimp [a]; abel
    rw [hshift]
    exact q.apply_symm_apply y
  obtain ⟨H, hH⟩ := Schoenflies.jordan_schoenflies_of_homeomorph hJ
    Schoenflies.isJordanCurve_modelCurve e'
  refine ⟨H, ?_, ?_⟩
  · ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hH ⟨w, hw⟩]
      exact (e' ⟨w, hw⟩).2
    · intro hz
      obtain ⟨w, hw⟩ := e'.surjective ⟨z, hz⟩
      exact ⟨w, w.2, (hH w).trans (congrArg Subtype.val hw)⟩
  · exact (hH u).trans (congrArg Subtype.val hpoint)

namespace Graph
variable {α β : Type*} {G : Graph α β}

/-- A nonloop edge is locally part of an auxiliary Jordan curve at each
interior point. The auxiliary arc is supplied by imported accessibility and
joining theorems, and is excluded from the final drawing neighborhood. -/
theorem PlaneEmbedding.nonloop_edge_has_local_modelCurve
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    (e : G.EdgeIndex) (hne : (P.ends e).1 ≠ (P.ends e).2)
    (t : I) (ht : IsInteriorTime t) :
    ∃ F : (ℝ × ℝ) ≃ₜ Schoenflies.Plane, ∃ U : Set (ℝ × ℝ),
      IsOpen U ∧ P.edgePath e t ∈ U ∧
      F (P.edgePath e t) = Schoenflies.Plane.mk 0 1 ∧
      ∀ z ∈ U, z ∈ P.drawnSet ↔ F z ∈ Schoenflies.modelCurve := by
  let E := schoenfliesPlaneHomeomorph
  let f : ℝ → Schoenflies.Plane := E ∘ (P.edgePath e).extend
  have hc : ContinuousOn f I := (E.continuous.comp (P.edgePath e).continuous_extend).continuousOn
  have hi : InjOn f I := by
    intro s hs r hr hsr
    have hpath : P.edgePath e ⟨s, hs⟩ = P.edgePath e ⟨r, hr⟩ := by
      apply E.injective
      simpa only [f, Function.comp_apply, Path.extend_apply _ hs, Path.extend_apply _ hr] using hsr
    exact congrArg Subtype.val (P.edgePath_injective_of_nonloop e hne hpath)
  let C := f '' I
  have hC : Schoenflies.IsArc C := ⟨f, hc, hi, rfl⟩
  have hCeq : C = E '' Set.range (P.edgePath e) := by
    change (E ∘ (P.edgePath e).extend) '' I = _
    rw [Set.image_comp, Path.image_extend_of_subset _ subset_rfl]
  have hCD : C ⊆ closure Cᶜ := by
    have hd : Dense Cᶜ := by
      rw [hCeq, ← Set.image_compl_eq E.bijective, dense_iff_closure_eq,
        ← E.image_closure, (P.dense_compl_edgePath e).closure_eq]
      exact Set.image_univ_of_surjective E.surjective
    intro z _
    rw [hd.closure_eq]
    trivial
  obtain ⟨A, hAC, _, hacc, hAdense⟩ := Schoenflies.exists_countable_dense_stronglyAccessible
    hC.isCompact hC.nonempty hC.isClosed.isOpen_compl subset_rfl
    (fun _ _ => connectedComponentIn_subset _ _) hCD
  have htime : ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ 1 →
      ∃ r ∈ Ioo u v, Schoenflies.StronglyAccessible Cᶜ (f r) := by
    intro u v hu huv hv
    let m := (u + v) / 2
    have hm : m ∈ Ioo u v := by dsimp [m]; constructor <;> linarith
    have hmI : m ∈ I := ⟨hu.trans hm.1.le, hm.2.le.trans hv⟩
    obtain ⟨W, hW, hrel⟩ := Schoenflies.image_isRelOpen hc hi (isOpen_Ioo (a := u) (b := v))
    have hmW : f m ∈ W := by
      have hp : f m ∈ f '' (Ioo u v ∩ I) := ⟨m, ⟨hm, hmI⟩, rfl⟩
      exact (hrel ▸ hp).1
    obtain ⟨z, hzW, hzA⟩ := mem_closure_iff.mp (hAdense ⟨m, hmI, rfl⟩) W hW hmW
    have hzimage : z ∈ f '' (Ioo u v ∩ I) := hrel.symm ▸ ⟨hzW, hAC hzA⟩
    obtain ⟨r, hr, hfr⟩ := hzimage
    exact ⟨r, hr.1, hfr ▸ hacc z hzA⟩
  obtain ⟨a, ha, haccess⟩ := htime 0 t.1 le_rfl ht.1 t.2.2
  obtain ⟨b, hb, hbaccess⟩ := htime t.1 1 t.2.1 ht.2 le_rfl
  have haI : a ∈ I := ⟨ha.1.le, (ha.2.trans ht.2).le⟩
  have hbI : b ∈ I := ⟨(ht.1.trans hb.1).le, hb.2.le⟩
  have hab : a < b := ha.2.trans hb.1
  have hfab : f a ≠ f b := fun h => hab.ne (hi haI hbI h)
  obtain ⟨B, _, hB, hBC⟩ := Schoenflies.exists_simple_arc_of_polyAccessible
    hC.isClosed.isOpen_compl (Schoenflies.arc_complement hC).isPreconnected hfab
    haccess.polyAccessible hbaccess.polyAccessible
  let D := f '' Icc a b
  have hD : Schoenflies.IsArcBetween D (f a) (f b) := by
    simpa only [D, uIcc_of_le hab.le] using
      Schoenflies.isArcBetween_subarc_of_injOn_I hc hi haI hbI hab.ne
  have hDC : D ⊆ C := Set.image_mono (Icc_subset_Icc haI.1 hbI.2)
  have hJ : Schoenflies.IsJordanCurve (D ∪ B) := by
    apply Schoenflies.IsJordanCurve.of_two_arcs hD hB.reverse
    intro z hzD hzB
    by_contra h
    exact hBC ⟨hzB, by simpa only [mem_insert_iff, mem_singleton_iff] using h⟩ (hDC hzD)
  have htD : f t.1 ∈ D := ⟨t, ⟨ha.2.le, hb.1.le⟩, rfl⟩
  have htB : f t.1 ∉ B := by
    intro hBmem
    apply hBC ⟨hBmem, ?_⟩ ⟨t, t.2, rfl⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    constructor
    · intro h; exact ha.2.ne (hi haI t.2 h.symm)
    · intro h; exact hb.1.ne (hi t.2 hbI h)
  obtain ⟨H, hHJ, hHt⟩ := ambientModelCurve_at hJ (f t.1) (Or.inl htD)
  let V : Set I := {s | (s : ℝ) ∈ Ioo a b}
  have hVopen : IsOpen V := isOpen_Ioo.preimage continuous_subtype_val
  obtain ⟨U₁, hU₁, htU₁, hdraw⟩ :=
    P.exists_isolated_subarc_neighborhood hV hE e t ht V hVopen ⟨ha.2, hb.1⟩
  let U := U₁ ∩ E ⁻¹' Bᶜ
  have hUopen : IsOpen U := hU₁.inter (hB.isArc.isClosed.isOpen_compl.preimage E.continuous)
  have hEt : E (P.edgePath e t) = f t.1 := by
    dsimp [f]; rw [Path.extend_extends']
  have htU : P.edgePath e t ∈ U := by
    refine ⟨htU₁, ?_⟩
    change E (P.edgePath e t) ∉ B
    rwa [hEt]
  have hagree : ∀ z ∈ U, z ∈ P.drawnSet ↔ E z ∈ D ∪ B := by
    intro z hz
    constructor
    · intro hzdraw
      obtain ⟨s, hs, hsz⟩ := hdraw ⟨hzdraw, hz.1⟩
      left
      refine ⟨s, ⟨hs.1.le, hs.2.le⟩, ?_⟩
      dsimp [f]
      rw [Path.extend_extends', hsz]
    · intro hzJ
      rcases hzJ with hzD | hzB
      · obtain ⟨s, hs, hsz⟩ := hzD
        have hsI : s ∈ I := ⟨haI.1.trans hs.1, hs.2.trans hbI.2⟩
        have hpath : P.edgePath e ⟨s, hsI⟩ = z := by
          apply E.injective
          simpa only [f, Function.comp_apply, Path.extend_apply _ hsI] using hsz
        rw [← hpath]
        exact Or.inr (mem_iUnion.mpr ⟨e, ⟨⟨s, hsI⟩, rfl⟩⟩)
      · exact False.elim (hz.2 hzB)
  refine ⟨E.trans H, U, hUopen, htU, ?_, ?_⟩
  · change H (E (P.edgePath e t)) = _
    rw [hEt]
    exact hHt
  · intro z hz
    change z ∈ P.drawnSet ↔ H (E z) ∈ Schoenflies.modelCurve
    rw [hagree z hz, ← hHJ]
    exact H.injective.mem_set_image.symm

/-- At every edge-interior point, at most two full faces approach the drawing,
and each of those faces approaches all nearby points of that edge. Unlike
the cycle result, this also applies to edges lying in no graph cycle. -/
theorem PlaneEmbedding.edge_local_faces
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    (e : G.EdgeIndex) (t : I) (ht : IsInteriorTime t) :
    ∃ U : Set (ℝ × ℝ), ∃ f g : P.Face,
      IsOpen U ∧ P.edgePath e t ∈ U ∧
      (∀ s : I, P.edgePath e s ∈ U →
        P.edgePath e s ∈ closure (P.facePoints f) ∧
          P.edgePath e s ∈ closure (P.facePoints g)) ∧
      (∀ z ∈ U, ∀ k : P.Face, z ∈ closure (P.facePoints k) → k = f ∨ k = g) := by
  by_cases hloop : (P.ends e).1 = (P.ends e).2
  · have hC : G.IsGraphCycle {(e : β)} := by
      refine ⟨Set.singleton_subset_iff.mpr e.2, ?_, ?_⟩
      · apply G.hasEdgeCycle_of_loop (e := e) (u := (P.ends e).1)
        · exact rfl
        · simpa only [hloop] using P.ends_valid e
      · intro D hD
        have hDempty : D = ∅ := Set.ssubset_singleton_iff.mp hD
        rw [hDempty]
        rintro ⟨d, hd, _⟩
        exact hd
    obtain ⟨U, f, g, hU, htU, happroach, hcomplete, _⟩ :=
      P.graphCycle_local_faces hV hE hC e rfl t ht
    refine ⟨U, f, g, hU, htU, ?_, hcomplete⟩
    intro s hs
    apply happroach _ hs
    simp only [PlaneEmbedding.edgeSupport, Set.mem_iUnion]
    exact ⟨e, rfl, s, rfl⟩
  · obtain ⟨F, U₀, hU₀, htU₀, hFt, hagree⟩ :=
      P.nonloop_edge_has_local_modelCurve hV hE e hloop t ht
    obtain ⟨U, f, g, hU, htU, happroach, hcomplete⟩ :=
      P.local_faces_of_modelCurve (P.edgePath e t) F hFt U₀ hU₀ htU₀ hagree
    refine ⟨U, f, g, hU, htU, ?_, hcomplete⟩
    intro s hs
    exact happroach _ hs (Or.inr (mem_iUnion.mpr ⟨e, ⟨s, rfl⟩⟩))

/-- Incidence with any edge holds along its entire interior as soon as it
holds at one interior point. -/
theorem PlaneEmbedding.edge_incidence_all_interior
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    (e : G.EdgeIndex) (f : P.Face) (t : I) (ht : IsInteriorTime t)
    (htf : P.edgePath e t ∈ closure (P.facePoints f)) :
    ∀ s : I, IsInteriorTime s → P.edgePath e s ∈ closure (P.facePoints f) := by
  let T := Set.Ioo (0 : I) 1
  let trace : T → ℝ × ℝ := fun s => P.edgePath e s.1
  let A : Set T := {s | trace s ∈ closure (P.facePoints f)}
  have htrace : Continuous trace := (P.edgePath e).continuous.comp continuous_subtype_val
  have hAclosed : IsClosed A := isClosed_closure.preimage htrace
  have hAopen : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro s hs
    obtain ⟨U, a, b, hU, hsU, happroach, hcomplete⟩ :=
      P.edge_local_faces hV hE e s.1 s.2
    have hpair := hcomplete _ hsU f hs
    have hsub : trace ⁻¹' U ⊆ A := by
      intro s' hs'
      have hcl := happroach s'.1 hs'
      change trace s' ∈ closure (P.facePoints f)
      rcases hpair with hfa | hfb
      · rw [hfa]; exact hcl.1
      · rw [hfb]; exact hcl.2
    exact Filter.mem_of_superset ((hU.preimage htrace).mem_nhds hsU) hsub
  let _ : PreconnectedSpace T := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  have hAall : A = Set.univ := (IsClopen.eq_univ ⟨hAclosed, hAopen⟩ ⟨⟨t, ht⟩, htf⟩)
  intro s hs
  have hmem : (⟨s, hs⟩ : T) ∈ A := by rw [hAall]; trivial
  exact hmem

/-- Every edge has a complete pair of incident full-drawing faces. The pair
may repeat a face; no cycle hypothesis or finite-face hypothesis is needed. -/
theorem PlaneEmbedding.edge_has_complete_incidentFaces
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    (e : G.EdgeIndex) :
    ∃ f g : P.Face,
      P.FaceIncident e f ∧ P.FaceIncident e g ∧
      (∀ k : P.Face, P.FaceIncident e k → k = f ∨ k = g) := by
  let t : I := ⟨1 / 2, by norm_num⟩
  have ht : IsInteriorTime t := by norm_num [IsInteriorTime, t]
  obtain ⟨U, f, g, _, htU, happroach, hcomplete⟩ := P.edge_local_faces hV hE e t ht
  have hcl := happroach t htU
  refine ⟨f, g, ⟨t, ht, hcl.1⟩, ⟨t, ht, hcl.2⟩, ?_⟩
  intro k hk
  obtain ⟨s, hs, hsk⟩ := hk
  exact hcomplete _ htU k (P.edge_incidence_all_interior hV hE e k s hs hsk t ht)

/-- Complete incidence for the original full finite drawing, preserving all
edge labels, loops, and parallel edges. -/
theorem PlaneEmbedding.exists_complete_incidence
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite) :
    ∃ sides : G.EdgeIndex → P.Face × P.Face,
      (∀ e, P.FaceIncident e (sides e).1 ∧ P.FaceIncident e (sides e).2) ∧
      (∀ e f, P.FaceIncident e f → f = (sides e).1 ∨ f = (sides e).2) := by
  classical
  have hpairs : ∀ e : G.EdgeIndex, ∃ p : P.Face × P.Face,
      (P.FaceIncident e p.1 ∧ P.FaceIncident e p.2) ∧
      (∀ f, P.FaceIncident e f → f = p.1 ∨ f = p.2) := by
    intro e
    obtain ⟨f, g, hf, hg, hcomplete⟩ := P.edge_has_complete_incidentFaces hV hE e
    exact ⟨(f, g), ⟨hf, hg⟩, hcomplete⟩
  choose sides hinc hcomplete using hpairs
  exact ⟨sides, hinc, hcomplete⟩

/-- The incident-face assignment and every primal cycle boundary are now
constructed from the finite drawing alone. Only forest-boundary exclusion
is absent from the existing N268 reduction. -/
theorem PlaneEmbedding.exists_incidence_with_cycle_boundaries
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite) :
    ∃ sides : G.EdgeIndex → P.Face × P.Face,
      (∀ e, P.FaceIncident e (sides e).1 ∧ P.FaceIncident e (sides e).2) ∧
      (∀ e f, P.FaceIncident e f → f = (sides e).1 ∨ f = (sides e).2) ∧
      (∀ C, G.IsGraphCycle C → ∃ S : Set P.Face, P.faceBoundary sides S = C) := by
  obtain ⟨sides, hinc, hcomplete⟩ := P.exists_complete_incidence hV hE
  exact ⟨sides, hinc, hcomplete,
    P.graphCycles_are_faceBoundaries_of_complete_incidence_no_faceFinite hV hE sides
      hinc hcomplete⟩

end Graph
