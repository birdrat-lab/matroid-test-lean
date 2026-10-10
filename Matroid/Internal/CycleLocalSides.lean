import Matroid.Internal.SchoenfliesCycle

/-! # The actual local faces of a cycle edge

Relative Schoenflies puts a chosen cycle point in the middle of a model-square
side. The finite drawing agrees locally with the cycle. Its two local open
half-balls therefore lie in actual full-drawing faces; no finite-face hypothesis
is needed.
-/

open Set unitInterval

private theorem modelCurve_eq_line_in_ball {ε : ℝ} (hε : ε < 1)
    {z : Schoenflies.Plane} (hz : z ∈ Metric.ball (Schoenflies.Plane.mk 0 1) ε) :
    z ∈ Schoenflies.modelCurve ↔ z 1 = 1 := by
  have hnorm : ‖z - Schoenflies.Plane.mk 0 1‖ < ε := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have h0 : |z 0| < 1 := by
    have h := (Schoenflies.Plane.abs_zero_le_supNorm (z - Schoenflies.Plane.mk 0 1)).trans
      (Schoenflies.Plane.supNorm_le_norm _)
    have hb : |z 0| ≤ ‖z - Schoenflies.Plane.mk 0 1‖ := by
      simpa only [Schoenflies.Plane.sub_apply, Schoenflies.Plane.mk,
        Matrix.cons_val_zero, sub_zero] using h
    exact lt_of_le_of_lt hb (hnorm.trans hε)
  have h1 : |z 1 - 1| < 1 := by
    have h := (Schoenflies.Plane.abs_one_le_supNorm (z - Schoenflies.Plane.mk 0 1)).trans
      (Schoenflies.Plane.supNorm_le_norm _)
    have hb : |z 1 - 1| ≤ ‖z - Schoenflies.Plane.mk 0 1‖ := by
      simpa only [Schoenflies.Plane.sub_apply, Schoenflies.Plane.mk,
        Matrix.cons_val_one, Matrix.cons_val_zero] using h
    exact lt_of_le_of_lt hb (hnorm.trans hε)
  have hzpos : 0 < z 1 := by have := (abs_lt.mp h1).1; linarith
  change max |z 0| |z 1| = 1 ↔ z 1 = 1
  rw [abs_of_pos hzpos]
  constructor
  · intro h
    have hle : z 1 ≤ 1 := by rw [← h]; exact le_max_right _ _
    have hge : 1 ≤ z 1 := by
      by_contra hn
      have hlt : max |z 0| (z 1) < 1 := max_lt h0 (lt_of_not_ge hn)
      rw [h] at hlt
      exact lt_irrefl _ hlt
    exact le_antisymm hle hge
  · intro h
    rw [h]
    exact max_eq_right h0.le

private theorem closure_halfBall {ε : ℝ} (hε : 0 < ε)
    {z : Schoenflies.Plane} (hz : z ∈ Metric.ball (Schoenflies.Plane.mk 0 1) ε)
    (hline : z 1 = 1) :
    z ∈ closure (Metric.ball (Schoenflies.Plane.mk 0 1) ε ∩ {w | w 1 < 1}) ∧
      z ∈ closure (Metric.ball (Schoenflies.Plane.mk 0 1) ε ∩ {w | 1 < w 1}) := by
  let a := Schoenflies.Plane.mk 0 (1 - ε / 2)
  let b := Schoenflies.Plane.mk 0 (1 + ε / 2)
  have ha : a ∈ Metric.ball (Schoenflies.Plane.mk 0 1) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : a - Schoenflies.Plane.mk 0 1 = Schoenflies.Plane.mk 0 (-ε / 2) := by
      ext i; fin_cases i <;> simp [a]
      ring
    rw [heq, EuclideanSpace.norm_eq]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.norm_eq_abs, abs_zero]
    rw [abs_of_neg (by linarith : -ε / 2 < 0)]
    norm_num only [zero_pow, zero_add, Real.sqrt_sq_eq_abs]
    rw [abs_of_pos (by linarith : 0 < -(-ε / 2))]
    linarith
  have hb : b ∈ Metric.ball (Schoenflies.Plane.mk 0 1) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : b - Schoenflies.Plane.mk 0 1 = Schoenflies.Plane.mk 0 (ε / 2) := by
      ext i; fin_cases i <;> simp [b]
    rw [heq, EuclideanSpace.norm_eq]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.norm_eq_abs, abs_zero]
    rw [abs_of_pos (by linarith : 0 < ε / 2)]
    norm_num only [zero_pow, zero_add, Real.sqrt_sq_eq_abs]
    rw [abs_of_pos (by linarith : 0 < ε / 2)]
    linarith
  have hL : openSegment ℝ z a ⊆ Metric.ball (Schoenflies.Plane.mk 0 1) ε ∩ {w | w 1 < 1} := by
    rintro w ⟨p, q, hp, hq, hpq, rfl⟩
    refine ⟨(convex_ball _ _) hz ha hp.le hq.le hpq, ?_⟩
    simp only [Set.mem_ofPred_eq, Schoenflies.Plane.smul_add_apply, hline, a,
      Schoenflies.Plane.mk, Matrix.cons_val_one, Matrix.cons_val_zero, mul_one]
    nlinarith
  have hR : openSegment ℝ z b ⊆ Metric.ball (Schoenflies.Plane.mk 0 1) ε ∩ {w | 1 < w 1} := by
    rintro w ⟨p, q, hp, hq, hpq, rfl⟩
    refine ⟨(convex_ball _ _) hz hb hp.le hq.le hpq, ?_⟩
    simp only [Set.mem_ofPred_eq, Schoenflies.Plane.smul_add_apply, hline, b,
      Schoenflies.Plane.mk, Matrix.cons_val_one, Matrix.cons_val_zero, mul_one]
    nlinarith
  exact ⟨closure_mono hL (segment_subset_closure_openSegment (left_mem_segment ℝ z a)),
    closure_mono hR (segment_subset_closure_openSegment (left_mem_segment ℝ z b))⟩

namespace Graph
variable {α β : Type*} {G : Graph α β}

private theorem PlaneEmbedding.connected_subset_facePoints
    (P : PlaneEmbedding G) {S : Set (ℝ × ℝ)} (hS : IsConnected S)
    (havoid : S ⊆ P.drawnSetᶜ) :
    ∃ f : P.Face, S ⊆ P.facePoints f := by
  obtain ⟨x, hx⟩ := hS.nonempty
  let f : P.Face := ConnectedComponents.mk ⟨x, havoid hx⟩
  refine ⟨f, ?_⟩
  intro y hy
  have hycomp := hS.isPreconnected.subset_connectedComponentIn hx havoid hy
  rw [connectedComponentIn_eq_image (havoid hx)] at hycomp
  obtain ⟨p, hp, hpy⟩ := hycomp
  have hpval : p = ⟨y, havoid hy⟩ := Subtype.ext hpy
  refine ⟨havoid hy, ?_⟩
  exact (ConnectedComponents.coe_eq_coe').mpr (hpval ▸ hp)

/-- A local ambient square model identifies all approaching full-drawing
faces. The two faces may coincide when the local sides join elsewhere. -/
theorem PlaneEmbedding.local_faces_of_modelCurve
    (P : PlaneEmbedding G) (x : ℝ × ℝ)
    (F : (ℝ × ℝ) ≃ₜ Schoenflies.Plane)
    (hFx : F x = Schoenflies.Plane.mk 0 1)
    (U₀ : Set (ℝ × ℝ)) (hU₀ : IsOpen U₀) (hxU₀ : x ∈ U₀)
    (hagree : ∀ z ∈ U₀, z ∈ P.drawnSet ↔ F z ∈ Schoenflies.modelCurve) :
    ∃ U : Set (ℝ × ℝ), ∃ f g : P.Face,
      IsOpen U ∧ x ∈ U ∧
      (∀ z ∈ U, z ∈ P.drawnSet →
        z ∈ closure (P.facePoints f) ∧ z ∈ closure (P.facePoints g)) ∧
      (∀ z ∈ U, ∀ k : P.Face, z ∈ closure (P.facePoints k) → k = f ∨ k = g) := by
  have hFxU : Schoenflies.Plane.mk 0 1 ∈ F '' U₀ := hFx ▸ ⟨x, hxU₀, rfl⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (F.isOpenMap U₀ hU₀) _ hFxU
  let ε := min r (1 / 2)
  have hε : 0 < ε := lt_min hr (by norm_num)
  have hεsmall : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  let N := Metric.ball (Schoenflies.Plane.mk 0 1) ε
  let L := N ∩ {z : Schoenflies.Plane | z 1 < 1}
  let R := N ∩ {z : Schoenflies.Plane | 1 < z 1}
  let U := F ⁻¹' N
  have hNsub : N ⊆ F '' U₀ := (Metric.ball_subset_ball (min_le_left _ _)).trans hball
  have hUsub : U ⊆ U₀ := by
    intro z hz
    obtain ⟨w, hw, heq⟩ := hNsub hz
    exact F.injective heq ▸ hw
  have hUopen : IsOpen U := F.continuous.isOpen_preimage _ Metric.isOpen_ball
  have hxU : x ∈ U := by change F x ∈ N; rw [hFx]; exact Metric.mem_ball_self hε
  have hclCenter := closure_halfBall hε (Metric.mem_ball_self hε) rfl
  have hL : IsConnected L :=
    ((convex_ball _ _).inter (Schoenflies.Plane.convex_coord_lt 1 1)).isConnected
      (closure_nonempty_iff.mp ⟨_, hclCenter.1⟩)
  have hR : IsConnected R :=
    ((convex_ball _ _).inter (Schoenflies.Plane.convex_coord_gt 1 1)).isConnected
      (closure_nonempty_iff.mp ⟨_, hclCenter.2⟩)
  have havoid : ∀ z ∈ N, z 1 ≠ 1 → F.symm z ∉ P.drawnSet := by
    intro z hz hne hD
    have hzU : F.symm z ∈ U := by change F (F.symm z) ∈ N; simpa using hz
    have hzJ := (hagree _ (hUsub hzU)).mp hD
    rw [F.apply_symm_apply] at hzJ
    exact hne ((modelCurve_eq_line_in_ball hεsmall hz).mp hzJ)
  have havoidL : F.symm '' L ⊆ P.drawnSetᶜ := by
    rintro _ ⟨z, ⟨hz, hlt⟩, rfl⟩
    exact havoid z hz (ne_of_lt hlt)
  have havoidR : F.symm '' R ⊆ P.drawnSetᶜ := by
    rintro _ ⟨z, ⟨hz, hgt⟩, rfl⟩
    exact havoid z hz (ne_of_gt hgt)
  obtain ⟨f, hLf⟩ := P.connected_subset_facePoints
    (hL.image F.symm F.symm.continuous.continuousOn) havoidL
  obtain ⟨g, hRg⟩ := P.connected_subset_facePoints
    (hR.image F.symm F.symm.continuous.continuousOn) havoidR
  have hcover : ∀ z ∈ U, ∀ hz : z ∉ P.drawnSet,
      (ConnectedComponents.mk ⟨z, hz⟩ : P.Face) = f ∨
        (ConnectedComponents.mk ⟨z, hz⟩ : P.Face) = g := by
    intro z hz hzD
    have hFzJ : F z ∉ Schoenflies.modelCurve :=
      fun h => hzD ((hagree _ (hUsub hz)).mpr h)
    have hne : F z 1 ≠ 1 := fun h => hFzJ ((modelCurve_eq_line_in_ball hεsmall hz).mpr h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl (hLf ⟨F z, ⟨hz, hlt⟩, F.symm_apply_apply z⟩).2
    · exact Or.inr (hRg ⟨F z, ⟨hz, hgt⟩, F.symm_apply_apply z⟩).2
  refine ⟨U, f, g, hUopen, hxU, ?_, ?_⟩
  · intro z hz hzD
    have hline := (modelCurve_eq_line_in_ball hεsmall hz).mp
      ((hagree _ (hUsub hz)).mp hzD)
    have hcl := closure_halfBall hε hz hline
    have hclL : z ∈ closure (F.symm '' L) := by
      rw [← F.symm.image_closure]
      exact ⟨F z, hcl.1, F.symm_apply_apply z⟩
    have hclR : z ∈ closure (F.symm '' R) := by
      rw [← F.symm.image_closure]
      exact ⟨F z, hcl.2, F.symm_apply_apply z⟩
    exact ⟨closure_mono hLf hclL, closure_mono hRg hclR⟩
  · intro z hz k hzk
    obtain ⟨w, hwU, hwD, hwk⟩ := mem_closure_iff.mp hzk U hUopen hz
    rcases hcover w hwU hwD with hf | hg
    · exact Or.inl (hwk.symm.trans hf)
    · exact Or.inr (hwk.symm.trans hg)

/-- At each interior point of a cycle edge, two actual full-drawing faces
exhaust the incident faces throughout a neighborhood. Every cycle point in
that neighborhood is approached by both faces, which occupy opposite Jordan
sides. Finiteness of the entire face type is not assumed. -/
theorem PlaneEmbedding.graphCycle_local_faces
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    {C : Set β} (hC : G.IsGraphCycle C) (e : G.EdgeIndex) (he : (e : β) ∈ C)
    (t : I) (ht : IsInteriorTime t) :
    ∃ U : Set (ℝ × ℝ), ∃ f g : P.Face,
      IsOpen U ∧ P.edgePath e t ∈ U ∧
      (∀ z ∈ U, z ∈ P.edgeSupport C →
        z ∈ closure (P.facePoints f) ∧ z ∈ closure (P.facePoints g)) ∧
      (∀ z ∈ U, ∀ k : P.Face, z ∈ closure (P.facePoints k) → k = f ∨ k = g) ∧
      P.faceMap_edgeSupport C f ≠ P.faceMap_edgeSupport C g := by
  let x := P.edgePath e t
  have hx : x ∈ P.edgeSupport C := by
    simp only [PlaneEmbedding.edgeSupport, Set.mem_iUnion]
    exact ⟨e, he, t, rfl⟩
  obtain ⟨F, hF, hFx⟩ := P.graphCycle_hasAmbientModelCurve_at hC x hx
  obtain ⟨U₀, hU₀, hxU₀, hagree⟩ :=
    P.edgeInterior_has_support_neighborhood hV hE C e he t ht
  have hFxU : Schoenflies.Plane.mk 0 1 ∈ F '' U₀ := hFx ▸ ⟨x, hxU₀, rfl⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (F.isOpenMap U₀ hU₀) _ hFxU
  let ε := min r (1 / 2)
  have hε : 0 < ε := lt_min hr (by norm_num)
  have hεsmall : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  let N := Metric.ball (Schoenflies.Plane.mk 0 1) ε
  let L := N ∩ {z : Schoenflies.Plane | z 1 < 1}
  let R := N ∩ {z : Schoenflies.Plane | 1 < z 1}
  let U := F ⁻¹' N
  have hNsub : N ⊆ F '' U₀ := (Metric.ball_subset_ball (min_le_left _ _)).trans hball
  have hUsub : U ⊆ U₀ := by
    intro z hz
    obtain ⟨w, hw, heq⟩ := hNsub hz
    exact F.injective heq ▸ hw
  have hUopen : IsOpen U := F.continuous.isOpen_preimage _ Metric.isOpen_ball
  have hxU : x ∈ U := by change F x ∈ N; rw [hFx]; exact Metric.mem_ball_self hε
  have hclCenter := closure_halfBall hε (Metric.mem_ball_self hε) rfl
  have hL : IsConnected L :=
    ((convex_ball _ _).inter (Schoenflies.Plane.convex_coord_lt 1 1)).isConnected
      (closure_nonempty_iff.mp ⟨_, hclCenter.1⟩)
  have hR : IsConnected R :=
    ((convex_ball _ _).inter (Schoenflies.Plane.convex_coord_gt 1 1)).isConnected
      (closure_nonempty_iff.mp ⟨_, hclCenter.2⟩)
  have havoid (S : Set Schoenflies.Plane) (hSN : S ⊆ N)
      (hSJ : ∀ w ∈ S, w ∉ Schoenflies.modelCurve) :
      F.symm '' S ⊆ P.drawnSetᶜ := by
    rintro z ⟨w, hw, rfl⟩ hdraw
    have hwU : F.symm w ∈ U₀ := by
      obtain ⟨v, hv, hvw⟩ := hNsub (hSN hw)
      exact (F.eq_symm_apply.mpr hvw) ▸ hv
    have hsupport := (hagree _ hwU).mp hdraw
    apply hSJ w hw
    rw [← hF]
    exact ⟨F.symm w, hsupport, F.apply_symm_apply w⟩
  have havoidL : F.symm '' L ⊆ P.drawnSetᶜ := havoid L inter_subset_left (by
    intro w hw hj
    have heq := (modelCurve_eq_line_in_ball hεsmall hw.1).mp hj
    exact ne_of_lt hw.2 heq)
  have havoidR : F.symm '' R ⊆ P.drawnSetᶜ := havoid R inter_subset_left (by
    intro w hw hj
    have heq := (modelCurve_eq_line_in_ball hεsmall hw.1).mp hj
    exact ne_of_gt hw.2 heq)
  obtain ⟨f, hLf⟩ := P.connected_subset_facePoints
    (hL.image F.symm F.symm.continuous.continuousOn) havoidL
  obtain ⟨g, hRg⟩ := P.connected_subset_facePoints
    (hR.image F.symm F.symm.continuous.continuousOn) havoidR
  have hcover : ∀ z ∈ U, ∀ hz : z ∉ P.drawnSet,
      (ConnectedComponents.mk ⟨z, hz⟩ : P.Face) = f ∨
        (ConnectedComponents.mk ⟨z, hz⟩ : P.Face) = g := by
    intro z hz hzD
    have hzJ : z ∉ P.edgeSupport C := fun h => hzD (P.edgeSupport_subset_drawnSet C h)
    have hFzJ : F z ∉ Schoenflies.modelCurve := by
      rw [← hF]
      simpa only [F.injective.mem_set_image] using hzJ
    have hne : F z 1 ≠ 1 := fun h => hFzJ ((modelCurve_eq_line_in_ball hεsmall hz).mpr h)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl (hLf ⟨F z, ⟨hz, hlt⟩, F.symm_apply_apply z⟩).2
    · exact Or.inr (hRg ⟨F z, ⟨hz, hgt⟩, F.symm_apply_apply z⟩).2
  have happroach : ∀ z ∈ U, z ∈ P.edgeSupport C →
      z ∈ closure (P.facePoints f) ∧ z ∈ closure (P.facePoints g) := by
    intro z hz hzC
    have hFz : F z ∈ Schoenflies.modelCurve := by rw [← hF]; exact ⟨z, hzC, rfl⟩
    have hline := (modelCurve_eq_line_in_ball hεsmall hz).mp hFz
    have hcl := closure_halfBall hε hz hline
    have hclL : z ∈ closure (F.symm '' L) := by
      rw [← F.symm.image_closure]
      exact ⟨F z, hcl.1, F.symm_apply_apply z⟩
    have hclR : z ∈ closure (F.symm '' R) := by
      rw [← F.symm.image_closure]
      exact ⟨F z, hcl.2, F.symm_apply_apply z⟩
    exact ⟨closure_mono hLf hclL, closure_mono hRg hclR⟩
  have hcomplete : ∀ z ∈ U, ∀ k : P.Face,
      z ∈ closure (P.facePoints k) → k = f ∨ k = g := by
    intro z hz k hzk
    obtain ⟨w, hwU, hwD, hwk⟩ := mem_closure_iff.mp hzk U hUopen hz
    rcases hcover w hwU hwD with hf | hg
    · exact Or.inl (hwk.symm.trans hf)
    · exact Or.inr (hwk.symm.trans hg)
  refine ⟨U, f, g, hUopen, hxU, happroach, hcomplete, ?_⟩
  intro hmaps
  obtain ⟨v, hv⟩ := ConnectedComponents.surjective_coe f
  have hvJ : v.1 ∈ (P.edgeSupport C)ᶜ :=
    fun h => v.2 (P.edgeSupport_subset_drawnSet C h)
  have hvmap : P.faceMap_edgeSupport C f = ConnectedComponents.mk ⟨v.1, hvJ⟩ := by
    rw [← hv]
    exact P.faceMap_edgeSupport_mk C v
  obtain ⟨w, hwJ, hdiff⟩ := P.graphCycle_exists_otherSide hC v.1 hvJ
  have hboundary := P.graphCycle_component_boundary hC w hwJ
    (P.graphCycle_exists_otherSide hC w hwJ)
  have hxcl : x ∈ closure (connectedComponentIn (P.edgeSupport C)ᶜ w) := by
    apply frontier_subset_closure
    rw [hboundary]
    exact hx
  obtain ⟨z, hzU, hzComp⟩ := mem_closure_iff.mp hxcl U hUopen hxU
  have hzJ : z ∈ (P.edgeSupport C)ᶜ := connectedComponentIn_subset _ _ hzComp
  have hzD : z ∉ P.drawnSet := fun h => hzJ ((hagree z (hUsub hzU)).mp h)
  have hzmap := P.faceMap_edgeSupport_mk_eq_of_mem_component C w hwJ z hzD hzComp
  have hsame : P.faceMap_edgeSupport C (ConnectedComponents.mk ⟨z, hzD⟩) =
      P.faceMap_edgeSupport C f := by
    rcases hcover z hzU hzD with hf | hg
    · rw [hf]
    · rw [hg]; exact hmaps.symm
  have hmk := hzmap.symm.trans (hsame.trans hvmap)
  apply hdiff
  rw [connectedComponentIn_eq_image hwJ, connectedComponentIn_eq_image hvJ]
  exact congrArg (Set.image (Subtype.val :
    {z : ℝ × ℝ // z ∉ P.edgeSupport C} → ℝ × ℝ))
      ((ConnectedComponents.coe_eq_coe).mp hmk)

/-- For an edge contained in a cycle, a full face approaching one interior
point approaches every interior point. Local two-face neighborhoods make the
incidence set clopen in the connected parameter interval. -/
theorem PlaneEmbedding.graphCycle_edge_incidence_all_interior
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    {C : Set β} (hC : G.IsGraphCycle C) (e : G.EdgeIndex) (he : (e : β) ∈ C)
    (f : P.Face) (t : I) (ht : IsInteriorTime t)
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
    obtain ⟨U, a, b, hU, hsU, happroach, hcomplete, _⟩ :=
      P.graphCycle_local_faces hV hE hC e he s.1 s.2
    have hpair := hcomplete _ hsU f hs
    have hsub : trace ⁻¹' U ⊆ A := by
      intro s' hs'
      have hsC : trace s' ∈ P.edgeSupport C := by
        simp only [PlaneEmbedding.edgeSupport, Set.mem_iUnion]
        exact ⟨e, he, s'.1, rfl⟩
      have hcl := happroach _ hs' hsC
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

/-- Every edge belonging to a primal cycle has exactly two incident full
faces. The same pair works along its entire interior, and the pair lies on
opposite sides of any selected cycle containing that edge. -/
theorem PlaneEmbedding.graphCycle_edge_has_complete_incidentFaces
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    {C : Set β} (hC : G.IsGraphCycle C) (e : G.EdgeIndex) (he : (e : β) ∈ C) :
    ∃ f g : P.Face,
      P.FaceIncident e f ∧ P.FaceIncident e g ∧
      (∀ k : P.Face, P.FaceIncident e k → k = f ∨ k = g) ∧
      P.faceMap_edgeSupport C f ≠ P.faceMap_edgeSupport C g := by
  let t : I := ⟨1 / 2, by norm_num⟩
  have ht : IsInteriorTime t := by norm_num [IsInteriorTime, t]
  obtain ⟨U, f, g, _, hxU, happroach, hcomplete, hopposite⟩ :=
    P.graphCycle_local_faces hV hE hC e he t ht
  have hxC : P.edgePath e t ∈ P.edgeSupport C := by
    simp only [PlaneEmbedding.edgeSupport, Set.mem_iUnion]
    exact ⟨e, he, t, rfl⟩
  have hcl := happroach _ hxU hxC
  refine ⟨f, g, ⟨t, ht, hcl.1⟩, ⟨t, ht, hcl.2⟩, ?_, hopposite⟩
  intro k hk
  obtain ⟨s, hs, hsk⟩ := hk
  exact hcomplete _ hxU k
    (P.graphCycle_edge_incidence_all_interior hV hE hC e he k s hs hsk t ht)

/-- A complete edge-face assignment straddles every cycle, without the
previous global finite-face assumption. -/
theorem PlaneEmbedding.faceBoundary_cycleSide_eq_of_complete_incidence_no_faceFinite
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    {C : Set β} (hC : G.IsGraphCycle C)
    (sides : G.EdgeIndex → P.Face × P.Face)
    (hinc : ∀ e, P.FaceIncident e (sides e).1 ∧ P.FaceIncident e (sides e).2)
    (hcomplete : ∀ e f, P.FaceIncident e f → f = (sides e).1 ∨ f = (sides e).2)
    (a : ConnectedComponents ((P.edgeSupport C)ᶜ : Set (ℝ × ℝ))) :
    P.faceBoundary sides {f | P.faceMap_edgeSupport C f = a} = C := by
  apply P.faceBoundary_cycleSide_eq_of_opposite hC sides hinc
  intro e he
  obtain ⟨f, g, hf, hg, _, hopposite⟩ :=
    P.graphCycle_edge_has_complete_incidentFaces hV hE hC e he
  intro heq
  apply hopposite
  rcases hcomplete e f hf with rfl | rfl <;>
    rcases hcomplete e g hg with rfl | rfl
  · rfl
  · exact heq
  · exact heq.symm
  · rfl

theorem PlaneEmbedding.graphCycles_are_faceBoundaries_of_complete_incidence_no_faceFinite
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    (sides : G.EdgeIndex → P.Face × P.Face)
    (hinc : ∀ e, P.FaceIncident e (sides e).1 ∧ P.FaceIncident e (sides e).2)
    (hcomplete : ∀ e f, P.FaceIncident e f → f = (sides e).1 ∨ f = (sides e).2) :
    ∀ C, G.IsGraphCycle C → ∃ S : Set P.Face, P.faceBoundary sides S = C := by
  intro C hC
  obtain ⟨a, _, _, _⟩ := Nat.card_eq_two_iff.mp (P.graphCycle_complement_card hC)
  exact ⟨{f | P.faceMap_edgeSupport C f = a},
    P.faceBoundary_cycleSide_eq_of_complete_incidence_no_faceFinite hV hE hC sides
      hinc hcomplete a⟩

/-- When every edge belongs to a cycle, the local result supplies one complete
incident-face assignment for the whole drawing. This is an edgewise subcase;
it does not assert the missing bridge-edge result or N268. -/
theorem PlaneEmbedding.exists_complete_incidence_of_each_edge_on_cycle
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    (hcyclic : ∀ e : G.EdgeIndex, ∃ C, G.IsGraphCycle C ∧ (e : β) ∈ C) :
    ∃ sides : G.EdgeIndex → P.Face × P.Face,
      (∀ e, P.FaceIncident e (sides e).1 ∧ P.FaceIncident e (sides e).2) ∧
      (∀ e f, P.FaceIncident e f → f = (sides e).1 ∨ f = (sides e).2) := by
  classical
  have hpairs : ∀ e : G.EdgeIndex, ∃ p : P.Face × P.Face,
      (P.FaceIncident e p.1 ∧ P.FaceIncident e p.2) ∧
      (∀ f, P.FaceIncident e f → f = p.1 ∨ f = p.2) := by
    intro e
    obtain ⟨C, hC, he⟩ := hcyclic e
    obtain ⟨f, g, hf, hg, hcomplete, _⟩ :=
      P.graphCycle_edge_has_complete_incidentFaces hV hE hC e he
    exact ⟨(f, g), ⟨hf, hg⟩, hcomplete⟩
  choose sides hinc hcomplete using hpairs
  exact ⟨sides, hinc, hcomplete⟩

/-- Reuse the existing N268 reduction after discharging the cycle-boundary
clause by relative Schoenflies. Complete incidence for all edges and the
nonempty-boundary/cycle clause are the only supplied geometric hypotheses;
global face finiteness is unnecessary. -/
theorem PlaneEmbedding.hasCycleBondFaceDual_of_complete_incidence_and_boundaryCycle
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    (sides : G.EdgeIndex → P.Face × P.Face)
    (hinc : ∀ e, P.FaceIncident e (sides e).1 ∧ P.FaceIncident e (sides e).2)
    (hcomplete : ∀ e f, P.FaceIncident e f → f = (sides e).1 ∨ f = (sides e).2)
    (hboundary : ∀ S : Set P.Face, (P.faceBoundary sides S).Nonempty →
      ∃ C, G.IsGraphCycle C ∧ C ⊆ P.faceBoundary sides S) :
    P.HasCycleBondFaceDual := by
  apply (P.hasCycleBondFaceDual_iff_geometric_conditions hE).mpr
  exact ⟨sides, hinc,
    P.graphCycles_are_faceBoundaries_of_complete_incidence_no_faceFinite hV hE sides
      hinc hcomplete, hboundary⟩

/-- The remaining boundary hypothesis can be stated just as exclusion of
nonempty forest boundaries. Circuit extraction and matroid duality are
already available, so no further topological converse is assumed. -/
theorem PlaneEmbedding.hasCycleBondFaceDual_of_complete_incidence_and_forestBoundary
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    (sides : G.EdgeIndex → P.Face × P.Face)
    (hinc : ∀ e, P.FaceIncident e (sides e).1 ∧ P.FaceIncident e (sides e).2)
    (hcomplete : ∀ e f, P.FaceIncident e f → f = (sides e).1 ∨ f = (sides e).2)
    (hforest : ∀ S : Set P.Face, G.IsForestIn (P.faceBoundary sides S) →
      P.faceBoundary sides S = ∅) :
    P.HasCycleBondFaceDual := by
  apply P.hasCycleBondFaceDual_of_complete_incidence_and_boundaryCycle hV hE sides
    hinc hcomplete
  intro S hS
  have hdep : (Matroid.graphic G hE).Dep (P.faceBoundary sides S) := by
    apply Matroid.dep_iff.mpr
    refine ⟨?_, by simpa using P.faceBoundary_subset_edgeSet sides S⟩
    intro hind
    have hempty := hforest S ((Matroid.graphic_indep_iff G hE _).mp hind).2
    simp [hempty] at hS
  obtain ⟨C, hCsub, hC⟩ := hdep.exists_isCircuit_subset
  exact ⟨C, (graphic_isCircuit_iff_isGraphCycle G hE C).mp hC, hCsub⟩

end Graph
