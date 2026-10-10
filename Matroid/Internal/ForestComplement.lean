import Matroid.Internal.ForestLift

/-! # Nonseparation of the actual finite forest support

The forest-specific circle extension from `ForestLift` contradicts the
imported `JordanCurve.Brouwer.no_retraction` if a complementary component
is bounded. The remaining component bookkeeping uses the imported
connected exterior of a disk. No polygonal replacement is made.
-/

open Set Metric Bornology

namespace Graph
variable {α β : Type*} {G : Graph α β}

/-- A finite embedded forest cannot have a bounded complementary component.
The topological obstruction is the proved no-retraction theorem imported
from the pinned Jordan development. -/
theorem PlaneEmbedding.forest_component_not_bounded
    (P : PlaneEmbedding G) (hE : G.edgeSet.Finite)
    (D : Set β) (hf : G.IsForestIn D)
    (o : JordanCurve.Plane)
    (ho : o ∉ schoenfliesPlaneHomeomorph '' P.edgeSupport D) :
    ¬ IsBounded (connectedComponentIn
      (schoenfliesPlaneHomeomorph '' P.edgeSupport D)ᶜ o) := by
  classical
  let E := schoenfliesPlaneHomeomorph
  let A := E '' P.edgeSupport D
  let K := connectedComponentIn Aᶜ o
  have hAc : IsCompact A := (P.isCompact_edgeSupport hE D).image E.continuous
  have hoK : o ∈ K := mem_connectedComponentIn ho
  have hKo : IsOpen K := hAc.isClosed.isOpen_compl.connectedComponentIn
  have hfront : frontier K ⊆ A := by
    intro x hx
    by_contra hxA
    have hxo : IsOpen (connectedComponentIn Aᶜ x) :=
      hAc.isClosed.isOpen_compl.connectedComponentIn
    have hxx : x ∈ connectedComponentIn Aᶜ x := mem_connectedComponentIn hxA
    obtain ⟨w, hwx, hwK⟩ := (_root_.mem_closure_iff.mp (frontier_subset_closure hx)) _ hxo hxx
    have hEq : connectedComponentIn Aᶜ x = K :=
      (connectedComponentIn_eq hwx).trans (connectedComponentIn_eq hwK).symm
    have hxK : x ∈ K := hEq ▸ hxx
    have hx' : x ∈ K ∩ frontier K := ⟨hxK, hx⟩
    simpa only [hKo.inter_frontier_eq, notMem_empty] using hx'
  intro hb
  obtain ⟨R, hR, hKR⟩ : ∃ R : ℝ, 0 < R ∧ K ⊆ ball o R := by
    obtain ⟨r, hr⟩ := hb.subset_closedBall o
    refine ⟨max r 0 + 1, by positivity, hr.trans (closedBall_subset_ball ?_)⟩
    exact lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
  let r : JordanCurve.Plane → JordanCurve.Plane := fun z => ‖z - o‖⁻¹ • (z - o)
  have hrnorm : ∀ z, z ≠ o → ‖r z‖ = 1 :=
    fun z hz => norm_smul_inv_norm (sub_ne_zero.mpr hz)
  have hne : ∀ x : P.edgeSupport D, E x ≠ o := by
    intro x h
    exact ho ⟨x, x.2, h⟩
  let f : C(P.edgeSupport D, sphere (0 : JordanCurve.Plane) 1) :=
    ⟨fun x => ⟨r (E x), by simpa [mem_sphere, dist_zero_right] using hrnorm (E x) (hne x)⟩,
      (by
        apply Continuous.subtype_mk
        have hc : Continuous (fun x : P.edgeSupport D => E x - o) :=
          (E.continuous.comp continuous_subtype_val).sub continuous_const
        exact (hc.norm.inv₀ (fun x => norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hne x)))).smul hc)⟩
  obtain ⟨F, hF⟩ := P.forest_sphere_extension hE D hf f
  let H : JordanCurve.Plane → JordanCurve.Plane := fun z => (F (E.symm z) : JordanCurve.Plane)
  have hHc : Continuous H := continuous_subtype_val.comp (F.continuous.comp E.symm.continuous)
  have hHnorm : ∀ z, ‖H z‖ = 1 := by
    intro z
    simpa [H, mem_sphere, dist_zero_right] using (F (E.symm z)).property
  have hHr : ∀ z ∈ A, H z = r z := by
    rintro z ⟨x, hx, rfl⟩
    change (F (E.symm (E x)) : JordanCurve.Plane) = _
    rw [E.symm_apply_apply, hF ⟨x, hx⟩]
    rfl
  let Q := K.piecewise H r
  have hQc : Continuous Q := by
    apply continuous_piecewise (fun z hz => hHr z (hfront hz)) hHc.continuousOn
    rw [hKo.isClosed_compl.closure_eq]
    have hn : ∀ z ∈ Kᶜ, z - o ≠ 0 := by
      intro z hz heq
      exact hz (sub_eq_zero.mp heq ▸ hoK)
    exact ((continuous_id.sub continuous_const).continuousOn.norm.inv₀
      (fun z hz => norm_ne_zero_iff.mpr (hn z hz))).smul
      (continuous_id.sub continuous_const).continuousOn
  have hQnorm : ∀ z, ‖Q z‖ = 1 := by
    intro z
    by_cases hz : z ∈ K
    · simpa [Q, hz] using hHnorm z
    · simpa [Q, hz] using hrnorm z (fun heq => hz (heq ▸ hoK))
  let ρ : C(closedBall (0 : JordanCurve.Plane) 1, closedBall (0 : JordanCurve.Plane) 1) :=
    ⟨fun x => ⟨Q (o + R • (x : JordanCurve.Plane)), by
        rw [mem_closedBall, dist_zero_right, hQnorm]⟩,
      (by
        apply Continuous.subtype_mk
        exact hQc.comp (continuous_const.add (continuous_subtype_val.const_smul R)))⟩
  apply JordanCurve.Brouwer.no_retraction ρ
  · intro x
    simpa [ρ, mem_sphere, dist_zero_right] using hQnorm (o + R • (x : JordanCurve.Plane))
  · intro x hx
    have hxn : ‖(x : JordanCurve.Plane)‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hx
    have hdist : ‖o + R • (x : JordanCurve.Plane) - o‖ = R := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_pos hR, hxn]
    have hxK : o + R • (x : JordanCurve.Plane) ∉ K := by
      intro hk
      have := hKR hk
      rw [mem_ball, dist_eq_norm, hdist] at this
      exact lt_irrefl R this
    change Q (o + R • (x : JordanCurve.Plane)) = (x : JordanCurve.Plane)
    rw [show Q (o + R • (x : JordanCurve.Plane)) = r (o + R • (x : JordanCurve.Plane))
      from piecewise_eq_of_notMem K H r hxK]
    dsimp only [r]
    rw [hdist, add_sub_cancel_left]
    rw [smul_smul, inv_mul_cancel₀ hR.ne', one_smul]

/-- The complement of every actual finite forest edge support is connected
in the sense needed by the retained N268 reduction. -/
theorem PlaneEmbedding.forest_edge_complement_preconnected
    (P : PlaneEmbedding G) (hE : G.edgeSet.Finite)
    (D : Set β) (hf : G.IsForestIn D) :
    IsPreconnected (P.edgeSupport D)ᶜ := by
  let E := schoenfliesPlaneHomeomorph
  let A := E '' P.edgeSupport D
  have hAc : IsCompact A := (P.isCompact_edgeSupport hE D).image E.continuous
  obtain ⟨r, hr⟩ := hAc.isBounded.subset_closedBall (0 : JordanCurve.Plane)
  let R := max r 0
  have hR : 0 ≤ R := le_max_right _ _
  have hAR : A ⊆ closedBall 0 R := hr.trans (closedBall_subset_closedBall (le_max_left _ _))
  let U : Set JordanCurve.Plane := {z | R < ‖z‖}
  have hUc : IsConnected U := JordanCurve.isConnected_compl_closedBall hR
  have hUA : U ⊆ Aᶜ := by
    intro z hz hzA
    have := hAR hzA
    rw [mem_closedBall, dist_zero_right] at this
    exact not_le.mpr hz this
  obtain ⟨p, hp⟩ := hUc.nonempty
  have hUcomp : U ⊆ connectedComponentIn Aᶜ p :=
    hUc.2.subset_connectedComponentIn hp hUA
  have hsub : Aᶜ ⊆ connectedComponentIn Aᶜ p := by
    intro x hx
    have hnb := P.forest_component_not_bounded hE D hf x hx
    have hmeet : ∃ w ∈ U, w ∈ connectedComponentIn Aᶜ x := by
      by_contra h
      push Not at h
      apply hnb
      have hbR : IsBounded (closedBall (0 : JordanCurve.Plane) R) := isBounded_closedBall
      apply hbR.subset
      intro w hw
      rw [mem_closedBall, dist_zero_right]
      exact not_lt.mp (fun hlt => h w hlt hw)
    obtain ⟨w, hwU, hwx⟩ := hmeet
    have heq : connectedComponentIn Aᶜ x = connectedComponentIn Aᶜ p :=
      (connectedComponentIn_eq hwx).trans (connectedComponentIn_eq (hUcomp hwU)).symm
    exact heq ▸ mem_connectedComponentIn hx
  have hc : IsPreconnected Aᶜ := by
    rw [subset_antisymm hsub (connectedComponentIn_subset Aᶜ p)]
    exact isPreconnected_connectedComponentIn
  have ht := hc.image E.symm E.symm.continuous.continuousOn
  rw [← image_compl_eq E.bijective, image_image] at ht
  simpa only [Homeomorph.symm_apply_apply, image_id'] using ht

/-- N268: the faces of the original finite labeled drawing form an
edge-corresponding dual with both cycle-bond correspondences. -/
theorem PlaneEmbedding.hasCycleBondFaceDual
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite) :
    P.HasCycleBondFaceDual :=
  P.hasCycleBondFaceDual_of_forest_edge_complement hV hE
    (fun D _ hf => P.forest_edge_complement_preconnected hE D hf)

/-- N176: the geometric dual identifies both graphic/cographic matroids on
the original labels, with no supplied duality certificate. -/
theorem PlaneEmbedding.matroid_correspondence
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite) :
    ∃ (H : Graph P.Face β) (hH : H.edgeSet.Finite),
      Matroid.graphic G hE = Matroid.cographic H hH ∧
      Matroid.cographic G hE = Matroid.graphic H hH :=
  P.matroid_correspondence_of_faceDual (P.hasCycleBondFaceDual hV hE) hE

/-- The manuscript's planar graphic/cographic correspondence, starting
from existence of an actual plane embedding. -/
theorem IsPlanar.matroid_correspondence (hP : G.IsPlanar)
    (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite) :
    ∃ (γ : Type) (H : Graph γ β) (hH : H.edgeSet.Finite),
      Matroid.graphic G hE = Matroid.cographic H hH ∧
      Matroid.cographic G hE = Matroid.graphic H hH := by
  obtain ⟨P⟩ := hP
  obtain ⟨H, hH, h⟩ := P.matroid_correspondence hV hE
  exact ⟨P.Face, H, hH, h⟩

end Graph
