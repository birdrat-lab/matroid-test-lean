import Matroid.Internal.SimpleCycleTrace
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Density of finite plane drawings

The core obstruction is that a continuous injection of a circle into an
interval cannot exist. A hypothetical open disk inside an embedded edge
arc would give such an injection. Loop edges use their Jordan boundary.
-/

open Set unitInterval

private abbrev unitSphere : Type := Metric.sphere (0 : ℝ × ℝ) 1

private def antipode (z : unitSphere) : unitSphere :=
  ⟨-z.1, by simpa [unitSphere, Metric.mem_sphere, dist_eq_norm] using z.2⟩

private theorem antipode_twice (z : unitSphere) : antipode (antipode z) = z := by
  apply Subtype.ext
  simp [antipode]

private theorem antipode_ne (z : unitSphere) : antipode z ≠ z := by
  intro h
  have hv : -z.1 = z.1 := congrArg Subtype.val h
  have hfst : -z.1.1 = z.1.1 := congrArg Prod.fst hv
  have hsnd : -z.1.2 = z.1.2 := congrArg Prod.snd hv
  have hz : z.1 = (0, 0) := by
    ext <;> simp_all only [neg_eq_iff_add_eq_zero] <;> linarith
  have hzdist : dist z.1 (0 : ℝ × ℝ) = 1 := z.2
  simp [hz] at hzdist

private theorem antipode_continuous : Continuous antipode := by
  exact continuous_neg.comp continuous_subtype_val |>.subtype_mk _

private theorem no_continuous_injective_sphere_interval
    (f : unitSphere → I) (hf : Continuous f) : ¬ Function.Injective f := by
  intro hinj
  have hrank : 1 < Module.rank ℝ (ℝ × ℝ) := by
    norm_num [rank_prod']
  letI : PreconnectedSpace unitSphere :=
    Subtype.preconnectedSpace (isPreconnected_sphere hrank 0 1)
  let g : unitSphere → ℝ := fun z => (f z : ℝ) - (f (antipode z) : ℝ)
  have hg : Continuous g := by
    dsimp [g]
    exact (continuous_subtype_val.comp hf).sub
      ((continuous_subtype_val.comp hf).comp antipode_continuous)
  have hodd (z : unitSphere) : g (antipode z) = -g z := by
    simp [g, antipode_twice]
  have hroot : ∃ z : unitSphere, g z = 0 := by
    let z : unitSphere :=
      ⟨(1, 0), by norm_num [unitSphere, Metric.mem_sphere, dist_eq_norm]⟩
    by_cases h : 0 ≤ g z
    · obtain ⟨w, hw⟩ := (mem_range_of_exists_le_of_exists_ge hg
        ⟨antipode z, by simp [hodd, h]⟩ ⟨z, h⟩ : 0 ∈ Set.range g)
      exact ⟨w, hw⟩
    · have hle : g z ≤ 0 := le_of_lt (lt_of_not_ge h)
      obtain ⟨w, hw⟩ := (mem_range_of_exists_le_of_exists_ge hg
        ⟨z, hle⟩ ⟨antipode z, by simp [hodd, hle]⟩ : 0 ∈ Set.range g)
      exact ⟨w, hw⟩
  obtain ⟨z, hz⟩ := hroot
  have hfeq : f z = f (antipode z) := by
    apply Subtype.ext
    exact sub_eq_zero.mp hz
  exact antipode_ne z (hinj hfeq).symm

/-- The interval obstruction used for graph edges also applies to any
embedded arc in the drawing plane. -/
theorem plane_dense_compl_of_arc (A : Set (ℝ × ℝ)) (e : A ≃ₜ I) : Dense Aᶜ := by
  apply interior_eq_empty_iff_dense_compl.mp
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨R, hR, hball⟩ :=
    Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  let r : ℝ := R / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hrR : r < R := by dsimp [r]; linarith
  let q : unitSphere → A := fun z =>
    ⟨x + r • z.1, hball (by
      have hz : ‖z.1‖ = 1 := by
        simpa [unitSphere, Metric.mem_sphere, dist_eq_norm] using z.2
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_pos hr, hz, mul_one]
      exact hrR)⟩
  have hq : Continuous q := by
    have hbase : Continuous (fun z : unitSphere => x + r • (z : ℝ × ℝ)) := by fun_prop
    exact hbase.subtype_mk _
  have hqinj : Function.Injective q := by
    intro a b hab
    have hv : x + r • a.1 = x + r • b.1 := congrArg Subtype.val hab
    have hsmul : r • a.1 = r • b.1 := add_left_cancel hv
    apply Subtype.ext
    apply Prod.ext
    · exact mul_left_cancel₀ hr.ne' (by
        simpa only [Prod.smul_fst, smul_eq_mul] using congrArg Prod.fst hsmul)
    · exact mul_left_cancel₀ hr.ne' (by
        simpa only [Prod.smul_snd, smul_eq_mul] using congrArg Prod.snd hsmul)
  exact no_continuous_injective_sphere_interval (e ∘ q)
    (e.continuous.comp hq) (e.injective.comp hqinj)

namespace Graph
/-- The support of a Jordan trace has empty interior in the drawing plane. -/
theorem PlaneEmbedding.dense_compl_jordanSupport {α β : Type*} {G : Graph α β}
    (P : PlaneEmbedding G) (C : Set β) (htrace : P.HasJordanTrace C) :
    Dense (P.edgeSupport C)ᶜ := by
  obtain ⟨a, b, hab, _⟩ := Nat.card_eq_two_iff.mp
    (P.edgeSupport_complement_card_of_jordanTrace C htrace)
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe b
  have hdiff : connectedComponentIn (P.edgeSupport C)ᶜ (y : ℝ × ℝ) ≠
      connectedComponentIn (P.edgeSupport C)ᶜ (x : ℝ × ℝ) := by
    intro heq
    apply hab
    have hym : (y : ℝ × ℝ) ∈
        connectedComponentIn (P.edgeSupport C)ᶜ (x : ℝ × ℝ) := by
      rw [← heq]
      exact mem_connectedComponentIn y.2
    rw [connectedComponentIn_eq_image x.2] at hym
    obtain ⟨z, hz, hzy⟩ := hym
    have hzeq : z = y := Subtype.ext hzy
    exact (ConnectedComponents.coe_eq_coe').2 (hzeq ▸ hz) |>.symm
  have hfront := P.edgeSupport_component_boundary_of_jordanTrace C htrace
    (x : ℝ × ℝ) x.2 ⟨(y : ℝ × ℝ), y.2, hdiff⟩
  obtain ⟨r, hc, _, hr⟩ := htrace
  have hclosed : IsClosed (P.edgeSupport C) := by
    rw [← hr]
    exact (isCompact_range hc).isClosed
  have hUopen : IsOpen
      (connectedComponentIn (P.edgeSupport C)ᶜ (x : ℝ × ℝ)) :=
    hclosed.isOpen_compl.connectedComponentIn
  apply interior_eq_empty_iff_dense_compl.mp
  rw [← hfront, ← frontier_compl]
  exact interior_frontier hUopen.isClosed_compl

/-- Every actual edge path of a crossing-free plane drawing has dense
complement, including loop edges. -/
theorem PlaneEmbedding.dense_compl_edgePath {α β : Type*} {G : Graph α β}
    (P : PlaneEmbedding G) (e : G.EdgeIndex) :
    Dense (Set.range (P.edgePath e))ᶜ := by
  by_cases hloop : (P.ends e).1 = (P.ends e).2
  · have hS : P.edgeSupport {(e : β)} = Set.range (P.edgePath e) := by
      ext z
      simp only [PlaneEmbedding.edgeSupport, Set.mem_iUnion, Set.mem_singleton_iff,
        Set.mem_range]
      constructor
      · rintro ⟨f, hf, t, rfl⟩
        have hfe : f = e := Subtype.ext hf
        subst f
        exact ⟨t, rfl⟩
      · rintro ⟨t, rfl⟩
        exact ⟨e, rfl, t, rfl⟩
    rw [← hS]
    exact P.dense_compl_jordanSupport {(e : β)}
      (P.loopEdge_hasJordanTrace e hloop)
  · exact plane_dense_compl_of_arc (Set.range (P.edgePath e))
      (P.edgeArcHomeomorph e hloop)

/-- The complement of every finite plane drawing is dense. -/
theorem PlaneEmbedding.dense_compl_drawnSet {α β : Type*} {G : Graph α β}
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite)
    (hE : G.edgeSet.Finite) : Dense P.drawnSetᶜ :=
  P.dense_compl_of_edge_ranges_dense hV hE P.dense_compl_edgePath

/-- Every face after deleting edges receives a face of the original finite
drawing. -/
theorem PlaneEmbedding.faceMap_deleteEdges_surjective_of_finite
    {α β : Type*} {G : Graph α β} (P : PlaneEmbedding G)
    (F : Set β) (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite) :
    Function.Surjective (P.faceMap_deleteEdges F) :=
  P.faceMap_deleteEdges_surjective F hV hE
    (P.dense_compl_drawnSet hV hE)

/-- Every cycle side contains a face of a finite full drawing. -/
theorem PlaneEmbedding.faceMap_edgeSupport_surjective_of_finite
    {α β : Type*} {G : Graph α β} (P : PlaneEmbedding G)
    (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    {C : Set β} (hC : G.IsGraphCycle C) :
    Function.Surjective (P.faceMap_edgeSupport C) :=
  P.faceMap_edgeSupport_surjective_of_dense hC
    (P.dense_compl_drawnSet hV hE)

/-- With finitely many full faces, each edge of a minimal cycle has two
distinct incident faces, one on each Jordan side. -/
theorem PlaneEmbedding.graphCycle_exists_two_incidentFaces_of_finite
    {α β : Type*} {G : Graph α β} (P : PlaneEmbedding G)
    (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    {C : Set β} (hC : G.IsGraphCycle C) (hfaces : Finite P.Face)
    (e : G.EdgeIndex) (he : (e : β) ∈ C)
    (x : ℝ × ℝ) (hx : x ∈ (P.edgeSupport C)ᶜ) :
    ∃ f g : P.Face, f ≠ g ∧ P.FaceIncident e f ∧ P.FaceIncident e g ∧
      P.faceMap_edgeSupport C f ≠ P.faceMap_edgeSupport C g :=
  P.graphCycle_exists_two_incidentFaces hC
    (P.dense_compl_drawnSet hV hE) hfaces e he x hx
end Graph
