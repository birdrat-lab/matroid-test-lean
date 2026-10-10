import Matroid.Internal.CycleWalkTrace
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # A simple vertex order for a labeled minimal connecting set

This auxiliary simple graph records only which vertices can be joined by a
chosen set of original labeled edges. Each adjacency retains a `LinkedOn`
witness so an actual edge label can be chosen for its drawn path. A minimal
connecting edge set must use every label selected by its simple vertex walk.
The general geometric injectivity proof remains separate. -/

namespace Graph
variable {α β : Type*}

private def linkSimpleGraph (G : Graph α β) (A : Set G.EdgeIndex) : SimpleGraph α where
  Adj u v := u ≠ v ∧ G.LinkedOn A u v
  symm := by
    constructor
    intro u v h
    obtain ⟨e, heA, hlink⟩ := h.2
    exact ⟨h.1.symm, e, heA, hlink.symm⟩
  loopless := by
    constructor
    intro u h
    exact h.1 rfl

private theorem reachableOn_to_simpleGraph {G : Graph α β}
    {A : Set G.EdgeIndex} {u v : α} (h : G.ReachableOn A u v) :
    (linkSimpleGraph G A).Reachable u v := by
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail b c _ hlink ih =>
      by_cases hbc : b = c
      · subst c
        exact ih
      · exact ih.trans (SimpleGraph.Adj.reachable ⟨hbc, hlink⟩)

theorem reachableOn_exists_simpleVertexPath {G : Graph α β}
    {A : Set G.EdgeIndex} {u v : α} (h : G.ReachableOn A u v) :
    ∃ p : (linkSimpleGraph G A).Walk u v, p.IsPath :=
  (reachableOn_to_simpleGraph h).exists_isPath

private noncomputable def edgeOfAdj {G : Graph α β} {A : Set G.EdgeIndex}
    {u v : α} (h : (linkSimpleGraph G A).Adj u v) : G.EdgeIndex :=
  Classical.choose h.2

private theorem edgeOfAdj_mem {G : Graph α β} {A : Set G.EdgeIndex}
    {u v : α} (h : (linkSimpleGraph G A).Adj u v) :
    edgeOfAdj h ∈ A := (Classical.choose_spec h.2).1

private theorem edgeOfAdj_link {G : Graph α β} {A : Set G.EdgeIndex}
    {u v : α} (h : (linkSimpleGraph G A).Adj u v) :
    G.IsLink (edgeOfAdj h : β) u v := (Classical.choose_spec h.2).2

private noncomputable def drawAdj {G : Graph α β} (P : PlaneEmbedding G)
    {A : Set G.EdgeIndex} {u v : α} (h : (linkSimpleGraph G A).Adj u v) :
    Path (P.vertexPoint u) (P.vertexPoint v) :=
  Classical.choose (P.exists_injective_linkPath (edgeOfAdj h) (edgeOfAdj_link h) h.1)

private theorem drawAdj_range {G : Graph α β} (P : PlaneEmbedding G)
    {A : Set G.EdgeIndex} {u v : α} (h : (linkSimpleGraph G A).Adj u v) :
    Set.range (drawAdj P h) = Set.range (P.edgePath (edgeOfAdj h)) :=
  (Classical.choose_spec
    (P.exists_injective_linkPath (edgeOfAdj h) (edgeOfAdj_link h) h.1)).1

private theorem drawAdj_injective {G : Graph α β} (P : PlaneEmbedding G)
    {A : Set G.EdgeIndex} {u v : α} (h : (linkSimpleGraph G A).Adj u v) :
    Function.Injective (drawAdj P h) :=
  (Classical.choose_spec
    (P.exists_injective_linkPath (edgeOfAdj h) (edgeOfAdj_link h) h.1)).2

private noncomputable def drawWalk {G : Graph α β} (P : PlaneEmbedding G)
    {A : Set G.EdgeIndex} :
    {u v : α} → (linkSimpleGraph G A).Walk u v →
      Path (P.vertexPoint u) (P.vertexPoint v)
  | _, _, .nil => Path.refl _
  | _, _, .cons h .nil => drawAdj P h
  | _, _, .cons h (.cons h' w) =>
      (drawAdj P h).trans (drawWalk P (.cons h' w))

private noncomputable def walkEdgeSet {G : Graph α β} {A : Set G.EdgeIndex} :
    {u v : α} → (linkSimpleGraph G A).Walk u v → Set G.EdgeIndex
  | _, _, .nil => ∅
  | _, _, .cons h w => {edgeOfAdj h} ∪ walkEdgeSet w

private theorem walkEdgeSet_subset {G : Graph α β} {A : Set G.EdgeIndex}
    {u v : α} (w : (linkSimpleGraph G A).Walk u v) : walkEdgeSet w ⊆ A := by
  induction w with
  | nil => simp [walkEdgeSet]
  | cons h w ih =>
      intro e he
      rcases he with he | he
      · have : e = edgeOfAdj h := Set.mem_singleton_iff.mp he
        subst e
        exact edgeOfAdj_mem h
      · exact ih he

private theorem walkEdgeSet_incident_support {G : Graph α β}
    {A : Set G.EdgeIndex} {u v : α}
    (w : (linkSimpleGraph G A).Walk u v) (e : G.EdgeIndex)
    (he : e ∈ walkEdgeSet w) :
    ∃ a b : α, a ∈ w.support ∧ b ∈ w.support ∧ G.IsLink (e : β) a b := by
  induction w with
  | nil => simp [walkEdgeSet] at he
  | @cons u z v h w ih =>
      rcases he with he | he
      · have he' : e = edgeOfAdj h := Set.mem_singleton_iff.mp he
        subst e
        exact ⟨u, z, by simp, by simp, edgeOfAdj_link h⟩
      · obtain ⟨a, b, ha, hb, hab⟩ := ih he
        exact ⟨a, b, by simpa using List.mem_cons_of_mem u ha,
          by simpa using List.mem_cons_of_mem u hb, hab⟩

private theorem drawAdj_tail_intersection {G : Graph α β}
    (P : PlaneEmbedding G) {A : Set G.EdgeIndex} {u v z : α}
    (h : (linkSimpleGraph G A).Adj u v)
    (w : (linkSimpleGraph G A).Walk v z)
    (hw : ((.cons h w) : (linkSimpleGraph G A).Walk u z).IsPath) :
    Set.range (drawAdj P h) ∩ P.edgeSupportOn (walkEdgeSet w) ⊆
      {P.vertexPoint v} := by
  intro x hx
  have hnot : u ∉ w.support := (SimpleGraph.Walk.cons_isPath_iff h w).mp hw |>.2
  rw [drawAdj_range] at hx
  obtain ⟨hxedge, hxother⟩ := hx
  simp only [PlaneEmbedding.edgeSupportOn, Set.mem_iUnion] at hxother
  obtain ⟨f, hf, hxother⟩ := hxother
  obtain ⟨a, b, ha, hb, hab⟩ := walkEdgeSet_incident_support w f hf
  have hne : edgeOfAdj h ≠ f := by
    intro heq
    subst f
    rcases (edgeOfAdj_link h).eq_and_eq_or_eq_and_eq hab with
      ⟨hua, _⟩ | ⟨hub, _⟩
    · exact hnot (hua ▸ ha)
    · exact hnot (hub ▸ hb)
  have hgeom := P.edgePath_intersection_endpoints (edgeOfAdj h) f hne
    (show x ∈ Set.range (P.edgePath (edgeOfAdj h)) ∩
      Set.range (P.edgePath f) from ⟨hxedge, hxother⟩)
  have hu : u ∈ G.vertexSet := G.left_mem_of_isLink (edgeOfAdj_link h)
  have ha' : a ∈ G.vertexSet := G.left_mem_of_isLink hab
  have hb' : b ∈ G.vertexSet := G.left_mem_of_isLink hab.symm
  have hgeom' : x = P.vertexPoint u ∨ x = P.vertexPoint v := by
    rcases (P.ends_valid (edgeOfAdj h)).eq_and_eq_or_eq_and_eq
      (edgeOfAdj_link h) with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · simpa only [hu, hv] using hgeom.1
    · simpa only [hu, hv, or_comm] using hgeom.1
  have hgeom'' : x = P.vertexPoint a ∨ x = P.vertexPoint b := by
    rcases (P.ends_valid f).eq_and_eq_or_eq_and_eq hab with
      ⟨hae, hbe⟩ | ⟨hae, hbe⟩
    · simpa only [hae, hbe] using hgeom.2
    · simpa only [hae, hbe, or_comm] using hgeom.2
  rcases hgeom' with hxU | hxV
  · rcases hgeom'' with hxA | hxB
    · have hua : u = a := P.vertex_injective hu ha' (hxU.symm.trans hxA)
      exact False.elim (hnot (hua ▸ ha))
    · have hub : u = b := P.vertex_injective hu hb' (hxU.symm.trans hxB)
      exact False.elim (hnot (hub ▸ hb))
  · exact hxV

private theorem walkEdgeSet_reachable {G : Graph α β} {A : Set G.EdgeIndex}
    {u v : α} (w : (linkSimpleGraph G A).Walk u v) :
    G.ReachableOn (walkEdgeSet w) u v := by
  induction w with
  | nil => exact Relation.ReflTransGen.refl
  | cons h w ih =>
      have hstep : G.LinkedOn (walkEdgeSet (.cons h w)) _ _ :=
        ⟨edgeOfAdj h, Set.mem_union_left _ (Set.mem_singleton _), edgeOfAdj_link h⟩
      have hmono : G.LinkedOn (walkEdgeSet w) ≤
          G.LinkedOn ({edgeOfAdj h} ∪ walkEdgeSet w) := by
        intro a b hlink
        obtain ⟨e, he, helink⟩ := hlink
        exact ⟨e, Set.mem_union_right _ he, helink⟩
      exact (Relation.ReflTransGen.single hstep).trans
        (Relation.ReflTransGen.mono hmono _ _ ih)

private theorem drawWalk_range {G : Graph α β} (P : PlaneEmbedding G)
    {A : Set G.EdgeIndex} {u v : α} (w : (linkSimpleGraph G A).Walk u v) :
    Set.range (drawWalk P w) = P.edgeSupportOn (walkEdgeSet w) ∪ {P.vertexPoint u} := by
  induction w with
  | nil => simp [drawWalk, walkEdgeSet, Path.refl_range, P.edgeSupportOn_empty]
  | @cons u v z h w ih =>
      have hstart : P.vertexPoint u ∈ Set.range (P.edgePath (edgeOfAdj h)) := by
        rw [← drawAdj_range P h]
        exact ⟨0, Path.source (drawAdj P h)⟩
      cases w with
      | nil =>
          rw [show drawWalk P (.cons h .nil) = drawAdj P h by rfl,
            drawAdj_range]
          change Set.range (P.edgePath (edgeOfAdj h)) =
            P.edgeSupportOn ({edgeOfAdj h} ∪ ∅) ∪ {P.vertexPoint u}
          rw [Set.union_empty, P.edgeSupportOn_singleton]
          exact (Set.union_eq_left.mpr (Set.singleton_subset_iff.mpr hstart)).symm
      | cons h' w' =>
          rw [show drawWalk P (.cons h (.cons h' w')) =
            (drawAdj P h).trans (drawWalk P (.cons h' w')) by rfl,
            Path.trans_range, drawAdj_range, ih]
          rw [show walkEdgeSet (.cons h (.cons h' w')) =
            {edgeOfAdj h} ∪ walkEdgeSet (.cons h' w') by rfl,
            P.edgeSupportOn_union, P.edgeSupportOn_singleton]
          have hmid : P.vertexPoint v ∈ Set.range (P.edgePath (edgeOfAdj h)) := by
            rw [← drawAdj_range P h]
            exact ⟨1, Path.target (drawAdj P h)⟩
          ext x
          simp only [Set.mem_union, Set.mem_singleton_iff]
          constructor
          · rintro (hx | hx | hx)
            · exact Or.inl (Or.inl hx)
            · exact Or.inl (Or.inr hx)
            · exact Or.inl (Or.inl (hx ▸ hmid))
          · rintro ((hx | hx) | hx)
            · exact Or.inl hx
            · exact Or.inr (Or.inl hx)
            · exact Or.inl (hx ▸ hstart)

private theorem drawWalk_injective_of_isPath {G : Graph α β}
    (P : PlaneEmbedding G) {A : Set G.EdgeIndex} {u v : α}
    (w : (linkSimpleGraph G A).Walk u v) :
    w.IsPath → u ≠ v → Function.Injective (drawWalk P w) := by
  induction w with
  | nil =>
      intro _ hne
      exact False.elim (hne rfl)
  | @cons u v z h w ih =>
      intro hw _
      cases w with
      | nil => exact drawAdj_injective P h
      | cons h' w' =>
          have htail : ((.cons h' w') : (linkSimpleGraph G A).Walk v z).IsPath :=
            (SimpleGraph.Walk.cons_isPath_iff h (.cons h' w')).mp hw |>.1
          have hvz : v ≠ z := by
            intro hvz
            subst z
            exact SimpleGraph.Walk.not_nil_cons
              ((SimpleGraph.Walk.isPath_iff_nil.mp htail))
          have hinter : Set.range (drawAdj P h) ∩
              Set.range (drawWalk P (.cons h' w')) ⊆ {P.vertexPoint v} := by
            intro x hx
            rw [drawWalk_range] at hx
            rcases hx.2 with hxedge | hxvertex
            · exact drawAdj_tail_intersection P h (.cons h' w') hw ⟨hx.1, hxedge⟩
            · exact hxvertex
          exact JordanPath.trans_injective_of_intersection
            (drawAdj P h) (drawWalk P (.cons h' w'))
            (drawAdj_injective P h) (ih htail hvz) hinter

private theorem exists_minimalReachable_simpleWalk {G : Graph α β}
    {A : Set G.EdgeIndex} {u v : α} (hreach : G.ReachableOn A u v)
    (hmin : ∀ D ⊂ A, ¬ G.ReachableOn D u v) :
    ∃ w : (linkSimpleGraph G A).Walk u v,
      w.IsPath ∧ walkEdgeSet w = A := by
  obtain ⟨w, hw⟩ := reachableOn_exists_simpleVertexPath hreach
  refine ⟨w, hw, ?_⟩
  have hsub : walkEdgeSet w ⊆ A := walkEdgeSet_subset w
  by_contra hne
  exact hmin _ (Set.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    (walkEdgeSet_reachable w)

private theorem exists_minimalReachable_simpleDrawnPath {G : Graph α β}
    (P : PlaneEmbedding G) {A : Set G.EdgeIndex} {u v : α}
    (hreach : G.ReachableOn A u v)
    (hmin : ∀ D ⊂ A, ¬ G.ReachableOn D u v) :
    ∃ w : (linkSimpleGraph G A).Walk u v,
      w.IsPath ∧ walkEdgeSet w = A ∧
      Set.range (drawWalk P w) = P.edgeSupportOn A ∪ {P.vertexPoint u} := by
  obtain ⟨w, hw, hset⟩ := exists_minimalReachable_simpleWalk hreach hmin
  exact ⟨w, hw, hset, by simpa [hset] using drawWalk_range P w⟩

/-- A minimal labeled edge set connecting distinct vertices draws an
injective arc with exactly the support of those edges (including its source
vertex). The auxiliary simple graph is confined to the proof. -/
theorem PlaneEmbedding.exists_minimalReachable_drawnArc {G : Graph α β}
    (P : PlaneEmbedding G) {A : Set G.EdgeIndex} {u v : α}
    (huv : u ≠ v) (hreach : G.ReachableOn A u v)
    (hmin : ∀ D ⊂ A, ¬ G.ReachableOn D u v) :
    ∃ p : Path (P.vertexPoint u) (P.vertexPoint v),
      Function.Injective p ∧
      Set.range p = P.edgeSupportOn A ∪ {P.vertexPoint u} := by
  obtain ⟨w, hw, hset, hrange⟩ :=
    exists_minimalReachable_simpleDrawnPath P hreach hmin
  exact ⟨drawWalk P w, drawWalk_injective_of_isPath P w hw huv, hrange⟩

/-- A labeled closing edge meets the drawn support of other labeled edges
only at its own endpoints. -/
theorem PlaneEmbedding.edgeSupportOn_inter_closingEdge {G : Graph α β}
    (P : PlaneEmbedding G) (A : Set G.EdgeIndex) (e : G.EdgeIndex)
    (he : e ∉ A) :
    P.edgeSupportOn A ∩ Set.range (P.edgePath e) ⊆
      {P.vertexPoint (P.ends e).1, P.vertexPoint (P.ends e).2} := by
  intro x hx
  obtain ⟨hxA, hxE⟩ := hx
  simp only [PlaneEmbedding.edgeSupportOn, Set.mem_iUnion] at hxA
  obtain ⟨f, hf, hxF⟩ := hxA
  have hfe : f ≠ e := fun h => he (h ▸ hf)
  have hgeom := P.edgePath_intersection_endpoints f e hfe ⟨hxF, hxE⟩
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hgeom.2

/-- An injectively drawn minimal connecting set, closed by a fresh labeled
edge, has a Jordan trace. This handles parallel edges because edge identity
is retained throughout the proof. -/
theorem PlaneEmbedding.hasJordanTrace_of_minimalClosingEdge {G : Graph α β}
    (P : PlaneEmbedding G) {A : Set G.EdgeIndex} {u v : α}
    (huv : u ≠ v) (hreach : G.ReachableOn A u v)
    (hmin : ∀ D ⊂ A, ¬ G.ReachableOn D u v)
    (e : G.EdgeIndex) (he : e ∉ A)
    (hlink : G.IsLink (e : β) u v) :
    P.HasJordanTrace (G.edgeEmbedding '' (A ∪ {e})) := by
  obtain ⟨p, hpInj, hpRange⟩ :=
    P.exists_minimalReachable_drawnArc huv hreach hmin
  obtain ⟨q, hqRange, hqInj⟩ :=
    P.exists_injective_linkPath e hlink.symm huv.symm
  have hinter : Set.range p ∩ Set.range q ⊆
      {P.vertexPoint u, P.vertexPoint v} := by
    intro x hx
    rw [hpRange, hqRange] at hx
    rcases hx.1 with hxA | hxU
    · have h := P.edgeSupportOn_inter_closingEdge A e he ⟨hxA, hx.2⟩
      rcases (P.ends_valid e).eq_and_eq_or_eq_and_eq hlink with
        ⟨hu, hv⟩ | ⟨hu, hv⟩
      · simpa only [hu, hv] using h
      · simp only [hu, hv, Set.mem_insert_iff, Set.mem_singleton_iff] at h
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h.symm
    · simp only [Set.mem_singleton_iff] at hxU
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inl hxU
  have hsimp : ∀ s t : unitInterval, (s : ℝ) < 1 → (t : ℝ) < 1 →
      p.trans q s = p.trans q t → s = t :=
    JordanPath.trans_simpleClosed_of_two_arcs p q hpInj hqInj hinter
  have huRange : P.vertexPoint u ∈ Set.range (P.edgePath e) := by
    rw [← hqRange]
    exact ⟨1, Path.target q⟩
  have hclosedRange : Set.range (p.trans q) =
      P.edgeSupport (G.edgeEmbedding '' (A ∪ {e})) := by
    rw [Path.trans_range, hpRange, hqRange]
    calc
      (P.edgeSupportOn A ∪ {P.vertexPoint u}) ∪
          Set.range (P.edgePath e) =
          P.edgeSupportOn A ∪ Set.range (P.edgePath e) := by
        ext x
        simp only [Set.mem_union, Set.mem_singleton_iff]
        constructor
        · rintro ((hx | hx) | hx)
          · exact Or.inl hx
          · exact Or.inr (hx ▸ huRange)
          · exact Or.inr hx
        · rintro (hx | hx)
          · exact Or.inl (Or.inl hx)
          · exact Or.inr hx
      _ = _ := by
        rw [← P.edgeSupportOn_singleton e,
          ← P.edgeSupportOn_union, P.edgeSupportOn_eq_support_image]
  exact P.hasJordanTrace_of_simpleClosedPath (p.trans q) hclosedRange hsimp

/-- Every minimal cycle in a labeled plane graph has an injective sphere
trace with exactly its drawn support. The loop case uses the single loop
path; the nonloop case closes the minimal drawn arc by its missing edge. -/
theorem PlaneEmbedding.graphCycle_hasJordanTrace {G : Graph α β}
    (P : PlaneEmbedding G) {C : Set β} (hC : G.IsGraphCycle C) :
    P.HasJordanTrace C := by
  obtain ⟨e, he, u, v, hlink, hreach⟩ := hC.2.1
  by_cases hloop : (P.ends e).1 = (P.ends e).2
  · exact P.graphCycle_hasJordanTrace_of_loop hC e he hloop
  have huv : u ≠ v := by
    intro huv
    subst v
    rcases (P.ends_valid e).eq_and_eq_or_eq_and_eq hlink with
      ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact hloop (hu.trans hv.symm)
    · exact hloop (hu.trans hv.symm)
  let A : Set G.EdgeIndex := (G.edgeEmbedding ⁻¹' C) \ {e}
  have hmin : ∀ D ⊂ A, ¬ G.ReachableOn D u v :=
    isGraphCycle_reachableEdges_minimal hC he hlink (Set.Subset.rfl) hreach
  have heA : e ∉ A := by simp [A]
  have htrace := P.hasJordanTrace_of_minimalClosingEdge
    huv hreach hmin e heA hlink
  have himage : G.edgeEmbedding '' (A ∪ {e}) = C :=
    isGraphCycle_image_reachableEdges_eq hC he hlink Set.Subset.rfl hreach
  change P.HasJordanTrace (G.edgeEmbedding '' (A ∪ {e})) at htrace
  rw [himage] at htrace
  exact htrace

/-- The drawn support of every minimal graph cycle separates the plane into
exactly two connected components. -/
theorem PlaneEmbedding.graphCycle_complement_card {G : Graph α β}
    (P : PlaneEmbedding G) {C : Set β} (hC : G.IsGraphCycle C) :
    Nat.card (ConnectedComponents ((P.edgeSupport C)ᶜ : Set (ℝ × ℝ))) = 2 :=
  P.edgeSupport_complement_card_of_jordanTrace C (P.graphCycle_hasJordanTrace hC)

/-- Each complementary side of a drawn graph cycle has the whole cycle as
its boundary, once a point on the other side is specified. -/
theorem PlaneEmbedding.graphCycle_component_boundary {G : Graph α β}
    (P : PlaneEmbedding G) {C : Set β} (hC : G.IsGraphCycle C)
    (x : ℝ × ℝ) (hx : x ∈ (P.edgeSupport C)ᶜ)
    (hy : ∃ y ∈ (P.edgeSupport C)ᶜ,
      connectedComponentIn (P.edgeSupport C)ᶜ y ≠
        connectedComponentIn (P.edgeSupport C)ᶜ x) :
    frontier (connectedComponentIn (P.edgeSupport C)ᶜ x) =
      P.edgeSupport C :=
  P.edgeSupport_component_boundary_of_jordanTrace C
    (P.graphCycle_hasJordanTrace hC) x hx hy

/-- The complement of the full drawing lies in the complement of the
support of any selected edge set. -/
theorem PlaneEmbedding.edgeSupport_subset_drawnSet {G : Graph α β}
    (P : PlaneEmbedding G) (C : Set β) :
    P.edgeSupport C ⊆ P.drawnSet := by
  intro x hx
  simp only [PlaneEmbedding.edgeSupport, Set.mem_iUnion] at hx
  obtain ⟨e, _, hxe⟩ := hx
  exact Or.inr (Set.mem_iUnion.mpr ⟨e, hxe⟩)

/-- Every face of the full drawing occupies a definite component of the
complement of a selected edge support. For a graph cycle, the target has two
components by `graphCycle_complement_card`. -/
def PlaneEmbedding.faceMap_edgeSupport {G : Graph α β}
    (P : PlaneEmbedding G) (C : Set β) :
    P.Face → ConnectedComponents ((P.edgeSupport C)ᶜ : Set (ℝ × ℝ)) := by
  let incl : {x : ℝ × ℝ // x ∉ P.drawnSet} →
      {x : ℝ × ℝ // x ∉ P.edgeSupport C} :=
    fun x => ⟨x.1, fun hx => x.2 (P.edgeSupport_subset_drawnSet C hx)⟩
  have hcont : Continuous incl := continuous_subtype_val.subtype_mk _
  exact Quotient.lift
    (fun x => ConnectedComponents.mk (incl x))
    (by
      intro x y hxy
      have hy : y ∈ connectedComponent x := by
        rw [hxy]
        exact mem_connectedComponent
      exact (ConnectedComponents.coe_eq_coe'.2
        (hcont.mapsTo_connectedComponent x hy)).symm)

@[simp]
theorem PlaneEmbedding.faceMap_edgeSupport_mk {G : Graph α β}
    (P : PlaneEmbedding G) (C : Set β)
    (x : {x : ℝ × ℝ // x ∉ P.drawnSet}) :
    P.faceMap_edgeSupport C (ConnectedComponents.mk x) =
      ConnectedComponents.mk
        (⟨x.1, fun hx => x.2 (P.edgeSupport_subset_drawnSet C hx)⟩ :
          {x : ℝ × ℝ // x ∉ P.edgeSupport C}) := rfl

/-- A graph cycle's drawn support is closed, as it is the range of its
continuous Jordan trace. -/
theorem PlaneEmbedding.isClosed_edgeSupport_of_graphCycle {G : Graph α β}
    (P : PlaneEmbedding G) {C : Set β} (hC : G.IsGraphCycle C) :
    IsClosed (P.edgeSupport C) := by
  obtain ⟨r, hc, _, hr⟩ := P.graphCycle_hasJordanTrace hC
  rw [← hr]
  exact (isCompact_range hc).isClosed

/-- If the full drawing's complement is dense, every Jordan side of a
graph cycle contains at least one face of the full drawing. This does not
identify the local face incident with any particular edge. -/
theorem PlaneEmbedding.faceMap_edgeSupport_surjective_of_dense
    {G : Graph α β} (P : PlaneEmbedding G)
    {C : Set β} (hC : G.IsGraphCycle C)
    (hdense : Dense P.drawnSetᶜ) :
    Function.Surjective (P.faceMap_edgeSupport C) := by
  intro side
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe side
  let U := connectedComponentIn (P.edgeSupport C)ᶜ (x : ℝ × ℝ)
  have hxU : (x : ℝ × ℝ) ∈ U := mem_connectedComponentIn x.2
  have hUopen : IsOpen U :=
    (P.isClosed_edgeSupport_of_graphCycle hC).isOpen_compl.connectedComponentIn
  obtain ⟨y, hyD, hyU⟩ := hdense.exists_mem_open hUopen ⟨x.1, hxU⟩
  have hyJ : y ∈ (P.edgeSupport C)ᶜ := connectedComponentIn_subset _ _ hyU
  have hycomp :
      (⟨y, hyJ⟩ : {z : ℝ × ℝ // z ∉ P.edgeSupport C}) ∈ connectedComponent x := by
    change y ∈ connectedComponentIn (P.edgeSupport C)ᶜ (x : ℝ × ℝ) at hyU
    rw [connectedComponentIn_eq_image x.2] at hyU
    obtain ⟨z, hz, hzy⟩ := hyU
    have hzeq : z = ⟨y, hyJ⟩ := Subtype.ext hzy
    exact hzeq ▸ hz
  refine ⟨ConnectedComponents.mk ⟨y, hyD⟩, ?_⟩
  rw [P.faceMap_edgeSupport_mk]
  exact (ConnectedComponents.coe_eq_coe').2 hycomp

/-- A point of a Jordan side lies in a full face assigned to that side. -/
theorem PlaneEmbedding.faceMap_edgeSupport_mk_eq_of_mem_component
    {G : Graph α β} (P : PlaneEmbedding G) (C : Set β)
    (x : ℝ × ℝ) (hx : x ∈ (P.edgeSupport C)ᶜ)
    (y : ℝ × ℝ) (hyD : y ∈ P.drawnSetᶜ)
    (hyU : y ∈ connectedComponentIn (P.edgeSupport C)ᶜ x) :
    P.faceMap_edgeSupport C (ConnectedComponents.mk ⟨y, hyD⟩) =
      ConnectedComponents.mk ⟨x, hx⟩ := by
  have hyJ : y ∈ (P.edgeSupport C)ᶜ := connectedComponentIn_subset _ _ hyU
  rw [P.faceMap_edgeSupport_mk]
  have hycomp :
      (⟨y, hyJ⟩ : {z : ℝ × ℝ // z ∉ P.edgeSupport C}) ∈
        connectedComponent (⟨x, hx⟩ : {z : ℝ × ℝ // z ∉ P.edgeSupport C}) := by
    rw [connectedComponentIn_eq_image hx] at hyU
    obtain ⟨z, hz, hzy⟩ := hyU
    have hzeq : z = ⟨y, hyJ⟩ := Subtype.ext hzy
    exact hzeq ▸ hz
  exact (ConnectedComponents.coe_eq_coe').2 hycomp

/-- Under density and finiteness of the full drawing's faces, a point in
the closure of a Jordan side is approached by a full face assigned to that
same side. -/
theorem PlaneEmbedding.exists_face_closure_on_cycleSide
    {G : Graph α β} (P : PlaneEmbedding G)
    {C : Set β} (hC : G.IsGraphCycle C)
    (hdense : Dense P.drawnSetᶜ) (hfaces : Finite P.Face)
    (x : ℝ × ℝ) (hx : x ∈ (P.edgeSupport C)ᶜ)
    (z : ℝ × ℝ)
    (hz : z ∈ closure (connectedComponentIn (P.edgeSupport C)ᶜ x)) :
    ∃ f : P.Face,
      P.faceMap_edgeSupport C f = ConnectedComponents.mk ⟨x, hx⟩ ∧
        z ∈ closure (P.facePoints f) := by
  letI : Finite P.Face := hfaces
  let U := connectedComponentIn (P.edgeSupport C)ᶜ x
  have hUopen : IsOpen U :=
    (P.isClosed_edgeSupport_of_graphCycle hC).isOpen_compl.connectedComponentIn
  have hUsub : U ⊆ closure (U ∩ P.drawnSetᶜ) := by
    intro y hyU
    apply mem_closure_iff.mpr
    intro O hO hyO
    obtain ⟨w, hwD, hwOU⟩ :=
      hdense.exists_mem_open (hO.inter hUopen) ⟨y, hyO, hyU⟩
    exact ⟨w, hwOU.1, hwOU.2, hwD⟩
  have hzUD : z ∈ closure (U ∩ P.drawnSetᶜ) :=
    closure_minimal hUsub isClosed_closure hz
  let S : Set P.Face :=
    {f | P.faceMap_edgeSupport C f = ConnectedComponents.mk ⟨x, hx⟩}
  let F : Set (ℝ × ℝ) :=
    ⋃ f : S, P.facePoints (f : P.Face)
  have hUDsubF : U ∩ P.drawnSetᶜ ⊆ F := by
    intro y hy
    have hside : P.faceMap_edgeSupport C
        (ConnectedComponents.mk ⟨y, hy.2⟩) =
        ConnectedComponents.mk ⟨x, hx⟩ :=
      P.faceMap_edgeSupport_mk_eq_of_mem_component C x hx y hy.2 hy.1
    exact Set.mem_iUnion.mpr
      ⟨⟨ConnectedComponents.mk ⟨y, hy.2⟩, hside⟩, ⟨hy.2, rfl⟩⟩
  have hzF : z ∈ closure F := closure_mono hUDsubF hzUD
  change z ∈ closure (⋃ f : S, P.facePoints (f : P.Face)) at hzF
  rw [closure_iUnion_of_finite] at hzF
  obtain ⟨f, hf⟩ := Set.mem_iUnion.mp hzF
  exact ⟨f.1, f.2, hf⟩

/-- Every Jordan side of a graph cycle has a distinct other side. -/
theorem PlaneEmbedding.graphCycle_exists_otherSide
    {G : Graph α β} (P : PlaneEmbedding G)
    {C : Set β} (hC : G.IsGraphCycle C)
    (x : ℝ × ℝ) (hx : x ∈ (P.edgeSupport C)ᶜ) :
    ∃ y ∈ (P.edgeSupport C)ᶜ,
      connectedComponentIn (P.edgeSupport C)ᶜ y ≠
        connectedComponentIn (P.edgeSupport C)ᶜ x := by
  let c : ConnectedComponents ((P.edgeSupport C)ᶜ : Set (ℝ × ℝ)) :=
    ConnectedComponents.mk ⟨x, hx⟩
  obtain ⟨d, hdc, _⟩ :=
    (Nat.card_eq_two_iff' c).mp (P.graphCycle_complement_card hC)
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe d
  refine ⟨y.1, y.2, ?_⟩
  intro hcc
  have hcomp : connectedComponent y =
      connectedComponent (⟨x, hx⟩ : {z : ℝ × ℝ // z ∉ P.edgeSupport C}) := by
    apply (Set.image_injective.mpr Subtype.coe_injective)
    simpa only [connectedComponentIn_eq_image y.2,
      connectedComponentIn_eq_image hx] using hcc
  exact hdc ((ConnectedComponents.coe_eq_coe).2 hcomp)

/-- Under dense complement and finite-face hypotheses, every edge in a
graph cycle has a full-drawing incident face on each chosen Jordan side. -/
theorem PlaneEmbedding.graphCycle_exists_incidentFace_on_side
    {G : Graph α β} (P : PlaneEmbedding G)
    {C : Set β} (hC : G.IsGraphCycle C)
    (hdense : Dense P.drawnSetᶜ) (hfaces : Finite P.Face)
    (e : G.EdgeIndex) (he : (e : β) ∈ C)
    (x : ℝ × ℝ) (hx : x ∈ (P.edgeSupport C)ᶜ) :
    ∃ f : P.Face,
      P.faceMap_edgeSupport C f = ConnectedComponents.mk ⟨x, hx⟩ ∧
        P.FaceIncident e f := by
  let t : unitInterval := ⟨1 / 2, by norm_num⟩
  have ht : IsInteriorTime t := by norm_num [IsInteriorTime, t]
  have hpoint : P.edgePath e t ∈ P.edgeSupport C := by
    simp only [PlaneEmbedding.edgeSupport, Set.mem_iUnion]
    exact ⟨e, he, ⟨t, rfl⟩⟩
  have hboundary := P.graphCycle_component_boundary hC x hx
    (P.graphCycle_exists_otherSide hC x hx)
  have hclosure : P.edgePath e t ∈
      closure (connectedComponentIn (P.edgeSupport C)ᶜ x) := by
    apply frontier_subset_closure
    rw [hboundary]
    exact hpoint
  obtain ⟨f, hfside, hfclosure⟩ :=
    P.exists_face_closure_on_cycleSide hC hdense hfaces x hx
      (P.edgePath e t) hclosure
  exact ⟨f, hfside, t, ht, hfclosure⟩

/-- Under the same finite-face and density hypotheses, a cycle edge has
two distinct full-drawing incident faces, one on each Jordan side. -/
theorem PlaneEmbedding.graphCycle_exists_two_incidentFaces
    {G : Graph α β} (P : PlaneEmbedding G)
    {C : Set β} (hC : G.IsGraphCycle C)
    (hdense : Dense P.drawnSetᶜ) (hfaces : Finite P.Face)
    (e : G.EdgeIndex) (he : (e : β) ∈ C)
    (x : ℝ × ℝ) (hx : x ∈ (P.edgeSupport C)ᶜ) :
    ∃ f g : P.Face, f ≠ g ∧ P.FaceIncident e f ∧ P.FaceIncident e g ∧
      P.faceMap_edgeSupport C f ≠ P.faceMap_edgeSupport C g := by
  obtain ⟨y, hy, hside⟩ := P.graphCycle_exists_otherSide hC x hx
  obtain ⟨f, hfmap, hfinc⟩ :=
    P.graphCycle_exists_incidentFace_on_side hC hdense hfaces e he x hx
  obtain ⟨g, hgmap, hginc⟩ :=
    P.graphCycle_exists_incidentFace_on_side hC hdense hfaces e he y hy
  have hmk : (ConnectedComponents.mk ⟨x, hx⟩ :
      ConnectedComponents ((P.edgeSupport C)ᶜ : Set (ℝ × ℝ))) ≠
      ConnectedComponents.mk ⟨y, hy⟩ := by
    intro h
    apply hside
    have hcomp := (ConnectedComponents.coe_eq_coe).mp h.symm
    rw [connectedComponentIn_eq_image hy, connectedComponentIn_eq_image hx]
    exact congrArg (Set.image (Subtype.val :
      {z : ℝ × ℝ // z ∉ P.edgeSupport C} → ℝ × ℝ)) hcomp
  have hfgmap : P.faceMap_edgeSupport C f ≠ P.faceMap_edgeSupport C g := by
    rw [hfmap, hgmap]
    exact hmk
  exact ⟨f, g, fun h => hfgmap (congrArg (P.faceMap_edgeSupport C) h),
    hfinc, hginc, hfgmap⟩

end Graph
