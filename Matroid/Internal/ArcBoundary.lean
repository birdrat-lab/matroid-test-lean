import Matroid.Internal.ForestBoundary
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-! # Arc-supported boundaries

Imported arc nonseparation also excludes boundaries contained in a proper
part of a graph cycle. Finite original vertices are handled using mathlib's
ball homeomorphism and connectedness of the punctured plane.
-/

open Set Metric unitInterval

namespace Graph

private theorem puncturedBall_isPreconnected (x : ℝ × ℝ) {r : ℝ} (hr : 0 < r) :
    IsPreconnected (ball x r \ {x}) := by
  let e := OpenPartialHomeomorph.univBall x r
  have he0 : e 0 = x := OpenPartialHomeomorph.univBall_apply_zero x r
  have htarget : e.target = ball x r := OpenPartialHomeomorph.univBall_target x hr
  have hsource : e.source = univ := OpenPartialHomeomorph.univBall_source x r
  have himage : e '' ({0}ᶜ : Set (ℝ × ℝ)) = ball x r \ {x} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨htarget ▸ e.map_source (hsource ▸ mem_univ w), ?_⟩
      intro hz
      have heq : e w = e 0 := (mem_singleton_iff.mp hz).trans he0.symm
      exact hw (e.injOn (hsource ▸ mem_univ w) (hsource ▸ mem_univ 0) heq)
    · rintro ⟨hz, hzx⟩
      have hzt : z ∈ e.target := htarget.symm ▸ hz
      refine ⟨e.symm z, ?_, e.right_inv hzt⟩
      intro heq
      apply hzx
      rw [mem_singleton_iff]
      have hzero : e.symm z = 0 := mem_singleton_iff.mp heq
      rw [← e.right_inv hzt, hzero, he0]
  rw [← himage]
  exact (isConnected_compl_singleton_of_one_lt_rank (by norm_num) (0 : ℝ × ℝ)).2.image
    e (OpenPartialHomeomorph.continuous_univBall x r).continuousOn

private theorem open_preconnected_sdiff_singleton {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hc : IsPreconnected U) (p : ℝ × ℝ) :
    IsPreconnected (U \ {p}) := by
  classical
  by_cases hp : p ∈ U
  · intro A B hA hB hcover hUA hUB
    by_contra hmeet
    have hdisj : Disjoint (A ∩ (U \ {p})) (B ∩ (U \ {p})) := by
      apply disjoint_left.mpr
      rintro z ⟨hzA, hzU⟩ ⟨hzB, _⟩
      exact hmeet ⟨z, hzU, hzA, hzB⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU p hp
    let V := ball p r \ {p}
    have hVU : V ⊆ U \ {p} := fun z hz => ⟨hball hz.1, hz.2⟩
    have hVne : V.Nonempty := by
      have hd : Dense ({p}ᶜ : Set (ℝ × ℝ)) := (countable_singleton p).dense_compl ℝ
      obtain ⟨z, hz, hzp⟩ := hd.inter_open_nonempty (ball p r) isOpen_ball
        ⟨p, mem_ball_self hr⟩
      exact ⟨z, hz, hzp⟩
    have hone : V ⊆ A ∨ V ⊆ B := by
      have hABopen : IsOpen (A ∩ (U \ {p})) := hA.inter (hU.sdiff isClosed_singleton)
      have hBBopen : IsOpen (B ∩ (U \ {p})) := hB.inter (hU.sdiff isClosed_singleton)
      have hcov : V ⊆ (A ∩ (U \ {p})) ∪ (B ∩ (U \ {p})) := by
        intro z hz
        rcases hcover (hVU hz) with hzA | hzB
        · exact Or.inl ⟨hzA, hVU hz⟩
        · exact Or.inr ⟨hzB, hVU hz⟩
      rcases (puncturedBall_isPreconnected p hr).subset_or_subset hABopen hBBopen
        hdisj hcov with h | h
      · exact Or.inl (fun z hz => (h hz).1)
      · exact Or.inr (fun z hz => (h hz).1)
    have hside : ∀ X Y : Set (ℝ × ℝ), IsOpen X → IsOpen Y →
        (U \ {p}) ⊆ X ∪ Y → ((U \ {p}) ∩ X).Nonempty →
        ((U \ {p}) ∩ Y).Nonempty →
        Disjoint (X ∩ (U \ {p})) (Y ∩ (U \ {p})) → V ⊆ X → False := by
      intro X Y hX hY hcov hUX hUY hXY hVX
      have hpY : p ∉ Y := by
        intro hpY
        have hd : Dense ({p}ᶜ : Set (ℝ × ℝ)) := (countable_singleton p).dense_compl ℝ
        obtain ⟨z, hz, hzp⟩ := hd.inter_open_nonempty (ball p r ∩ Y)
          (isOpen_ball.inter hY) ⟨p, mem_ball_self hr, hpY⟩
        have hzV : z ∈ V := ⟨hz.1, hzp⟩
        exact disjoint_left.mp hXY ⟨hVX hzV, hVU hzV⟩ ⟨hz.2, hVU hzV⟩
      have hcoverU : U ⊆ (X ∪ ball p r) ∪ Y := by
        intro z hz
        by_cases hzp : z = p
        · exact Or.inl (Or.inr (hzp ▸ mem_ball_self hr))
        · rcases hcov ⟨hz, hzp⟩ with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
      obtain ⟨z, hzU, hzX | hzBall, hzY⟩ := hc (X ∪ ball p r) Y
        (hX.union isOpen_ball) hY hcoverU
        (hUX.mono (fun z hz => ⟨hz.1.1, Or.inl hz.2⟩))
        (hUY.mono (fun z hz => ⟨hz.1.1, hz.2⟩))
      · have hzp : z ≠ p := fun h => hpY (h ▸ hzY)
        exact disjoint_left.mp hXY ⟨hzX, hzU, hzp⟩ ⟨hzY, hzU, hzp⟩
      · have hzp : z ≠ p := fun h => hpY (h ▸ hzY)
        have hzV : z ∈ V := ⟨hzBall, hzp⟩
        exact disjoint_left.mp hXY ⟨hVX hzV, hVU hzV⟩ ⟨hzY, hVU hzV⟩
    rcases hone with h | h
    · exact hside A B hA hB hcover hUA hUB hdisj h
    · exact hside B A hB hA (by simpa [union_comm] using hcover)
        hUB hUA hdisj.symm h
  · simpa [sdiff_eq_left.mpr (disjoint_singleton_right.mpr hp)] using hc

/-- Removing finitely many original vertices from an open connected region
does not change its preconnectedness. The local punctured balls are images
of the imported connected punctured plane, not a new disk-separation proof. -/
theorem plane_open_preconnected_sdiff_finite {U F : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hc : IsPreconnected U) (hF : F.Finite) :
    IsPreconnected (U \ F) := by
  induction F, hF using Set.Finite.induction_on with
  | empty => simpa using hc
  | @insert p F hp hF ih =>
    have h := open_preconnected_sdiff_singleton (hU.sdiff hF.isClosed) ih p
    simpa [sdiff_sdiff, union_comm] using h

variable {α β : Type*} {G : Graph α β}

/-- Retaining finitely many original vertices is immaterial for complement
connectivity. This removes isolated vertices from the remaining forest
obligation without changing the graph or its drawing. -/
theorem PlaneEmbedding.retained_complement_preconnected_iff_edge_complement
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    (D : Set β) :
    IsPreconnected (P.vertexPoint '' G.vertexSet ∪ P.edgeSupport D)ᶜ ↔
      IsPreconnected (P.edgeSupport D)ᶜ := by
  constructor
  · intro hc
    have hd : Dense (P.vertexPoint '' G.vertexSet ∪ P.edgeSupport D)ᶜ :=
      (P.dense_compl_drawnSet hV hE).mono (compl_subset_compl.mpr
        (union_subset subset_union_left (P.edgeSupport_subset_drawnSet D)))
    apply hc.subset_closure (compl_subset_compl.mpr subset_union_right)
    rw [hd.closure_eq]
    exact subset_univ _
  · intro hc
    have h := plane_open_preconnected_sdiff_finite
      (P.isCompact_edgeSupport hE D).isClosed.isOpen_compl hc (hV.image P.vertexPoint)
    simpa only [Set.sdiff_eq, compl_union, inter_comm] using h

/-- The sufficient forest input to N268 can omit all original vertices.
It remains an explicit argument here; `ForestComplement` proves it using
the imported disk no-retraction theorem. -/
theorem PlaneEmbedding.hasCycleBondFaceDual_of_forest_edge_complement
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    (hforest : ∀ D : Set β, D ⊆ G.edgeSet → G.IsForestIn D →
      IsPreconnected (P.edgeSupport D)ᶜ) : P.HasCycleBondFaceDual := by
  apply P.hasCycleBondFaceDual_of_forest_complement hV hE
  intro D hDE hf
  exact (P.retained_complement_preconnected_iff_edge_complement hV hE D).mpr
    (hforest D hDE hf)

/-- A boundary supported inside one simple arc is empty. This is an
unconditional geometric subcase; branching forests are not assumed to fit
inside an arc. -/
theorem PlaneEmbedding.faceBoundary_eq_empty_of_subset_arc
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    (sides : G.EdgeIndex → P.Face × P.Face)
    (hcomplete : ∀ e f, P.FaceIncident e f → f = (sides e).1 ∨ f = (sides e).2)
    (S : Set P.Face) (A : Set (ℝ × ℝ))
    (hA : A ≃ₜ I)
    (hsub : P.edgeSupport (P.faceBoundary sides S) ⊆ A) :
    P.faceBoundary sides S = ∅ := by
  let E := schoenfliesPlaneHomeomorph
  have hcompact : IsCompact A := by
    let _ : CompactSpace A := hA.symm.compactSpace
    exact isCompact_iff_compactSpace.mpr inferInstance
  have hclosed : IsClosed A := hcompact.isClosed
  have hconn : IsPreconnected Aᶜ := by
    have h := (JordanCurve.arc_not_separates JordanCurve.Brouwer.brouwerFPT
      ((E.image A).symm.trans hA)).2.image E.symm E.symm.continuous.continuousOn
    rw [← Set.image_compl_eq E.bijective, Set.image_image] at h
    simp only [E.symm_apply_apply] at h
    change IsPreconnected (id '' Aᶜ) at h
    simpa only [Set.image_id] using h
  let F := P.vertexPoint '' G.vertexSet
  have hF : F.Finite := hV.image _
  have hbase : IsPreconnected (A ∪ F)ᶜ := by
    simpa [compl_union, Set.sdiff_eq] using
      plane_open_preconnected_sdiff_finite hclosed.isOpen_compl hconn hF
  have hdense : Dense (A ∪ F)ᶜ := by
    rw [compl_union]
    exact (plane_dense_compl_of_arc A hA).inter_of_isOpen_left
      (hF.countable.dense_compl ℝ) hclosed.isOpen_compl
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hne
  apply P.faceBoundary_complement_not_isPreconnected hV hE sides hcomplete S hne
  apply hbase.subset_closure
  · exact compl_subset_compl.mpr (union_subset subset_union_right
      (hsub.trans subset_union_left))
  · rw [hdense.closure_eq]
    exact subset_univ _

/-- A proper edge subset of a drawn graph cycle fits inside one proper arc
of its Jordan trace. Missing labeled edges really remove interior points,
including for loops and parallel pairs. -/
theorem PlaneEmbedding.proper_cycle_subset_is_contained_in_arc
    (P : PlaneEmbedding G) (hE : G.edgeSet.Finite)
    {C D : Set β} (hC : G.IsGraphCycle C) (hDC : D ⊂ C) :
    ∃ A : Set (ℝ × ℝ), P.edgeSupport D ⊆ A ∧ Nonempty (A ≃ₜ I) := by
  classical
  obtain ⟨r, hc, hi, hr⟩ := P.graphCycle_hasJordanTrace hC
  let K := r ⁻¹' P.edgeSupport D
  have hKclosed : IsClosed K := (P.isCompact_edgeSupport hE D).isClosed.preimage hc
  have hKproper : K ≠ univ := by
    obtain ⟨e, heC, heD⟩ := Set.exists_of_ssubset hDC
    let e' : G.EdgeIndex := ⟨e, hC.1 heC⟩
    let t : I := ⟨1 / 2, by constructor <;> norm_num⟩
    have ht : IsInteriorTime t := by constructor <;> norm_num [t]
    have hepoint : P.edgePath e' t ∈ P.edgeSupport C := by
      simp only [PlaneEmbedding.edgeSupport, mem_iUnion]
      exact ⟨e', heC, t, rfl⟩
    have hnot : P.edgePath e' t ∉ P.edgeSupport D := by
      intro hz
      simp only [PlaneEmbedding.edgeSupport, mem_iUnion, mem_range] at hz
      obtain ⟨f, hfD, s, hsf⟩ := hz
      have hfe : f = e' := (P.interior_unique_preimage e' f t s ht hsf.symm).1.symm
      subst f
      exact heD hfD
    rw [← hr] at hepoint
    obtain ⟨z, hz⟩ := hepoint
    intro hK
    have hzK : z ∈ K := hK.symm ▸ mem_univ z
    exact hnot (hz ▸ hzK)
  obtain ⟨A₀, hKA, _, hA₀closed, ⟨e₀⟩⟩ :=
    JordanCurve.Arcs.exists_proper_arc hKclosed hKproper
  let _ : CompactSpace (Metric.sphere (0 : JordanCurve.Plane) 1) :=
    JordanCurve.Arcs.circleHomeoSphere.compactSpace
  let _ : CompactSpace A₀ := isCompact_iff_compactSpace.mp hA₀closed.isCompact
  let A := r '' A₀
  let eImg : A₀ ≃ₜ A := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.image r A₀ hi)
    (continuous_induced_rng.mpr (hc.comp continuous_subtype_val))
  refine ⟨A, ?_, ⟨eImg.symm.trans e₀⟩⟩
  intro z hz
  have hzC : z ∈ P.edgeSupport C := by
    obtain ⟨e, he⟩ := mem_iUnion.mp hz
    obtain ⟨heD, hez⟩ := mem_iUnion.mp he
    exact mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨hDC.1 heD, hez⟩⟩
  rw [← hr] at hzC
  obtain ⟨w, rfl⟩ := hzC
  exact ⟨w, hKA hz, rfl⟩

/-- Every primal graph cycle is a minimal nonempty boundary of the actual
full drawing. Proper boundary subsets are ruled out by imported arc
nonseparation, so this direction has no forest-complement hypothesis. -/
theorem PlaneEmbedding.graphCycle_isMinimalFaceBoundary
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    (sides : G.EdgeIndex → P.Face × P.Face)
    (hinc : ∀ e, P.FaceIncident e (sides e).1 ∧ P.FaceIncident e (sides e).2)
    (hcomplete : ∀ e f, P.FaceIncident e f → f = (sides e).1 ∨ f = (sides e).2)
    {C : Set β} (hC : G.IsGraphCycle C) : P.IsMinimalFaceBoundary sides C := by
  obtain ⟨S, hS⟩ :=
    P.graphCycles_are_faceBoundaries_of_complete_incidence_no_faceFinite hV hE sides
      hinc hcomplete C hC
  refine ⟨⟨⟨S, hS⟩, ((G.graphic_isCircuit_iff_isGraphCycle hE C).mpr hC).nonempty⟩, ?_⟩
  intro D hD hDC
  by_contra hCD
  obtain ⟨A, hDA, ⟨eA⟩⟩ := P.proper_cycle_subset_is_contained_in_arc hE hC ⟨hDC, hCD⟩
  obtain ⟨T, hT⟩ := hD.1
  have hzero := P.faceBoundary_eq_empty_of_subset_arc hV hE sides hcomplete T A eA
    (hT.symm ▸ hDA)
  rw [hT] at hzero
  simpa [hzero] using hD.2

/-- The cycle-to-bond direction of N268 for any complete actual incidence
assignment. `ForestComplement` supplies the converse through forest
nonseparation and the retained matroid reductions. -/
theorem PlaneEmbedding.graphCycle_isBond_faceIncidenceGraph
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    (sides : G.EdgeIndex → P.Face × P.Face)
    (hinc : ∀ e, P.FaceIncident e (sides e).1 ∧ P.FaceIncident e (sides e).2)
    (hcomplete : ∀ e f, P.FaceIncident e f → f = (sides e).1 ∨ f = (sides e).2)
    {C : Set β} (hC : G.IsGraphCycle C) :
    (P.faceIncidenceGraph sides).IsBond C :=
  (P.faceIncidenceGraph_isBond_iff_minimalFaceBoundary sides C).mpr
    (P.graphCycle_isMinimalFaceBoundary hV hE sides hinc hcomplete hC)

/-- Choose the geometric incidence assignment with its unconditional
primal-cycle to dual-bond direction. -/
theorem PlaneEmbedding.exists_incidence_with_cycle_bonds
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite) :
    ∃ sides : G.EdgeIndex → P.Face × P.Face,
      (∀ e, P.FaceIncident e (sides e).1 ∧ P.FaceIncident e (sides e).2) ∧
      (∀ e f, P.FaceIncident e f → f = (sides e).1 ∨ f = (sides e).2) ∧
      (∀ C, G.IsGraphCycle C → (P.faceIncidenceGraph sides).IsBond C) := by
  obtain ⟨sides, hinc, hcomplete⟩ := P.exists_complete_incidence hV hE
  exact ⟨sides, hinc, hcomplete,
    fun _ hC => P.graphCycle_isBond_faceIncidenceGraph hV hE sides hinc hcomplete hC⟩

end Graph
