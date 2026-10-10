import Matroid.PlanarDuality

/-! # A closed trace for a minimal graph cycle

The graph's `IsGraphCycle` predicate gives a minimal set of labeled edges and
an abstract reachability proof. We turn that proof into a continuous path
whose image contains precisely the traversed edge images. Minimality forces
all edges of the cycle to occur. This path need not yet be injective. -/

namespace Graph
variable {α β : Type*}

/-- Draw one graph link in either orientation. The path retains the actual
edge label and its full drawn image. -/
theorem PlaneEmbedding.exists_linkPath {G : Graph α β} (P : PlaneEmbedding G)
    (e : G.EdgeIndex) {u v : α} (hlink : G.IsLink (e : β) u v) :
    ∃ p : Path (P.vertexPoint u) (P.vertexPoint v),
      Set.range p = Set.range (P.edgePath e) := by
  rcases (P.ends_valid e).eq_and_eq_or_eq_and_eq hlink with
    ⟨hu, hv⟩ | ⟨hu, hv⟩
  · subst u
    subst v
    exact ⟨P.edgePath e, rfl⟩
  · subst u
    subst v
    exact ⟨(P.edgePath e).symm, Path.symm_range _⟩

/-- A link between distinct vertices can be drawn in either orientation as
an injective arc while retaining the image of its original labeled edge. -/
theorem PlaneEmbedding.exists_injective_linkPath {G : Graph α β}
    (P : PlaneEmbedding G) (e : G.EdgeIndex) {u v : α}
    (hlink : G.IsLink (e : β) u v) (hne : u ≠ v) :
    ∃ p : Path (P.vertexPoint u) (P.vertexPoint v),
      Set.range p = Set.range (P.edgePath e) ∧ Function.Injective p := by
  rcases (P.ends_valid e).eq_and_eq_or_eq_and_eq hlink with
    ⟨hu, hv⟩ | ⟨hu, hv⟩
  · subst u
    subst v
    exact ⟨P.edgePath e, rfl, P.edgePath_injective_of_nonloop e hne⟩
  · subst u
    subst v
    refine ⟨(P.edgePath e).symm, Path.symm_range _, ?_⟩
    intro t s h
    have h' : unitInterval.symm t = unitInterval.symm s :=
      P.edgePath_injective_of_nonloop e hne.symm
        (by simpa only [Path.symm_apply, Function.comp_apply] using h)
    exact unitInterval.symm_bijective.injective h'

/-- Drawn support indexed by actual edges, before forgetting their labels
through the subtype embedding. -/
def PlaneEmbedding.edgeSupportOn {G : Graph α β} (P : PlaneEmbedding G)
    (A : Set G.EdgeIndex) : Set (ℝ × ℝ) :=
  ⋃ e : G.EdgeIndex, ⋃ (_ : e ∈ A), Set.range (P.edgePath e)

theorem PlaneEmbedding.edgeSupportOn_union {G : Graph α β}
    (P : PlaneEmbedding G) (A B : Set G.EdgeIndex) :
    P.edgeSupportOn (A ∪ B) = P.edgeSupportOn A ∪ P.edgeSupportOn B := by
  ext x
  simp only [edgeSupportOn, Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨e, he | he, hx⟩
    · exact Or.inl ⟨e, he, hx⟩
    · exact Or.inr ⟨e, he, hx⟩
  · rintro (⟨e, he, hx⟩ | ⟨e, he, hx⟩)
    · exact ⟨e, Or.inl he, hx⟩
    · exact ⟨e, Or.inr he, hx⟩

theorem PlaneEmbedding.edgeSupportOn_singleton {G : Graph α β}
    (P : PlaneEmbedding G) (e : G.EdgeIndex) :
    P.edgeSupportOn {e} = Set.range (P.edgePath e) := by
  ext x
  simp [edgeSupportOn]

theorem PlaneEmbedding.edgeSupportOn_empty {G : Graph α β}
    (P : PlaneEmbedding G) : P.edgeSupportOn ∅ = ∅ := by
  simp [edgeSupportOn]

theorem PlaneEmbedding.edgeSupportOn_eq_support_image {G : Graph α β}
    (P : PlaneEmbedding G) (A : Set G.EdgeIndex) :
    P.edgeSupportOn A = P.edgeSupport (G.edgeEmbedding '' A) := by
  ext x
  simp only [edgeSupportOn, edgeSupport, Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨e, he, hx⟩
    exact ⟨e, ⟨e, he, rfl⟩, hx⟩
  · rintro ⟨e, ⟨f, hf, hfe⟩, hx⟩
    have h : e = f := G.edgeEmbedding.injective hfe.symm
    subst e
    exact ⟨f, hf, hx⟩

private theorem reachableOn_mono {G : Graph α β}
    {A B : Set G.EdgeIndex} (hAB : A ⊆ B) {u v : α}
    (h : G.ReachableOn A u v) : G.ReachableOn B u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hlink ih =>
      obtain ⟨e, heA, heLink⟩ := hlink
      exact ih.tail ⟨e, hAB heA, heLink⟩

/-- An abstract reachable path has a concrete path trace and a set of
traversed edge labels whose drawn union is exactly that trace, apart from
the stationary start point in the reflexive case. -/
theorem PlaneEmbedding.exists_reachablePath_exactSupport {G : Graph α β}
    (P : PlaneEmbedding G) {A : Set G.EdgeIndex} {u v : α}
    (hreach : G.ReachableOn A u v) :
    ∃ B : Set G.EdgeIndex, B ⊆ A ∧ G.ReachableOn B u v ∧
      ∃ p : Path (P.vertexPoint u) (P.vertexPoint v),
        Set.range p = P.edgeSupportOn B ∪ {P.vertexPoint u} := by
  induction hreach with
  | refl =>
      refine ⟨∅, Set.empty_subset _, Relation.ReflTransGen.refl,
        Path.refl (P.vertexPoint u), ?_⟩
      simp [Path.refl_range, P.edgeSupportOn_empty]
  | @tail b c _ hlink ih =>
      obtain ⟨B, hBA, hreachB, q, hq⟩ := ih
      obtain ⟨e, heA, heLink⟩ := hlink
      obtain ⟨r, hr⟩ := P.exists_linkPath e heLink
      refine ⟨B ∪ {e}, ?_, ?_, q.trans r, ?_⟩
      · exact Set.union_subset hBA (Set.singleton_subset_iff.mpr heA)
      · apply (reachableOn_mono Set.subset_union_left hreachB).tail
        exact ⟨e, Set.mem_union_right _ (Set.mem_singleton e), heLink⟩
      · rw [Path.trans_range, hq, hr, P.edgeSupportOn_union,
          P.edgeSupportOn_singleton]
        ac_rfl

/-- Any reachable witness inside a minimal graph cycle must traverse every
edge of that cycle once the closing edge is included. -/
theorem isGraphCycle_image_reachableEdges_eq {G : Graph α β} {C : Set β}
    (hC : G.IsGraphCycle C) {e : G.EdgeIndex}
    (he : e ∈ G.edgeEmbedding ⁻¹' C) {u v : α}
    (hlink : G.IsLink (e : β) u v)
    {B : Set G.EdgeIndex}
    (hB : B ⊆ (G.edgeEmbedding ⁻¹' C) \ {e})
    (hreach : G.ReachableOn B u v) :
    G.edgeEmbedding '' (B ∪ {e}) = C := by
  let D : Set β := G.edgeEmbedding '' (B ∪ {e})
  have hDsub : D ⊆ C := by
    rintro d ⟨f, hf, rfl⟩
    rcases hf with hf | hf
    · exact (hB hf).1
    · have hfe : f = e := Set.mem_singleton_iff.mp hf
      subst f
      exact he
  have hDcycle : G.HasEdgeCycle (G.edgeEmbedding ⁻¹' D) := by
    refine ⟨e, ?_, u, v, hlink, ?_⟩
    · exact ⟨e, Set.mem_union_right _ (Set.mem_singleton e), rfl⟩
    · apply reachableOn_mono _ hreach
      intro f hf
      refine ⟨?_, ?_⟩
      · exact ⟨f, Set.mem_union_left _ hf, rfl⟩
      · intro hfe
        have hfe' : f = e := Set.mem_singleton_iff.mp hfe
        exact (hB hf).2 hfe'
  have hDC : D = C := by
    by_contra hne
    exact hC.2.2 D (Set.ssubset_iff_subset_ne.mpr ⟨hDsub, hne⟩) hDcycle
  exact hDC

/-- After removing any edge of a minimal cycle, its two endpoints are joined
by a minimal set of the other cycle edges. No proper subset of those edges
still connects the endpoints. -/
theorem isGraphCycle_reachableEdges_minimal {G : Graph α β} {C : Set β}
    (hC : G.IsGraphCycle C) {e : G.EdgeIndex}
    (he : e ∈ G.edgeEmbedding ⁻¹' C) {u v : α}
    (hlink : G.IsLink (e : β) u v)
    {B : Set G.EdgeIndex}
    (hB : B ⊆ (G.edgeEmbedding ⁻¹' C) \ {e})
    (hreach : G.ReachableOn B u v) :
    ∀ D ⊂ B, ¬ G.ReachableOn D u v := by
  have himage : G.edgeEmbedding '' (B ∪ {e}) = C :=
    isGraphCycle_image_reachableEdges_eq hC he hlink hB hreach
  intro D hDB hreachD
  let E : Set β := G.edgeEmbedding '' (D ∪ {e})
  have hEsub : E ⊆ C := by
    rw [← himage]
    apply Set.image_mono
    intro f hf
    rcases hf with hf | hf
    · exact Or.inl (hDB.subset hf)
    · exact Or.inr hf
  have hEne : E ≠ C := by
    intro hEq
    have hset : D ∪ {e} = B ∪ {e} :=
      (Set.image_injective.mpr G.edgeEmbedding.injective)
        (hEq.trans himage.symm)
    have hBsubD : B ⊆ D := by
      intro f hfB
      have hf : f ∈ D ∪ {e} := by
        rw [hset]
        exact Set.mem_union_left _ hfB
      rcases hf with hf | hf
      · exact hf
      · exact False.elim ((hB hfB).2 (Set.mem_singleton_iff.mp hf))
    exact hDB.ne (Set.Subset.antisymm hDB.subset hBsubD)
  have hcycleE : G.HasEdgeCycle (G.edgeEmbedding ⁻¹' E) := by
    refine ⟨e, ?_, u, v, hlink, ?_⟩
    · exact ⟨e, Set.mem_union_right _ (Set.mem_singleton e), rfl⟩
    · apply reachableOn_mono _ hreachD
      intro f hfD
      refine ⟨?_, ?_⟩
      · exact ⟨f, Set.mem_union_left _ hfD, rfl⟩
      · intro hfe
        have hfe' : f = e := Set.mem_singleton_iff.mp hfe
        exact (hB (hDB.subset hfD)).2 hfe'
  exact hC.2.2 E (Set.ssubset_iff_subset_ne.mpr ⟨hEsub, hEne⟩) hcycleE

/-- Every minimal graph cycle in a plane embedding has a continuous closed
path whose image is exactly the drawn support of that cycle. This result
includes loops and parallel edges. Injectivity modulo endpoints is the next
separate obligation before applying the Jordan theorem. -/
theorem PlaneEmbedding.isGraphCycle_closedPath_exactSupport {G : Graph α β}
    (P : PlaneEmbedding G) {C : Set β} (hC : G.IsGraphCycle C) :
    ∃ x : ℝ × ℝ, ∃ p : Path x x, Set.range p = P.edgeSupport C := by
  obtain ⟨e, he, u, v, hlink, hreach⟩ := hC.2.1
  obtain ⟨B, hB, hreachB, q, hq⟩ :=
    P.exists_reachablePath_exactSupport hreach
  obtain ⟨r, hr⟩ := P.exists_linkPath e hlink.symm
  have himage : G.edgeEmbedding '' (B ∪ {e}) = C :=
    isGraphCycle_image_reachableEdges_eq hC he hlink hB hreachB
  have hstart : P.vertexPoint u ∈ Set.range (P.edgePath e) := by
    rw [← hr]
    exact ⟨1, Path.target r⟩
  have hsingleton : ({P.vertexPoint u} : Set (ℝ × ℝ)) ⊆
      Set.range (P.edgePath e) :=
    Set.singleton_subset_iff.mpr hstart
  have hunion :
      (P.edgeSupportOn B ∪ {P.vertexPoint u}) ∪ Set.range (P.edgePath e) =
        P.edgeSupportOn B ∪ Set.range (P.edgePath e) := by
    ext z
    constructor
    · rintro ((hz | hz) | hz)
      · exact Or.inl hz
      · exact Or.inr (hsingleton hz)
      · exact Or.inr hz
    · rintro (hz | hz)
      · exact Or.inl (Or.inl hz)
      · exact Or.inr hz
  refine ⟨P.vertexPoint u, q.trans r, ?_⟩
  rw [Path.trans_range, hq, hr, hunion,
    ← P.edgeSupportOn_singleton e, ← P.edgeSupportOn_union,
    P.edgeSupportOn_eq_support_image, himage]

/-- The remaining path-level Jordan obligation is injectivity on the
half-open parameter interval. Once supplied for an exact-support closed
path, the imported circle quotient bridge constructs `HasJordanTrace`. -/
theorem PlaneEmbedding.hasJordanTrace_of_simpleClosedPath
    {G : Graph α β} (P : PlaneEmbedding G) {C : Set β} {x : ℝ × ℝ}
    (p : Path x x) (hsupport : Set.range p = P.edgeSupport C)
    (hsimple : ∀ s t : unitInterval, (s : ℝ) < 1 → (t : ℝ) < 1 →
      p s = p t → s = t) : P.HasJordanTrace C := by
  obtain ⟨r, hc, hi, hr⟩ := JordanPath.exists_jordanTrace p hsimple
  exact ⟨r, hc, hi, hr.trans hsupport⟩

/-- A minimal cycle containing a loop is exactly that one edge. -/
theorem isGraphCycle_eq_singleton_of_loop {G : Graph α β}
    {C : Set β} (hC : G.IsGraphCycle C)
    (e : G.EdgeIndex) (he : (e : β) ∈ C)
    {u : α} (hloop : G.IsLink (e : β) u u) :
    C = {(e : β)} := by
  have hsub : ({(e : β)} : Set β) ⊆ C := Set.singleton_subset_iff.mpr he
  have hcyc : G.HasEdgeCycle (G.edgeEmbedding ⁻¹' {(e : β)}) :=
    G.hasEdgeCycle_of_loop (by simp [Graph.edgeEmbedding]) hloop
  by_contra hne
  have hss : ({(e : β)} : Set β) ⊂ C :=
    Set.ssubset_iff_subset_ne.mpr ⟨hsub, Ne.symm hne⟩
  exact hC.2.2 _ hss hcyc

/-- The graph-cycle-to-Jordan bridge is complete when the cycle contains a
loop edge: minimality reduces it to that edge, whose Jordan trace was proved
from the embedding axioms. -/
theorem PlaneEmbedding.graphCycle_hasJordanTrace_of_loop
    {G : Graph α β} (P : PlaneEmbedding G)
    {C : Set β} (hC : G.IsGraphCycle C)
    (e : G.EdgeIndex) (he : (e : β) ∈ C)
    (hloop : (P.ends e).1 = (P.ends e).2) :
    P.HasJordanTrace C := by
  have hlink : G.IsLink (e : β) (P.ends e).1 (P.ends e).1 := by
    simpa only [← hloop] using P.ends_valid e
  have hCeq : C = {(e : β)} :=
    isGraphCycle_eq_singleton_of_loop hC e he hlink
  rw [hCeq]
  exact P.loopEdge_hasJordanTrace e hloop

end Graph
