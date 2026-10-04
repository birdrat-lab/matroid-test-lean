import Matroid.Graphic
import Mathlib.Combinatorics.Graph.Delete
import Mathlib.Topology.Path
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.GDelta.Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Set.Finite.Powerset
import Mathlib.Analysis.Normed.Module.Connected

/-! # Graph cycle and bond interface for planar duality

The cycle-bond comparison below is the combinatorial part of planar graph
duality. A separate geometric theorem must produce this data from a plane
embedding of a finite labeled multigraph. -/

namespace Graph

variable {α β γ : Type*}

open unitInterval

/-- Interior of the unit interval used to parameterize an edge path. -/
def IsInteriorTime (t : I) : Prop := (0 : ℝ) < t.1 ∧ t.1 < 1

/-- A crossing-free drawing of a labeled graph in the Euclidean plane.
Each actual edge has its own continuous path, so loops and parallel edges
remain distinct. The interiors of all edge paths are jointly injective and
avoid all drawn vertices. -/
structure PlaneEmbedding (G : Graph α β) where
  ends : G.EdgeIndex → α × α
  ends_valid : ∀ e : G.EdgeIndex, G.IsLink e.1 (ends e).1 (ends e).2
  vertexPoint : α → ℝ × ℝ
  vertex_injective : Set.InjOn vertexPoint G.vertexSet
  edgePath : ∀ e : G.EdgeIndex,
    Path (vertexPoint (ends e).1) (vertexPoint (ends e).2)
  interior_injective : ∀ (e f : G.EdgeIndex) (t s : I),
    IsInteriorTime t → IsInteriorTime s →
      edgePath e t = edgePath f s → e = f ∧ t = s
  interior_avoids_vertices : ∀ (e : G.EdgeIndex) (t : I) (v : α),
    IsInteriorTime t → v ∈ G.vertexSet → edgePath e t ≠ vertexPoint v

/-- Planarity by an actual crossing-free plane drawing, independent of
graphic or cographic matroid structure. -/
def IsPlanar (G : Graph α β) : Prop := Nonempty (PlaneEmbedding G)

/-- The image occupied by drawn vertices and edge paths. -/
def PlaneEmbedding.drawnSet {G : Graph α β} (P : PlaneEmbedding G) : Set (ℝ × ℝ) :=
  P.vertexPoint '' G.vertexSet ∪
    ⋃ e : G.EdgeIndex, Set.range (P.edgePath e)

/-- A face is a connected component of the complement of a plane drawing. -/
def PlaneEmbedding.Face {G : Graph α β} (P : PlaneEmbedding G) : Type :=
  ConnectedComponents {p : ℝ × ℝ // p ∉ P.drawnSet}

/-- For a finite drawing, the union of vertices and edge paths is closed;
its complementary faces therefore occupy an open subset of the plane. -/
theorem PlaneEmbedding.isClosed_drawnSet {G : Graph α β}
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite)
    (hE : G.edgeSet.Finite) : IsClosed P.drawnSet := by
  letI : Finite G.EdgeIndex := hE.to_subtype
  apply IsClosed.union
  · exact (hV.image P.vertexPoint).isClosed
  · exact isClosed_iUnion_of_finite (fun e =>
      (isCompact_range (P.edgePath e).continuous).isClosed)

/-- The support of a finite plane drawing is compact. -/
theorem PlaneEmbedding.isCompact_drawnSet {G : Graph α β}
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite)
    (hE : G.edgeSet.Finite) : IsCompact P.drawnSet := by
  letI : Finite G.EdgeIndex := hE.to_subtype
  exact (hV.image P.vertexPoint).isCompact.union
    (isCompact_iUnion fun e => isCompact_range (P.edgePath e).continuous)

/-- A sufficiently large circle misses a finite drawing. -/
theorem PlaneEmbedding.exists_outer_circle {G : Graph α β}
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite)
    (hE : G.edgeSet.Finite) :
    ∃ r : ℝ, 0 < r ∧
      P.drawnSet ⊆ Metric.ball (0 : ℝ × ℝ) r ∧
      (Metric.sphere (0 : ℝ × ℝ) r).Nonempty := by
  obtain ⟨r, hr, hbound⟩ :=
    (P.isCompact_drawnSet hV hE).isBounded.subset_ball_lt 0 (0 : ℝ × ℝ)
  exact ⟨r, hr, hbound, NormedSpace.sphere_nonempty.mpr hr.le⟩

/-- For a finite drawing, density of the complement reduces to density of
the complement of each individual edge path. The remaining assertion that
an embedded arc has empty interior is topological, not combinatorial. -/
theorem PlaneEmbedding.dense_compl_of_edge_ranges_dense {G : Graph α β}
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite)
    (hE : G.edgeSet.Finite)
    (hArc : ∀ e : G.EdgeIndex, Dense (Set.range (P.edgePath e))ᶜ) :
    Dense P.drawnSetᶜ := by
  letI : Finite G.EdgeIndex := hE.to_subtype
  have hVnd : IsNowhereDense (P.vertexPoint '' G.vertexSet) :=
    (isClosed_isNowhereDense_iff_compl.mpr
      ⟨(hV.image P.vertexPoint).isClosed.isOpen_compl,
        (hV.image P.vertexPoint).countable.dense_compl ℝ⟩).2
  have hArcNd : ∀ e : G.EdgeIndex,
      IsNowhereDense (Set.range (P.edgePath e)) := by
    intro e
    exact (isClosed_isNowhereDense_iff_compl.mpr
      ⟨(isCompact_range (P.edgePath e).continuous).isClosed.isOpen_compl,
        hArc e⟩).2
  have hDrawNd : IsNowhereDense P.drawnSet :=
    hVnd.union (IsNowhereDense.iUnion hArcNd)
  exact (isClosed_isNowhereDense_iff_compl.mp
    ⟨P.isClosed_drawnSet hV hE, hDrawNd⟩).2

theorem PlaneEmbedding.isOpen_faceRegion {G : Graph α β}
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite)
    (hE : G.edgeSet.Finite) : IsOpen P.drawnSetᶜ :=
  (P.isClosed_drawnSet hV hE).isOpen_compl

/-- Complementary face regions of a finite drawing are locally path connected.
Thus their connected components can be studied using paths avoiding the
drawing. -/
theorem PlaneEmbedding.faceRegion_locallyPathConnected {G : Graph α β}
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite)
    (hE : G.edgeSet.Finite) :
    LocallyPathConnectedSpace {p : ℝ × ℝ // p ∉ P.drawnSet} :=
  (P.isOpen_faceRegion hV hE).locallyPathConnectedSpace

/-- Two points outside a finite drawing lie in the same face exactly when
they can be joined by a path that stays outside the drawing. -/
theorem PlaneEmbedding.sameFace_iff_joined {G : Graph α β}
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite)
    (hE : G.edgeSet.Finite)
    (p q : {x : ℝ × ℝ // x ∉ P.drawnSet}) :
    (ConnectedComponents.mk p : P.Face) = ConnectedComponents.mk q ↔ Joined p q := by
  letI : LocallyPathConnectedSpace {x : ℝ × ℝ // x ∉ P.drawnSet} :=
    P.faceRegion_locallyPathConnected hV hE
  exact (ConnectedComponents.coe_eq_coe).trans (connectedComponent_eq_iff_joined p q)

/-- A radial segment between two points on the positive horizontal ray
stays outside the disk of radius `R`. -/
private theorem plane_radialJoined (R r : ℝ) (hR : 0 ≤ R) (hr : R ≤ r) :
    JoinedIn {z : ℝ × ℝ | R ≤ dist z (0 : ℝ × ℝ)}
      (r, 0) (R, 0) := by
  have hcontin : Continuous
      (fun t : ℝ => (((1 - t) * r + t * R), (0 : ℝ))) := by
    fun_prop
  refine JoinedIn.ofLine hcontin.continuousOn ?_ ?_ ?_
  · simp
  · simp
  · intro z hz
    obtain ⟨t, ht, rfl⟩ := hz
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hcoef : 0 ≤ 1 - t := by linarith
    have hcoord : R ≤ (1 - t) * r + t * R := by
      calc
        R = (1 - t) * R + t * R := by ring
        _ ≤ (1 - t) * r + t * R := by gcongr
    have hnonneg : 0 ≤ (1 - t) * r + t * R := hR.trans hcoord
    simp [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg hnonneg, hcoord]

/-- The exterior of a closed disk in the plane is path connected. The
proof moves each point around its radius circle, then along a ray. -/
private theorem plane_outerRegion_pathConnected (R : ℝ) (hR : 0 ≤ R) :
    IsPathConnected {z : ℝ × ℝ | R ≤ dist z (0 : ℝ × ℝ)} := by
  let F : Set (ℝ × ℝ) := {z | R ≤ dist z (0 : ℝ × ℝ)}
  have hbase : (R, (0 : ℝ)) ∈ F := by
    simp [F, dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg hR, hR]
  refine ⟨(R, (0 : ℝ)), hbase, ?_⟩
  intro x hx
  let r := dist x (0 : ℝ × ℝ)
  have hr : R ≤ r := hx
  have hr0 : 0 ≤ r := hR.trans hr
  have hrank : 1 < Module.rank ℝ (ℝ × ℝ) := by norm_num
  have hxSphere : x ∈ Metric.sphere (0 : ℝ × ℝ) r := rfl
  have hrSphere : (r, (0 : ℝ)) ∈ Metric.sphere (0 : ℝ × ℝ) r := by
    simp [Real.norm_eq_abs, abs_of_nonneg hr0, hr0]
  have hSphereSub : Metric.sphere (0 : ℝ × ℝ) r ⊆ F := by
    intro z hz
    exact hr.trans_eq hz.symm
  have hCircle : JoinedIn F (r, 0) x :=
    ((isPathConnected_sphere hrank (0 : ℝ × ℝ) hr0).joinedIn
      (r, 0) hrSphere x hxSphere).mono hSphereSub
  have hRadial : JoinedIn F (r, 0) (R, 0) := plane_radialJoined R r hR hr
  exact hRadial.symm.trans hCircle

/-- Every point on a circle avoiding a finite drawing belongs to the same
complementary face. -/
theorem PlaneEmbedding.sameFace_on_avoiding_circle {G : Graph α β}
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite)
    (hE : G.edgeSet.Finite) (r : ℝ) (hr : 0 ≤ r)
    (havoid : Metric.sphere (0 : ℝ × ℝ) r ⊆ P.drawnSetᶜ)
    (x y : ℝ × ℝ) (hx : x ∈ Metric.sphere (0 : ℝ × ℝ) r)
    (hy : y ∈ Metric.sphere (0 : ℝ × ℝ) r) :
    (ConnectedComponents.mk ⟨x, havoid hx⟩ : P.Face) =
    ConnectedComponents.mk ⟨y, havoid hy⟩ := by
  have hrank : 1 < Module.rank ℝ (ℝ × ℝ) := by norm_num
  have hjoined : JoinedIn (Metric.sphere (0 : ℝ × ℝ) r) x y :=
    (isPathConnected_sphere hrank (0 : ℝ × ℝ) hr).joinedIn x hx y hy
  exact (P.sameFace_iff_joined hV hE _ _).2
    ((hjoined.mono havoid).joined_subtype)

/-- The points of one complementary face, viewed in the ambient plane. -/
def PlaneEmbedding.facePoints {G : Graph α β}
    (P : PlaneEmbedding G) (f : P.Face) : Set (ℝ × ℝ) :=
  {x | ∃ hx : x ∉ P.drawnSet, (ConnectedComponents.mk ⟨x, hx⟩ : P.Face) = f}

/-- A finite plane drawing has a complementary face containing an entire
circle around the drawing. -/
theorem PlaneEmbedding.exists_outer_face {G : Graph α β}
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite)
    (hE : G.edgeSet.Finite) :
    ∃ r : ℝ, 0 < r ∧ ∃ f : P.Face,
      P.drawnSet ⊆ Metric.ball (0 : ℝ × ℝ) r ∧
        Metric.sphere (0 : ℝ × ℝ) r ⊆ P.facePoints f := by
  obtain ⟨r, hr, hbound, ⟨base, hbase⟩⟩ := P.exists_outer_circle hV hE
  have havoid : Metric.sphere (0 : ℝ × ℝ) r ⊆ P.drawnSetᶜ := by
    intro x hx hdraw
    have heq : dist x (0 : ℝ × ℝ) = r := hx
    have hlt : dist x (0 : ℝ × ℝ) < r := hbound hdraw
    exact (lt_irrefl r) (heq ▸ hlt)
  let f : P.Face := ConnectedComponents.mk ⟨base, havoid hbase⟩
  refine ⟨r, hr, f, hbound, ?_⟩
  intro x hx
  exact ⟨havoid hx,
    P.sameFace_on_avoiding_circle hV hE r hr.le havoid x base hx hbase⟩

/-- The exterior of a sufficiently large disk belongs to one face of a
finite plane drawing. In particular this face is unbounded. -/
theorem PlaneEmbedding.exists_unbounded_face {G : Graph α β}
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite)
    (hE : G.edgeSet.Finite) :
    ∃ r : ℝ, 0 < r ∧ ∃ f : P.Face,
      P.drawnSet ⊆ Metric.ball (0 : ℝ × ℝ) r ∧
        {z : ℝ × ℝ | r ≤ dist z (0 : ℝ × ℝ)} ⊆ P.facePoints f := by
  obtain ⟨r, hr, hbound, _⟩ := P.exists_outer_circle hV hE
  let F : Set (ℝ × ℝ) := {z | r ≤ dist z (0 : ℝ × ℝ)}
  have hFsub : F ⊆ P.drawnSetᶜ := by
    intro x hx hdraw
    have hlt : dist x (0 : ℝ × ℝ) < r := hbound hdraw
    exact (not_lt_of_ge hx) hlt
  obtain ⟨base, hbase, hpaths⟩ := plane_outerRegion_pathConnected r hr.le
  let f : P.Face := ConnectedComponents.mk ⟨base, hFsub hbase⟩
  refine ⟨r, hr, f, hbound, ?_⟩
  intro x hx
  have hjoined : JoinedIn P.drawnSetᶜ base x :=
    (hpaths hx).mono hFsub
  have heq : (ConnectedComponents.mk ⟨base, hFsub hbase⟩ : P.Face) =
      ConnectedComponents.mk ⟨x, hFsub hx⟩ :=
    (P.sameFace_iff_joined hV hE _ _).2 hjoined.joined_subtype
  exact ⟨hFsub hx, heq.symm⟩

/-- A finite plane drawing has exactly one unbounded complementary face. -/
theorem PlaneEmbedding.existsUnique_unbounded_face {G : Graph α β}
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite)
    (hE : G.edgeSet.Finite) :
    ∃! f : P.Face, ¬ Bornology.IsBounded (P.facePoints f) := by
  obtain ⟨r, hr, f, _, hFface⟩ := P.exists_unbounded_face hV hE
  let F : Set (ℝ × ℝ) := {z | r ≤ dist z (0 : ℝ × ℝ)}
  have hFub : ¬ Bornology.IsBounded F := by
    intro hFb
    have hcover : (Set.univ : Set (ℝ × ℝ)) ⊆
        Metric.ball (0 : ℝ × ℝ) r ∪ F := by
      intro x _
      by_cases hx : dist x (0 : ℝ × ℝ) < r
      · exact Or.inl hx
      · right
        change r ≤ dist x (0 : ℝ × ℝ)
        exact le_of_not_gt hx
    exact NormedSpace.unbounded_univ ℝ (ℝ × ℝ)
      ((Metric.isBounded_ball.union hFb).subset hcover)
  have hfub : ¬ Bornology.IsBounded (P.facePoints f) := by
    intro hf
    exact hFub (hf.subset hFface)
  refine ⟨f, hfub, ?_⟩
  intro g hg
  have hnotSub : ¬ P.facePoints g ⊆ Metric.ball (0 : ℝ × ℝ) r := by
    intro hsub
    exact hg (Metric.isBounded_ball.subset hsub)
  obtain ⟨x, hxg, hxball⟩ := Set.not_subset.mp hnotSub
  have hxF : x ∈ F := by
    change ¬ dist x (0 : ℝ × ℝ) < r at hxball
    exact le_of_not_gt hxball
  have hxf := hFface hxF
  exact hxg.2.symm.trans hxf.2

/-- The complementary face regions cover exactly the complement of the
drawing. -/
theorem PlaneEmbedding.iUnion_facePoints {G : Graph α β}
    (P : PlaneEmbedding G) :
    (⋃ f : P.Face, P.facePoints f) = P.drawnSetᶜ := by
  ext x
  constructor
  · intro hx
    obtain ⟨f, hf⟩ := Set.mem_iUnion.mp hx
    exact hf.1
  · intro hx
    apply Set.mem_iUnion.mpr
    exact ⟨ConnectedComponents.mk ⟨x, hx⟩, hx, rfl⟩

/-- Each face region of a finite drawing is open in the ambient plane. -/
theorem PlaneEmbedding.isOpen_facePoints {G : Graph α β}
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite)
    (hE : G.edgeSet.Finite) (f : P.Face) : IsOpen (P.facePoints f) := by
  letI : LocallyPathConnectedSpace {x : ℝ × ℝ // x ∉ P.drawnSet} :=
    P.faceRegion_locallyPathConnected hV hE
  have hf : IsOpen
      {p : {x : ℝ × ℝ // x ∉ P.drawnSet} | ConnectedComponents.mk p = f} := by
    obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe f
    simpa [ConnectedComponents.coe_eq_coe, connectedComponent_eq_iff_mem] using
      (isOpen_connectedComponent (x := p))
  have himage : P.facePoints f =
      Subtype.val '' {p : {x : ℝ × ℝ // x ∉ P.drawnSet} |
        ConnectedComponents.mk p = f} := by
    ext x
    constructor
    · rintro ⟨hx, hface⟩
      exact ⟨⟨x, hx⟩, hface, rfl⟩
    · rintro ⟨p, hface, rfl⟩
      exact ⟨p.property, hface⟩
  rw [himage]
  exact (P.isOpen_faceRegion hV hE).isOpenMap_subtype_val _ hf

/-- A face is incident with an edge if its region approaches an interior
point of that drawn edge. This uses the actual geometry of the drawing. -/
def PlaneEmbedding.FaceIncident {G : Graph α β}
    (P : PlaneEmbedding G) (e : G.EdgeIndex) (f : P.Face) : Prop :=
  ∃ t : I, IsInteriorTime t ∧ P.edgePath e t ∈ closure (P.facePoints f)

/-- If the complement is dense and has finitely many faces, every point of
the plane lies in the closure of at least one face region. -/
theorem PlaneEmbedding.exists_face_closure_of_dense_compl {G : Graph α β}
    (P : PlaneEmbedding G) (hdense : Dense P.drawnSetᶜ)
    (hfaces : Finite P.Face) (x : ℝ × ℝ) :
    ∃ f : P.Face, x ∈ closure (P.facePoints f) := by
  letI : Finite P.Face := hfaces
  have hcover : closure (⋃ f : P.Face, P.facePoints f) = Set.univ := by
    rw [P.iUnion_facePoints]
    exact hdense.closure_eq
  rw [closure_iUnion_of_finite] at hcover
  have hx : x ∈ ⋃ f : P.Face, closure (P.facePoints f) := by
    rw [hcover]
    trivial
  exact Set.mem_iUnion.mp hx

/-- Density of the complement and finiteness of the face set supply at
least one incident face for each edge. This does not identify its two
local sides or prove the cycle-boundary theorem. -/
theorem PlaneEmbedding.exists_incident_face_of_dense_compl {G : Graph α β}
    (P : PlaneEmbedding G) (hdense : Dense P.drawnSetᶜ)
    (hfaces : Finite P.Face) (e : G.EdgeIndex) :
    ∃ f : P.Face, P.FaceIncident e f := by
  let midpoint : I := ⟨1 / 2, by norm_num⟩
  have hmid : IsInteriorTime midpoint := by norm_num [IsInteriorTime, midpoint]
  obtain ⟨f, hf⟩ :=
    P.exists_face_closure_of_dense_compl hdense hfaces (P.edgePath e midpoint)
  exact ⟨f, midpoint, hmid, hf⟩

/-- A concrete sufficient condition for obtaining an incident face: each
drawn edge path has dense complement and there are finitely many faces. -/
theorem PlaneEmbedding.exists_incident_face_of_edge_ranges_dense {G : Graph α β}
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite)
    (hE : G.edgeSet.Finite)
    (hArc : ∀ e : G.EdgeIndex, Dense (Set.range (P.edgePath e))ᶜ)
    (hfaces : Finite P.Face) (e : G.EdgeIndex) :
    ∃ f : P.Face, P.FaceIncident e f :=
  P.exists_incident_face_of_dense_compl
    (P.dense_compl_of_edge_ranges_dense hV hE hArc) hfaces e

/-- An edge interior cannot pass through the initial endpoint of another
edge. Endpoint membership uses the graph's incidence predicate. -/
theorem PlaneEmbedding.interior_ne_edge_source {G : Graph α β}
    (P : PlaneEmbedding G) (e f : G.EdgeIndex) (t : I)
    (ht : IsInteriorTime t) : P.edgePath e t ≠ P.edgePath f 0 := by
  rw [Path.source]
  exact P.interior_avoids_vertices e t (P.ends f).1 ht
    (G.left_mem_of_isLink (P.ends_valid f))

/-- An edge interior also avoids every terminal endpoint. -/
theorem PlaneEmbedding.interior_ne_edge_target {G : Graph α β}
    (P : PlaneEmbedding G) (e f : G.EdgeIndex) (t : I)
    (ht : IsInteriorTime t) : P.edgePath e t ≠ P.edgePath f 1 := by
  rw [Path.target]
  exact P.interior_avoids_vertices e t (P.ends f).2 ht
    (G.left_mem_of_isLink
      ((G.isLink_symm f.2).symm (P.ends f).1 (P.ends f).2 (P.ends_valid f)))

/-- An interior point has a unique edge and path parameter as a preimage,
even for a loop whose two endpoints coincide. -/
theorem PlaneEmbedding.interior_unique_preimage {G : Graph α β}
    (P : PlaneEmbedding G) (e f : G.EdgeIndex) (t s : I)
    (ht : IsInteriorTime t) (h : P.edgePath e t = P.edgePath f s) :
    e = f ∧ t = s := by
  by_cases hs0 : s = 0
  · subst s
    exact False.elim (P.interior_ne_edge_source e f t ht h)
  by_cases hs1 : s = 1
  · subst s
    exact False.elim (P.interior_ne_edge_target e f t ht h)
  have hs : IsInteriorTime s := by
    dsimp [IsInteriorTime]
    have h0 : (s : ℝ) ≠ 0 := by
      intro h
      exact hs0 (Subtype.ext h)
    have h1 : (s : ℝ) ≠ 1 := by
      intro h
      exact hs1 (Subtype.ext h)
    have hsbound : 0 ≤ (s : ℝ) ∧ (s : ℝ) ≤ 1 := s.property
    exact ⟨lt_of_le_of_ne hsbound.1 h0.symm,
      lt_of_le_of_ne hsbound.2 h1⟩
  exact P.interior_injective e f t s ht hs h

/-- All drawn vertices and all edge paths other than the chosen edge. -/
def PlaneEmbedding.otherDrawnSet {G : Graph α β}
    (P : PlaneEmbedding G) (e : G.EdgeIndex) : Set (ℝ × ℝ) :=
  P.vertexPoint '' G.vertexSet ∪
    ⋃ f : {f : G.EdgeIndex // f ≠ e}, Set.range (P.edgePath f.1)

/-- The rest of a finite drawing is closed. -/
theorem PlaneEmbedding.isClosed_otherDrawnSet {G : Graph α β}
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite)
    (hE : G.edgeSet.Finite) (e : G.EdgeIndex) :
    IsClosed (P.otherDrawnSet e) := by
  letI : Finite G.EdgeIndex := hE.to_subtype
  letI : Finite {f : G.EdgeIndex // f ≠ e} := inferInstance
  exact (hV.image P.vertexPoint).isClosed.union
    (isClosed_iUnion_of_finite (fun f =>
      (isCompact_range (P.edgePath f.1).continuous).isClosed))

/-- An interior point of an edge belongs to no other edge path or drawn
vertex, including when the selected edge is a loop. -/
theorem PlaneEmbedding.interior_not_mem_otherDrawnSet {G : Graph α β}
    (P : PlaneEmbedding G) (e : G.EdgeIndex) (t : I)
    (ht : IsInteriorTime t) : P.edgePath e t ∉ P.otherDrawnSet e := by
  intro h
  rcases h with hvertex | hother
  · obtain ⟨v, hv, hve⟩ := hvertex
    exact P.interior_avoids_vertices e t v ht hv hve.symm
  · obtain ⟨f, hf⟩ := Set.mem_iUnion.mp hother
    obtain ⟨s, hfe⟩ := Set.mem_range.mp hf
    exact f.2 ((P.interior_unique_preimage e f.1 t s ht hfe.symm).1).symm

/-- Around every edge interior point of a finite drawing, a neighborhood
meets the drawing only along that edge. This is the isolation needed before
any local arc-side separation argument. -/
theorem PlaneEmbedding.exists_isolated_edge_neighborhood {G : Graph α β}
    (P : PlaneEmbedding G) (hV : G.vertexSet.Finite)
    (hE : G.edgeSet.Finite) (e : G.EdgeIndex) (t : I)
    (ht : IsInteriorTime t) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ P.edgePath e t ∈ U ∧
      P.drawnSet ∩ U ⊆ Set.range (P.edgePath e) := by
  refine ⟨(P.otherDrawnSet e)ᶜ,
    (P.isClosed_otherDrawnSet hV hE e).isOpen_compl,
    P.interior_not_mem_otherDrawnSet e t ht, ?_⟩
  intro x hx
  obtain ⟨hdrawn, hother⟩ := hx
  rcases hdrawn with hvertex | hpath
  · exact False.elim (hother (Or.inl hvertex))
  · obtain ⟨f, hf⟩ := Set.mem_iUnion.mp hpath
    by_cases hfe : f = e
    · subst f
      exact hf
    · exact False.elim (hother (Or.inr
        (Set.mem_iUnion.mpr ⟨⟨f, hfe⟩, hf⟩)))

/-- The compact edge path has no remote parameter values arbitrarily close
to a chosen interior point. -/
theorem PlaneEmbedding.exists_edge_parameter_neighborhood {G : Graph α β}
    (P : PlaneEmbedding G) (e : G.EdgeIndex) (t : I)
    (ht : IsInteriorTime t) (V : Set I) (hV : IsOpen V) (htV : t ∈ V) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ P.edgePath e t ∈ U ∧
      ∀ s : I, P.edgePath e s ∈ U → s ∈ V := by
  have hclosed : IsClosed (P.edgePath e '' Vᶜ) :=
    (hV.isClosed_compl.isCompact.image (P.edgePath e).continuous).isClosed
  have hnot : P.edgePath e t ∉ P.edgePath e '' Vᶜ := by
    rintro ⟨s, hs, heq⟩
    have hts := (P.interior_unique_preimage e e t s ht heq.symm).2
    exact hs (hts ▸ htV)
  refine ⟨(P.edgePath e '' Vᶜ)ᶜ, hclosed.isOpen_compl, hnot, ?_⟩
  intro s hs
  by_contra hnotV
  exact hs ⟨s, hnotV, rfl⟩

/-- Every interior point has an open neighborhood whose drawn support is
contained in an arbitrarily chosen open subarc around its parameter. -/
theorem PlaneEmbedding.exists_isolated_subarc_neighborhood {G : Graph α β}
    (P : PlaneEmbedding G) (hvertices : G.vertexSet.Finite)
    (hedges : G.edgeSet.Finite) (e : G.EdgeIndex) (t : I)
    (ht : IsInteriorTime t) (V : Set I) (hV : IsOpen V) (htV : t ∈ V) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ P.edgePath e t ∈ U ∧
      P.drawnSet ∩ U ⊆ P.edgePath e '' V := by
  obtain ⟨U₁, hU₁, hp₁, hdraw⟩ :=
    P.exists_isolated_edge_neighborhood hvertices hedges e t ht
  obtain ⟨U₂, hU₂, hp₂, hparam⟩ :=
    P.exists_edge_parameter_neighborhood e t ht V hV htV
  refine ⟨U₁ ∩ U₂, hU₁.inter hU₂, ⟨hp₁, hp₂⟩, ?_⟩
  intro x hx
  obtain ⟨hdrawn, hx₁, hx₂⟩ := hx
  obtain ⟨s, hs⟩ := hdraw ⟨hdrawn, hx₁⟩
  exact ⟨s, hparam s (hs ▸ hx₂), hs⟩

/-- Restrict a drawing to the edges surviving deletion, while retaining the
same vertex positions and the original edge labels. -/
def PlaneEmbedding.deleteEdges {G : Graph α β} (P : PlaneEmbedding G)
    (F : Set β) : PlaneEmbedding (G.deleteEdges F) := by
  let incl : (G.deleteEdges F).EdgeIndex → G.EdgeIndex :=
    fun e => ⟨e.1, e.2.1⟩
  refine {
    ends := fun e => P.ends (incl e)
    ends_valid := ?_
    vertexPoint := P.vertexPoint
    vertex_injective := ?_
    edgePath := fun e => P.edgePath (incl e)
    interior_injective := ?_
    interior_avoids_vertices := ?_ }
  · intro e
    exact ⟨P.ends_valid (incl e), e.2.2⟩
  · simpa using P.vertex_injective
  · intro e f t s ht hs heq
    obtain ⟨hef, hts⟩ := P.interior_injective (incl e) (incl f) t s ht hs heq
    exact ⟨Subtype.ext (congrArg (fun x : G.EdgeIndex => (x : β)) hef), hts⟩
  · intro e t v ht hv
    exact P.interior_avoids_vertices (incl e) t v ht (by simpa using hv)

/-- Removing edges only removes points from the support of a drawing. -/
theorem PlaneEmbedding.deleteEdges_drawnSet_subset {G : Graph α β}
    (P : PlaneEmbedding G) (F : Set β) :
    (P.deleteEdges F).drawnSet ⊆ P.drawnSet := by
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl (by simpa [Graph.deleteEdges, Graph.restrict,
      PlaneEmbedding.deleteEdges] using hx)
  · rcases Set.mem_iUnion.mp hx with ⟨e, he⟩
    refine Or.inr (Set.mem_iUnion.mpr ⟨(⟨e.1, e.2.1⟩ : G.EdgeIndex), ?_⟩)
    rcases he with ⟨t, rfl⟩
    exact ⟨t, rfl⟩

/-- Inclusion of the old drawing complement into the complement after edge deletion. -/
def PlaneEmbedding.complementInclusion_deleteEdges {G : Graph α β}
    (P : PlaneEmbedding G) (F : Set β) :
    {x : ℝ × ℝ // x ∉ P.drawnSet} →
      {x : ℝ × ℝ // x ∉ (P.deleteEdges F).drawnSet} :=
  fun x => ⟨x.1, fun hx => x.2 (P.deleteEdges_drawnSet_subset F hx)⟩

theorem PlaneEmbedding.continuous_complementInclusion_deleteEdges {G : Graph α β}
    (P : PlaneEmbedding G) (F : Set β) :
    Continuous (P.complementInclusion_deleteEdges F) := by
  exact continuous_subtype_val.subtype_mk _

/-- Each old face lies in a well-defined face after deleting edges. -/
def PlaneEmbedding.faceMap_deleteEdges {G : Graph α β}
    (P : PlaneEmbedding G) (F : Set β) :
    P.Face → (P.deleteEdges F).Face :=
  Quotient.lift
    (fun x => ConnectedComponents.mk (P.complementInclusion_deleteEdges F x))
    (by
      intro x y hxy
      have hy : y ∈ connectedComponent x := by
        rw [hxy]
        exact mem_connectedComponent
      exact (ConnectedComponents.coe_eq_coe'.2
        ((P.continuous_complementInclusion_deleteEdges F).mapsTo_connectedComponent x
          hy)).symm)

@[simp]
theorem PlaneEmbedding.faceMap_deleteEdges_mk {G : Graph α β}
    (P : PlaneEmbedding G) (F : Set β) (x : {x : ℝ × ℝ // x ∉ P.drawnSet}) :
    P.faceMap_deleteEdges F (ConnectedComponents.mk x) =
      ConnectedComponents.mk (P.complementInclusion_deleteEdges F x) := rfl

/-- Old face regions are contained in their image face after edge deletion. -/
theorem PlaneEmbedding.facePoints_subset_deleteEdges {G : Graph α β}
    (P : PlaneEmbedding G) (F : Set β) (f : P.Face) :
    P.facePoints f ⊆
      (P.deleteEdges F).facePoints (P.faceMap_deleteEdges F f) := by
  intro x hx
  obtain ⟨hnot, hface⟩ := hx
  let hnew : x ∉ (P.deleteEdges F).drawnSet :=
    fun h => hnot (P.deleteEdges_drawnSet_subset F h)
  refine ⟨hnew, ?_⟩
  exact (P.faceMap_deleteEdges_mk F ⟨x, hnot⟩).symm.trans
    (congrArg (P.faceMap_deleteEdges F) hface)

/-- An unbounded face remains unbounded when edges are deleted. -/
theorem PlaneEmbedding.faceMap_deleteEdges_unbounded {G : Graph α β}
    (P : PlaneEmbedding G) (F : Set β) (f : P.Face)
    (hf : ¬ Bornology.IsBounded (P.facePoints f)) :
    ¬ Bornology.IsBounded
      ((P.deleteEdges F).facePoints (P.faceMap_deleteEdges F f)) := by
  intro hbound
  exact hf (hbound.subset (P.facePoints_subset_deleteEdges F f))

/-- If the original complement is dense, every face after deleting edges
contains a point from an old face. -/
theorem PlaneEmbedding.faceMap_deleteEdges_surjective {G : Graph α β}
    (P : PlaneEmbedding G) (F : Set β)
    (hV : G.vertexSet.Finite) (hE : G.edgeSet.Finite)
    (hDense : Dense P.drawnSetᶜ) :
    Function.Surjective (P.faceMap_deleteEdges F) := by
  intro f
  obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe f
  have hV' : (G.deleteEdges F).vertexSet.Finite := by
    simpa [Graph.deleteEdges, Graph.restrict] using hV
  have hE' : (G.deleteEdges F).edgeSet.Finite :=
    hE.subset (G.deleteEdges_le : G.deleteEdges F ≤ G).edgeSet_mono
  have hnon : ((P.deleteEdges F).facePoints (ConnectedComponents.mk p)).Nonempty :=
    ⟨p.1, p.2, rfl⟩
  obtain ⟨x, hOld, _, hFace⟩ :=
    hDense.exists_mem_open ((P.deleteEdges F).isOpen_facePoints hV' hE' _) hnon
  refine ⟨ConnectedComponents.mk ⟨x, hOld⟩, ?_⟩
  exact (P.faceMap_deleteEdges_mk F ⟨x, hOld⟩).trans hFace

/-- Incidence with a surviving edge persists under edge deletion, even when
the incident face merges with another face. -/
theorem PlaneEmbedding.faceIncident_deleteEdges {G : Graph α β}
    (P : PlaneEmbedding G) (F : Set β) (e : (G.deleteEdges F).EdgeIndex)
    (f : P.Face)
    (h : P.FaceIncident (⟨e.1, e.2.1⟩ : G.EdgeIndex) f) :
    (P.deleteEdges F).FaceIncident e (P.faceMap_deleteEdges F f) := by
  obtain ⟨t, ht, hclosure⟩ := h
  refine ⟨t, ht, ?_⟩
  exact (closure_mono (P.facePoints_subset_deleteEdges F f)) hclosure

/-- Edge deletion preserves the geometric planarity predicate. -/
theorem IsPlanar.deleteEdges {G : Graph α β} (h : G.IsPlanar) (F : Set β) :
    (G.deleteEdges F).IsPlanar := by
  obtain ⟨P⟩ := h
  exact ⟨P.deleteEdges F⟩

/-- A graph on the complementary faces from a proposed assignment of the
two faces incident with each drawn edge. Establishing that such an assignment
comes from the geometry, and that it has the cycle-bond property, is still
required for planar duality. -/
def PlaneEmbedding.faceIncidenceGraph {G : Graph α β} (P : PlaneEmbedding G)
    (sides : G.EdgeIndex → P.Face × P.Face) : Graph P.Face β where
  vertexSet := Set.univ
  edgeSet := G.edgeSet
  IsLink e x y := ∃ he : e ∈ G.edgeSet,
    (x = (sides ⟨e, he⟩).1 ∧ y = (sides ⟨e, he⟩).2) ∨
    (x = (sides ⟨e, he⟩).2 ∧ y = (sides ⟨e, he⟩).1)
  isLink_symm := by aesop (add simp symm_def)
  eq_or_eq_of_isLink_of_isLink := by aesop
  edge_mem_iff_exists_isLink := by
    intro e
    constructor
    · intro he
      exact ⟨(sides ⟨e, he⟩).1, (sides ⟨e, he⟩).2,
        he, Or.inl ⟨rfl, rfl⟩⟩
    · rintro ⟨_, _, he, _⟩
      exact he
  left_mem_of_isLink := by simp

@[simp] theorem PlaneEmbedding.faceIncidenceGraph_edgeSet {G : Graph α β}
    (P : PlaneEmbedding G) (sides : G.EdgeIndex → P.Face × P.Face) :
    (P.faceIncidenceGraph sides).edgeSet = G.edgeSet := rfl

/-- Edges crossing a partition of the complementary faces. -/
def PlaneEmbedding.faceBoundary {G : Graph α β} (P : PlaneEmbedding G)
    (sides : G.EdgeIndex → P.Face × P.Face) (S : Set P.Face) : Set β :=
  {e | ∃ he : e ∈ G.edgeSet,
    ((sides ⟨e, he⟩).1 ∈ S) ≠ ((sides ⟨e, he⟩).2 ∈ S)}

theorem PlaneEmbedding.faceBoundary_subset_edgeSet {G : Graph α β}
    (P : PlaneEmbedding G) (sides : G.EdgeIndex → P.Face × P.Face)
    (S : Set P.Face) : P.faceBoundary sides S ⊆ G.edgeSet := by
  rintro e ⟨he, _⟩
  exact he

/-- The graph cut of a proposed face dual is exactly the set of primal edge
labels whose two assigned faces lie on opposite sides of the partition. -/
theorem PlaneEmbedding.faceIncidenceGraph_edgeCut_eq_faceBoundary
    {G : Graph α β} (P : PlaneEmbedding G)
    (sides : G.EdgeIndex → P.Face × P.Face) (S : Set P.Face) :
    (P.faceIncidenceGraph sides).edgeCut S = P.faceBoundary sides S := by
  classical
  ext e
  by_cases he : e ∈ G.edgeSet
  · have hlink : (P.faceIncidenceGraph sides).IsLink e
        (sides ⟨e, he⟩).1 (sides ⟨e, he⟩).2 :=
      ⟨he, Or.inl ⟨rfl, rfl⟩⟩
    rw [hlink.mem_edgeCut_iff]
    simp only [faceBoundary, Set.mem_ofPred_eq]
    constructor
    · intro h
      refine ⟨he, ?_⟩
      tauto
    · rintro ⟨he', h⟩
      have : (sides ⟨e, he'⟩) = sides ⟨e, he⟩ := rfl
      rw [this] at h
      tauto
  · constructor
    · intro h
      exact False.elim (he ((P.faceIncidenceGraph sides).edgeCut_subset_edgeSet h))
    · rintro ⟨he', _⟩
      exact (he he').elim

/-- A nonempty edge boundary minimal under inclusion, described solely by
partitions of the complementary faces. -/
def PlaneEmbedding.IsMinimalFaceBoundary {G : Graph α β}
    (P : PlaneEmbedding G) (sides : G.EdgeIndex → P.Face × P.Face)
    (C : Set β) : Prop :=
  Minimal (fun D : Set β =>
    (∃ S : Set P.Face, P.faceBoundary sides S = D) ∧ D.Nonempty) C

/-- Bonds of the face-incidence graph are precisely minimal nonempty face
boundaries. The remaining plane-separation theorem can be phrased without
mentioning graph cuts or matroids. -/
theorem PlaneEmbedding.faceIncidenceGraph_isBond_iff_minimalFaceBoundary
    {G : Graph α β} (P : PlaneEmbedding G)
    (sides : G.EdgeIndex → P.Face × P.Face) (C : Set β) :
    (P.faceIncidenceGraph sides).IsBond C ↔
      P.IsMinimalFaceBoundary sides C := by
  simp only [Graph.IsBond, Graph.IsEdgeCut, IsMinimalFaceBoundary,
    P.faceIncidenceGraph_edgeCut_eq_faceBoundary]

/-- A minimal cyclic set of actual labeled edges. This includes loops and
parallel-edge pairs. -/
def IsGraphCycle (G : Graph α β) (C : Set β) : Prop :=
  C ⊆ G.edgeSet ∧
    G.HasEdgeCycle (G.edgeEmbedding ⁻¹' C) ∧
      ∀ D ⊂ C, ¬ G.HasEdgeCycle (G.edgeEmbedding ⁻¹' D)

/-- The graph-cycle predicate agrees with the circuits of the constructed
graphic matroid. -/
theorem graphic_isCircuit_iff_isGraphCycle (G : Graph α β)
    (hE : G.edgeSet.Finite) (C : Set β) :
    (Matroid.graphic G hE).IsCircuit C ↔ G.IsGraphCycle C := by
  rw [Matroid.isCircuit_iff_forall_ssubset]
  constructor
  · rintro ⟨hdep, hproper⟩
    have hCE : C ⊆ G.edgeSet := by simpa using hdep.subset_ground
    have hcycle : G.HasEdgeCycle (G.edgeEmbedding ⁻¹' C) := by
      have hn : ¬ (Matroid.graphic G hE).Indep C := hdep.not_indep
      simpa [Matroid.graphic_indep_iff, hCE, Graph.IsForestIn,
        Graph.IsForestOn] using hn
    refine ⟨hCE, hcycle, ?_⟩
    intro D hDC
    have hDE : D ⊆ G.edgeSet := hDC.subset.trans hCE
    have hDI := hproper hDC
    simpa [Matroid.graphic_indep_iff, hDE, Graph.IsForestIn,
      Graph.IsForestOn] using hDI
  · rintro ⟨hCE, hcycle, hproper⟩
    have hdep : (Matroid.graphic G hE).Dep C := by
      apply (Matroid.dep_iff).2
      constructor
      · intro hI
        exact ((Matroid.graphic_indep_iff G hE C).1 hI).2 hcycle
      · simpa using hCE
    refine ⟨hdep, ?_⟩
    intro D hDC
    apply (Matroid.graphic_indep_iff G hE D).2
    exact ⟨hDC.subset.trans hCE, hproper D hDC⟩

/-- Two geometric statements suffice for the cycle/minimal-boundary
equivalence: every primal minimal cycle occurs as a boundary of faces, and
every nonempty face boundary contains a primal minimal cycle. The latter
excludes spurious dual bonds. -/
theorem PlaneEmbedding.isGraphCycle_iff_minimalFaceBoundary_of_geometric_conditions
    {G : Graph α β} (P : PlaneEmbedding G) (hE : G.edgeSet.Finite)
    (sides : G.EdgeIndex → P.Face × P.Face)
    (hcycles : ∀ C, G.IsGraphCycle C →
      ∃ S : Set P.Face, P.faceBoundary sides S = C)
    (hboundaries : ∀ S : Set P.Face,
      (P.faceBoundary sides S).Nonempty →
        ∃ C, G.IsGraphCycle C ∧ C ⊆ P.faceBoundary sides S) :
    ∀ C, G.IsGraphCycle C ↔ P.IsMinimalFaceBoundary sides C := by
  intro C
  constructor
  · intro hC
    obtain ⟨S, hSC⟩ := hcycles C hC
    have hCne : C.Nonempty :=
      ((G.graphic_isCircuit_iff_isGraphCycle hE C).2 hC).nonempty
    refine ⟨⟨⟨S, hSC⟩, hCne⟩, ?_⟩
    intro D hD hDC
    by_cases hDCeq : D = C
    · simp [hDCeq]
    have hDCstrict : D ⊂ C :=
      Set.ssubset_iff_subset_ne.mpr ⟨hDC, hDCeq⟩
    obtain ⟨T, hTD⟩ := hD.1
    obtain ⟨K, hK, hKD⟩ := hboundaries T (by simpa [hTD] using hD.2)
    have hKC : K ⊂ C :=
      Set.ssubset_of_subset_of_ssubset (hKD.trans_eq hTD) hDCstrict
    exact False.elim ((hC.2.2 K hKC) hK.2.1)
  · intro hmin
    obtain ⟨S, hSC⟩ := hmin.prop.1
    obtain ⟨K, hK, hKS⟩ := hboundaries S (by simpa [hSC] using hmin.prop.2)
    have hKC : K ⊆ C := hKS.trans_eq hSC
    obtain ⟨T, hTK⟩ := hcycles K hK
    have hKne : K.Nonempty :=
      ((G.graphic_isCircuit_iff_isGraphCycle hE K).2 hK).nonempty
    have hKCeq : K = C := hmin.eq_of_subset ⟨⟨T, hTK⟩, hKne⟩ hKC
    simpa [hKCeq] using hK

/-- On a finite edge set, the two geometric cycle/boundary conditions are
also necessary for the exact cycle/minimal-boundary equivalence. -/
theorem PlaneEmbedding.cycles_iff_minimalFaceBoundary_iff_geometric_conditions
    {G : Graph α β} (P : PlaneEmbedding G) (hE : G.edgeSet.Finite)
    (sides : G.EdgeIndex → P.Face × P.Face) :
    (∀ C, G.IsGraphCycle C ↔ P.IsMinimalFaceBoundary sides C) ↔
      (∀ C, G.IsGraphCycle C →
        ∃ S : Set P.Face, P.faceBoundary sides S = C) ∧
      (∀ S : Set P.Face, (P.faceBoundary sides S).Nonempty →
        ∃ C, G.IsGraphCycle C ∧ C ⊆ P.faceBoundary sides S) := by
  constructor
  · intro hsep
    constructor
    · intro C hC
      exact ((hsep C).mp hC).prop.1
    · intro S hS
      let D := P.faceBoundary sides S
      let boundary : Set (Set β) :=
        {B | (∃ T : Set P.Face, P.faceBoundary sides T = B) ∧ B.Nonempty}
      have hboundary_finite : boundary.Finite := by
        apply hE.finite_subsets.subset
        rintro B ⟨⟨T, rfl⟩, _⟩
        exact P.faceBoundary_subset_edgeSet sides T
      let candidates : Set (Set β) := {B | B ∈ boundary ∧ B ⊆ D}
      have hcandidates_finite : candidates.Finite :=
        hboundary_finite.subset (fun _ h => h.1)
      have hcandidates_nonempty : candidates.Nonempty := by
        refine ⟨D, ?_⟩
        exact ⟨⟨⟨S, rfl⟩, hS⟩, subset_rfl⟩
      obtain ⟨B, hmin⟩ :=
        hcandidates_finite.exists_minimal hcandidates_nonempty
      have hBmin : P.IsMinimalFaceBoundary sides B := by
        change Minimal (fun B : Set β =>
          (∃ T : Set P.Face, P.faceBoundary sides T = B) ∧ B.Nonempty) B
        refine ⟨hmin.prop.1, ?_⟩
        intro B' hB' hB'B
        exact hmin.le_of_le ⟨hB', hB'B.trans hmin.prop.2⟩ hB'B
      exact ⟨B, (hsep B).mpr hBmin, hmin.prop.2⟩
  · rintro ⟨hcycles, hboundaries⟩
    exact P.isGraphCycle_iff_minimalFaceBoundary_of_geometric_conditions
      hE sides hcycles hboundaries

/-- Edge-corresponding graph duality data: cycles of either graph are bonds
of the other. For plane graphs, producing these witnesses is the substantive
topological prerequisite to the matroid correspondence. -/
structure CycleBondDuality (G : Graph α β) (H : Graph γ β) : Prop where
  edgeSet_eq : G.edgeSet = H.edgeSet
  cycles_iff_bonds : ∀ C, G.IsGraphCycle C ↔ H.IsBond C
  dual_cycles_iff_bonds : ∀ C, H.IsGraphCycle C ↔ G.IsBond C

/-- For finite edge sets, one cycle-to-bond correspondence forces the reverse
one by duality of matroids. Thus the geometric part of N268 needs only one
cycle-bond direction once the edge labels are identified. -/
theorem CycleBondDuality.of_cycles_iff_bonds
    (G : Graph α β) (H : Graph γ β)
    (hG : G.edgeSet.Finite) (hH : H.edgeSet.Finite)
    (hE : G.edgeSet = H.edgeSet)
    (hCB : ∀ C, G.IsGraphCycle C ↔ H.IsBond C) :
    CycleBondDuality G H := by
  have hgraphic : Matroid.graphic G hG = Matroid.cographic H hH := by
    apply Matroid.ext_isCircuit
    · simpa using hE
    · intro C _
      rw [graphic_isCircuit_iff_isGraphCycle,
        Matroid.cographic_isCircuit_iff_isBond]
      exact hCB C
  have hcographic : Matroid.cographic G hG = Matroid.graphic H hH := by
    have hd := congrArg (fun M : Matroid β => M✶) hgraphic
    simpa [Matroid.cographic] using hd
  refine ⟨hE, hCB, ?_⟩
  intro C
  calc
    H.IsGraphCycle C ↔ (Matroid.graphic H hH).IsCircuit C :=
      (graphic_isCircuit_iff_isGraphCycle H hH C).symm
    _ ↔ (Matroid.cographic G hG).IsCircuit C := by rw [hcographic]
    _ ↔ G.IsBond C := Matroid.cographic_isCircuit_iff_isBond G hG C

/-- The exact missing N268 obligation for a fixed geometric drawing: assign
the two incident complementary faces to each edge so that the resulting
face graph has the two cycle-bond correspondences. This predicate is kept
separate from `IsPlanar`, which only asserts a crossing-free drawing. -/
def PlaneEmbedding.HasCycleBondFaceDual {G : Graph α β}
    (P : PlaneEmbedding G) : Prop :=
  ∃ sides : G.EdgeIndex → P.Face × P.Face,
    (∀ e, P.FaceIncident e (sides e).1 ∧
      P.FaceIncident e (sides e).2) ∧
      CycleBondDuality G (P.faceIncidenceGraph sides)

/-- A one-sided geometric cycle-bond theorem suffices to build the full
face-duality certificate for a finite drawing. -/
theorem PlaneEmbedding.hasCycleBondFaceDual_of_cycles_iff_bonds
    {G : Graph α β} (P : PlaneEmbedding G) (hE : G.edgeSet.Finite)
    (sides : G.EdgeIndex → P.Face × P.Face)
    (hincident : ∀ e, P.FaceIncident e (sides e).1 ∧
      P.FaceIncident e (sides e).2)
    (hCB : ∀ C, G.IsGraphCycle C ↔
      (P.faceIncidenceGraph sides).IsBond C) :
    P.HasCycleBondFaceDual := by
  refine ⟨sides, hincident, ?_⟩
  apply CycleBondDuality.of_cycles_iff_bonds G (P.faceIncidenceGraph sides)
    hE (by simpa using hE)
    (P.faceIncidenceGraph_edgeSet sides).symm hCB

/-- For a finite drawing, the face-duality certificate is equivalent to
assigning actual incident faces so that the minimal cyclic edge sets are
exactly the minimal nonempty boundaries of face partitions. This isolates
the remaining plane-separation obligation from graph-cut bookkeeping. -/
theorem PlaneEmbedding.hasCycleBondFaceDual_iff_minimalFaceBoundary
    {G : Graph α β} (P : PlaneEmbedding G) (hE : G.edgeSet.Finite) :
    P.HasCycleBondFaceDual ↔
      ∃ sides : G.EdgeIndex → P.Face × P.Face,
        (∀ e, P.FaceIncident e (sides e).1 ∧
          P.FaceIncident e (sides e).2) ∧
        ∀ C, G.IsGraphCycle C ↔ P.IsMinimalFaceBoundary sides C := by
  constructor
  · rintro ⟨sides, hincident, hdual⟩
    refine ⟨sides, hincident, ?_⟩
    intro C
    exact (hdual.cycles_iff_bonds C).trans
      (P.faceIncidenceGraph_isBond_iff_minimalFaceBoundary sides C)
  · rintro ⟨sides, hincident, hsep⟩
    apply P.hasCycleBondFaceDual_of_cycles_iff_bonds hE sides hincident
    intro C
    exact (hsep C).trans
      (P.faceIncidenceGraph_isBond_iff_minimalFaceBoundary sides C).symm

/-- The exact finite geometric obligations for a face dual: assign incident
faces, realize each primal cycle as a face boundary, and show that every
nonempty face boundary contains a primal cycle. -/
theorem PlaneEmbedding.hasCycleBondFaceDual_iff_geometric_conditions
    {G : Graph α β} (P : PlaneEmbedding G) (hE : G.edgeSet.Finite) :
    P.HasCycleBondFaceDual ↔
      ∃ sides : G.EdgeIndex → P.Face × P.Face,
        (∀ e, P.FaceIncident e (sides e).1 ∧
          P.FaceIncident e (sides e).2) ∧
        (∀ C, G.IsGraphCycle C →
          ∃ S : Set P.Face, P.faceBoundary sides S = C) ∧
        (∀ S : Set P.Face, (P.faceBoundary sides S).Nonempty →
          ∃ C, G.IsGraphCycle C ∧ C ⊆ P.faceBoundary sides S) := by
  rw [P.hasCycleBondFaceDual_iff_minimalFaceBoundary hE]
  constructor
  · rintro ⟨sides, hincident, hsep⟩
    exact ⟨sides, hincident,
      (P.cycles_iff_minimalFaceBoundary_iff_geometric_conditions hE sides).mp hsep⟩
  · rintro ⟨sides, hincident, hgeometric⟩
    exact ⟨sides, hincident,
      (P.cycles_iff_minimalFaceBoundary_iff_geometric_conditions hE sides).mpr
        hgeometric⟩

/-- A cycle-bond dual pair yields both graphic-cographic identifications on
the original edge labels. -/
theorem CycleBondDuality.matroid_correspondence {G : Graph α β} {H : Graph γ β}
    (h : CycleBondDuality G H) (hG : G.edgeSet.Finite)
    (hH : H.edgeSet.Finite) :
    Matroid.graphic G hG = Matroid.cographic H hH ∧
      Matroid.cographic G hG = Matroid.graphic H hH := by
  constructor
  · apply Matroid.ext_isCircuit
    · simpa using h.edgeSet_eq
    · intro C _
      rw [graphic_isCircuit_iff_isGraphCycle,
        Matroid.cographic_isCircuit_iff_isBond]
      exact h.cycles_iff_bonds C
  · symm
    apply Matroid.ext_isCircuit
    · simpa using h.edgeSet_eq.symm
    · intro C _
      rw [graphic_isCircuit_iff_isGraphCycle,
        Matroid.cographic_isCircuit_iff_isBond]
      exact h.dual_cycles_iff_bonds C

/-- The manuscript-facing conclusion follows from the missing geometric
face-duality theorem once it is supplied for a given plane drawing. -/
theorem PlaneEmbedding.matroid_correspondence_of_faceDual {G : Graph α β}
    (P : PlaneEmbedding G) (hdual : P.HasCycleBondFaceDual)
    (hE : G.edgeSet.Finite) :
    ∃ (H : Graph P.Face β) (hH : H.edgeSet.Finite),
      Matroid.graphic G hE = Matroid.cographic H hH ∧
      Matroid.cographic G hE = Matroid.graphic H hH := by
  obtain ⟨sides, _, h⟩ := hdual
  let H := P.faceIncidenceGraph sides
  have hH : H.edgeSet.Finite := by simpa [H] using hE
  exact ⟨H, hH, h.matroid_correspondence hE hH⟩

end Graph
