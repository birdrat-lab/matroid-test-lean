import Matroid.Graphic
import Matroid.Minors
import Mathlib.Combinatorics.Graph.Delete

/-! Labeled graph-minor constructions for graphic matroids. -/

namespace Graph

variable {α β : Type*} (G : Graph α β) (D A : Set β)

private theorem linkedOn_deleteEdges_iff (hA : A ⊆ Dᶜ)
    {u v : α} :
    (G.deleteEdges D).LinkedOn
      ((G.deleteEdges D).edgeEmbedding ⁻¹' A) u v ↔
      G.LinkedOn (G.edgeEmbedding ⁻¹' A) u v := by
  constructor
  · rintro ⟨e, heA, hlink⟩
    exact ⟨⟨e, hlink.1.edge_mem⟩, heA, hlink.1⟩
  · rintro ⟨e, heA, hlink⟩
    have heD : (e : β) ∉ D := hA heA
    exact ⟨⟨e, by simp [heD, hlink.edge_mem]⟩, heA,
      ⟨hlink, heD⟩⟩

private theorem reachableOn_deleteEdges_iff (hA : A ⊆ Dᶜ)
    (u v : α) :
    (G.deleteEdges D).ReachableOn
      ((G.deleteEdges D).edgeEmbedding ⁻¹' A) u v ↔
      G.ReachableOn (G.edgeEmbedding ⁻¹' A) u v := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hlink ih =>
        exact ih.tail ((linkedOn_deleteEdges_iff G D A hA).1 hlink)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hlink ih =>
        exact ih.tail ((linkedOn_deleteEdges_iff G D A hA).2 hlink)

/-- Identify precisely two vertices. If they coincide, this quotient is
isomorphic to the original vertex type. -/
def identifyVertices (u v : α) : Setoid α where
  r x y := x = y ∨ ((x = u ∨ x = v) ∧ (y = u ∨ y = v))
  iseqv := by
    constructor
    · intro x
      exact Or.inl rfl
    · intro x y h
      rcases h with rfl | ⟨hx, hy⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hy, hx⟩
    · intro x y z hxy hyz
      rcases hxy with rfl | ⟨hx, hy⟩
      · exact hyz
      rcases hyz with rfl | ⟨hy', hz⟩
      · exact Or.inr ⟨hx, hy⟩
      · exact Or.inr ⟨hx, hz⟩

abbrev ContractVertex (u v : α) := Quotient (identifyVertices u v)

def contractVertex (u v : α) (x : α) : ContractVertex u v :=
  Quotient.mk (identifyVertices u v) x

theorem contractVertex_eq_iff (u v x y : α) :
    contractVertex u v x = contractVertex u v y ↔
      x = y ∨ ((x = u ∨ x = v) ∧ (y = u ∨ y = v)) := by
  exact Quotient.eq

theorem contractVertex_endpoints_eq (u v : α) :
    contractVertex u v u = contractVertex u v v :=
  (contractVertex_eq_iff u v u v).2 (Or.inr ⟨Or.inl rfl, Or.inr rfl⟩)

/-- Delete one edge and identify its two endpoints, retaining every other
edge label. The endpoints may be equal, and loops and parallel edges among
the surviving labels remain present. -/
def contractEdge (e : β) (u v : α) : Graph (ContractVertex u v) β where
  vertexSet := contractVertex u v '' G.vertexSet
  edgeSet := G.edgeSet \ {e}
  IsLink f x y := f ≠ e ∧
    ∃ a b, G.IsLink f a b ∧ contractVertex u v a = x ∧ contractVertex u v b = y
  isLink_symm := by
    intro f _
    constructor
    intro x y h
    obtain ⟨hne, a, b, hab, rfl, rfl⟩ := h
    exact ⟨hne, b, a, hab.symm, rfl, rfl⟩
  eq_or_eq_of_isLink_of_isLink := by
    intro f x y z w hxy hzw
    obtain ⟨_, a, b, hab, rfl, rfl⟩ := hxy
    obtain ⟨_, c, d, hcd, rfl, rfl⟩ := hzw
    rcases hab.left_eq_or_eq hcd with h | h
    · exact Or.inl (congrArg (contractVertex u v) h)
    · exact Or.inr (congrArg (contractVertex u v) h)
  edge_mem_iff_exists_isLink := by
    intro f
    constructor
    · intro hf
      obtain ⟨a, b, hab⟩ := G.exists_isLink_of_mem_edgeSet hf.1
      exact ⟨contractVertex u v a, contractVertex u v b,
        hf.2, a, b, hab, rfl, rfl⟩
    · rintro ⟨x, y, hne, a, b, hab, _, _⟩
      exact ⟨hab.edge_mem, hne⟩
  left_mem_of_isLink := by
    intro f x y h
    obtain ⟨_, a, b, hab, rfl, _⟩ := h
    exact ⟨a, hab.left_mem, rfl⟩

@[simp] theorem contractEdge_edgeSet (e : β) (u v : α) :
    (G.contractEdge e u v).edgeSet = G.edgeSet \ {e} := rfl

private theorem reachableOn_of_same_contractVertex {e : β} {u v : α}
    (he : G.IsLink e u v) (A : Set β) {x y : α}
    (hxy : contractVertex u v x = contractVertex u v y) :
    G.ReachableOn (G.edgeEmbedding ⁻¹' (A ∪ {e})) x y := by
  rcases (contractVertex_eq_iff u v x y).1 hxy with rfl | ⟨hx, hy⟩
  · exact Relation.ReflTransGen.refl
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single
      ⟨⟨e, he.edge_mem⟩, Or.inr (by rfl), he⟩
  · exact Relation.ReflTransGen.single
      ⟨⟨e, he.edge_mem⟩, Or.inr (by rfl), he.symm⟩
  · exact Relation.ReflTransGen.refl

private theorem original_linkedOn_of_contracted_linkedOn {e : β} {u v : α}
    (he : G.IsLink e u v) (A : Set β) {x y : α}
    (h : (G.contractEdge e u v).LinkedOn
      ((G.contractEdge e u v).edgeEmbedding ⁻¹' A)
        (contractVertex u v x) (contractVertex u v y)) :
    G.ReachableOn (G.edgeEmbedding ⁻¹' (A ∪ {e})) x y := by
  obtain ⟨f, hfA, hflink⟩ := h
  obtain ⟨_, a, b, hab, hax, hby⟩ := hflink
  have hleft := reachableOn_of_same_contractVertex G he A hax.symm
  have hright := reachableOn_of_same_contractVertex G he A hby
  have hmid : G.ReachableOn (G.edgeEmbedding ⁻¹' (A ∪ {e})) a b :=
    Relation.ReflTransGen.single
      ⟨⟨f, hab.edge_mem⟩, by exact Or.inl hfA, hab⟩
  exact (hleft.trans hmid).trans hright

private theorem original_reachableOn_of_contracted_reachableOn
    {e : β} {u v : α} (he : G.IsLink e u v) (A : Set β)
    {p q : ContractVertex u v}
    (hreach : (G.contractEdge e u v).ReachableOn
      ((G.contractEdge e u v).edgeEmbedding ⁻¹' A) p q) :
    ∀ x y : α, contractVertex u v x = p → contractVertex u v y = q →
      G.ReachableOn (G.edgeEmbedding ⁻¹' (A ∪ {e})) x y := by
  induction hreach with
  | refl =>
      intro x y hx hy
      exact reachableOn_of_same_contractVertex G he A (hx.trans hy.symm)
  | tail hprior hlink ih =>
      intro x y hx hy
      obtain ⟨f, hfA, hflink⟩ := hlink
      obtain ⟨hne, a, b, hab, ha, hb⟩ := hflink
      have hfirst := ih x a hx ha
      have hlast : G.ReachableOn (G.edgeEmbedding ⁻¹' (A ∪ {e})) a y := by
        apply original_linkedOn_of_contracted_linkedOn G he A
        refine ⟨f, hfA, hne, a, b, hab, rfl, ?_⟩
        exact hb.trans hy.symm
      exact hfirst.trans hlast

private theorem contracted_reachableOn_of_original_linkedOn
    {e : β} {u v : α} (he : G.IsLink e u v) (A : Set β)
    {x y : α}
    (h : G.LinkedOn (G.edgeEmbedding ⁻¹' (A ∪ {e})) x y) :
    (G.contractEdge e u v).ReachableOn
      ((G.contractEdge e u v).edgeEmbedding ⁻¹' A)
        (contractVertex u v x) (contractVertex u v y) := by
  obtain ⟨f, hfA, hlink⟩ := h
  by_cases hfe : (f : β) = e
  · subst e
    rcases (he.isLink_iff.mp hlink) with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
    · subst x; subst y
      rw [contractVertex_endpoints_eq]
      exact Relation.ReflTransGen.refl
    · subst x; subst y
      rw [← contractVertex_endpoints_eq]
      exact Relation.ReflTransGen.refl
  · have hf : (f : β) ∈ A := by
      rcases hfA with hfA | hfA
      · exact hfA
      · have hfeq : (f : β) = e := by
          simpa [Graph.edgeEmbedding] using hfA
        exact (hfe hfeq).elim
    exact Relation.ReflTransGen.single
      ⟨⟨f, by simp [Graph.contractEdge_edgeSet, hfe, hlink.edge_mem]⟩,
        hf, ⟨hfe, x, y, hlink, rfl, rfl⟩⟩

private theorem contracted_reachableOn_of_original_reachableOn
    {e : β} {u v : α} (he : G.IsLink e u v) (A : Set β)
    {x y : α}
    (hreach : G.ReachableOn (G.edgeEmbedding ⁻¹' (A ∪ {e})) x y) :
    (G.contractEdge e u v).ReachableOn
      ((G.contractEdge e u v).edgeEmbedding ⁻¹' A)
        (contractVertex u v x) (contractVertex u v y) := by
  induction hreach with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hlink ih =>
      exact ih.trans (contracted_reachableOn_of_original_linkedOn G he A hlink)

/-- Collapsing a chosen edge has the same path relation as allowing that
edge in the original graph. The selected surviving labels remain unchanged. -/
theorem reachableOn_contractEdge_iff
    {e : β} {u v : α} (he : G.IsLink e u v)
    (A : Set β) (x y : α) :
    (G.contractEdge e u v).ReachableOn
      ((G.contractEdge e u v).edgeEmbedding ⁻¹' A)
        (contractVertex u v x) (contractVertex u v y) ↔
      G.ReachableOn (G.edgeEmbedding ⁻¹' (A ∪ {e})) x y := by
  constructor
  · intro h
    exact original_reachableOn_of_contracted_reachableOn G he A h x y rfl rfl
  · exact contracted_reachableOn_of_original_reachableOn G he A

end Graph

namespace Matroid

variable {α β : Type*} (G : Graph α β)

/-- N174 partial: graph edge deletion exactly matches deletion in the
graphic matroid on the surviving original edge labels. -/
theorem graphic_deleteEdges_eq_delete
    (hE : G.edgeSet.Finite) (D : Set β) :
    graphic (G.deleteEdges D)
      (by simpa using hE.subset (Set.sdiff_subset : G.edgeSet \ D ⊆ G.edgeSet)) =
        (graphic G hE) ＼ D := by
  have hE' : (G.deleteEdges D).edgeSet.Finite := by
    simpa using hE.subset (Set.sdiff_subset : G.edgeSet \ D ⊆ G.edgeSet)
  apply Matroid.ext_closure
  intro X
  rw [Matroid.delete_closure_eq]
  ext e
  by_cases he : e ∈ G.edgeSet \ D
  · obtain ⟨u, v, hlink⟩ := G.exists_isLink_of_mem_edgeSet he.1
    have hlink' : (G.deleteEdges D).IsLink e u v := ⟨hlink, he.2⟩
    rw [graphic_mem_closure_iff_reachableOn (G.deleteEdges D) hE' X e
      (by simpa using he) hlink']
    rw [Set.mem_sdiff, graphic_mem_closure_iff_reachableOn G hE (X \ D) e he.1 hlink]
    simp only [he.2, not_false_eq_true, and_true]
    have hpre : (G.deleteEdges D).edgeEmbedding ⁻¹' X =
        (G.deleteEdges D).edgeEmbedding ⁻¹' (X \ D) := by
      ext f
      have hfD : (f : β) ∉ D := by simpa using f.property.2
      change ((f : β) ∈ X ↔ (f : β) ∈ X ∧ (f : β) ∉ D)
      exact (and_iff_left hfD).symm
    rw [hpre]
    exact Graph.reachableOn_deleteEdges_iff G D (X \ D)
      (Set.sdiff_subset_compl X D) u v
  · have hnotleft : e ∉ (graphic (G.deleteEdges D) hE').closure X := by
      intro h
      exact he (by simpa using (graphic (G.deleteEdges D) hE').mem_ground_of_mem_closure h)
    have hnotright : e ∉ (graphic G hE).closure (X \ D) \ D := by
      intro h
      have heG : e ∈ G.edgeSet := by
        simpa using (graphic G hE).mem_ground_of_mem_closure h.1
      exact he ⟨heG, h.2⟩
    exact iff_of_false hnotleft hnotright

/-- Contracting one actual labeled graph edge agrees with contraction of
the graphic matroid. This includes a loop (whose endpoints coincide) and
parallel surviving labels. -/
theorem graphic_contractEdge_eq_contract
    (hE : G.edgeSet.Finite) {e : β} {u v : α}
    (he : G.IsLink e u v) :
    graphic (G.contractEdge e u v)
      (by simpa using hE.subset (Set.sdiff_subset : G.edgeSet \ {e} ⊆ G.edgeSet)) =
        (graphic G hE) ／ {e} := by
  have hE' : (G.contractEdge e u v).edgeSet.Finite := by
    simpa using hE.subset (Set.sdiff_subset : G.edgeSet \ {e} ⊆ G.edgeSet)
  apply Matroid.ext_closure
  intro X
  rw [Matroid.contract_closure_eq]
  ext f
  by_cases hf : f ∈ G.edgeSet \ {e}
  · obtain ⟨a, b, hab⟩ := G.exists_isLink_of_mem_edgeSet hf.1
    have hlink' : (G.contractEdge e u v).IsLink f
        (Graph.contractVertex u v a) (Graph.contractVertex u v b) :=
      ⟨hf.2, a, b, hab, rfl, rfl⟩
    rw [graphic_mem_closure_iff_reachableOn (G.contractEdge e u v) hE' X f
      (by simpa using hf) hlink']
    rw [Set.mem_sdiff, graphic_mem_closure_iff_reachableOn G hE (X ∪ {e}) f hf.1 hab]
    simp only [hf.2, not_false_eq_true, and_true]
    exact G.reachableOn_contractEdge_iff he X a b
  · have hnotleft : f ∉ (graphic (G.contractEdge e u v) hE').closure X := by
      intro h
      exact hf (by simpa using (graphic (G.contractEdge e u v) hE').mem_ground_of_mem_closure h)
    have hnotright : f ∉ (graphic G hE).closure (X ∪ {e}) \ {e} := by
      intro h
      have hfG : f ∈ G.edgeSet := by
        simpa using (graphic G hE).mem_ground_of_mem_closure h.1
      exact hf ⟨hfG, h.2⟩
    exact iff_of_false hnotleft hnotright

/-- A finite labeled graph realization of a matroid. The vertex type may
change under edge contraction, while the edge-label type stays fixed. -/
def IsGraphic.{u,v} {β : Type v} (M : Matroid β) : Prop :=
  ∃ (α : Type u) (G : Graph α β) (hE : G.edgeSet.Finite), M = graphic G hE

theorem isGraphic_graphic {α : Type u} {β : Type v}
    (G : Graph α β) (hE : G.edgeSet.Finite) :
    (graphic G hE).IsGraphic.{u,v} :=
  ⟨α, G, hE, rfl⟩

theorem IsGraphic.delete {β : Type v} {M : Matroid β}
    (hM : M.IsGraphic.{u,v}) (D : Set β) :
    (M ＼ D).IsGraphic.{u,v} := by
  obtain ⟨α, G, hE, rfl⟩ := hM
  exact ⟨α, G.deleteEdges D,
    (by simpa using hE.subset (Set.sdiff_subset : G.edgeSet \ D ⊆ G.edgeSet)),
      (graphic_deleteEdges_eq_delete G hE D).symm⟩

theorem IsGraphic.contractElem {β : Type v} {M : Matroid β}
    (hM : M.IsGraphic.{u,v}) (e : β) :
    (M ／ {e}).IsGraphic.{u,v} := by
  obtain ⟨α, G, hE, rfl⟩ := hM
  by_cases he : e ∈ G.edgeSet
  · obtain ⟨a, b, hab⟩ := G.exists_isLink_of_mem_edgeSet he
    have hE' : (G.contractEdge e a b).edgeSet.Finite := by
      simpa using hE.subset
        (Set.sdiff_subset : G.edgeSet \ {e} ⊆ G.edgeSet)
    exact ⟨Graph.ContractVertex a b, G.contractEdge e a b, hE',
      (graphic_contractEdge_eq_contract G hE hab).symm⟩
  · have hnot : e ∉ (graphic G hE).E := by simpa using he
    rw [Matroid.contractElem_eq_self hnot]
    exact isGraphic_graphic G hE

theorem IsGraphic.contract {β : Type v} {M : Matroid β}
    (hM : M.IsGraphic.{u,v}) (C : Set β) :
    (M ／ C).IsGraphic.{u,v} := by
  have hME : M.E.Finite := by
    obtain ⟨α, G, hE, hEq⟩ := hM
    rw [hEq]
    simpa using hE
  have hC : (C ∩ M.E).Finite := hME.subset Set.inter_subset_right
  have aux (S : Set β) (hS : S.Finite) : (M ／ S).IsGraphic.{u,v} := by
    induction S, hS using Set.Finite.induction_on with
    | empty => simpa using hM
    | @insert e S heS hS ih =>
        have h := ih.contractElem e
        simpa [M.contract_contract, Set.union_comm] using h
  rw [← M.contract_inter_ground_eq C]
  exact aux (C ∩ M.E) hC

/-- N174: every matroid minor of a finite labeled graphic matroid is
graphic on its surviving original edge labels. -/
theorem IsGraphic.minor {β : Type v} {M N : Matroid β}
    (hM : M.IsGraphic.{u,v}) (hNM : N ≤m M) :
    N.IsGraphic.{u,v} := by
  obtain ⟨C, D, rfl⟩ := (minor_iff_contract_delete N M).1 hNM
  exact (hM.contract C).delete D

end Matroid
