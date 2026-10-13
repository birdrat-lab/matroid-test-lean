import Matroid.Graphic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases

/-! The labeled six-path graphic component in the second R10 program. -/

namespace Matroid.DoubleStar

/-- The nine Boolean query labels `eᵢⱼ`. -/
abbrev Query := Fin 3 × Fin 3

/-- Three row paths join `source` to `middle`; three column paths join
`middle` to `sink`. Each path has two distinct internal vertices. -/
inductive Vertex where
  | source | middle | sink
  | rowFirst (i : Fin 3) | rowSecond (i : Fin 3)
  | colFirst (j : Fin 3) | colSecond (j : Fin 3)
  deriving DecidableEq, Fintype

/-- There are 18 response edges and one distinguished target edge. -/
inductive Edge where
  | target
  | row (i j : Fin 3)
  | col (i j : Fin 3)
  deriving DecidableEq, Fintype

/-- The first index of a row edge chooses its row path; the second index
chooses its position. Column edges reverse those roles. -/
def ends : Edge → Vertex × Vertex
  | .target => (.source, .sink)
  | .row i 0 => (.source, .rowFirst i)
  | .row i 1 => (.rowFirst i, .rowSecond i)
  | .row i _ => (.rowSecond i, .middle)
  | .col 0 j => (.middle, .colFirst j)
  | .col 1 j => (.colFirst j, .colSecond j)
  | .col _ j => (.colSecond j, .sink)

/-- The actual labeled multigraph, with all nineteen edges present. -/
def graph : Graph Vertex Edge where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink e u v := (u, v) = ends e ∨ (v, u) = ends e
  isLink_symm := by
    simp [symm_def, or_comm]
  eq_or_eq_of_isLink_of_isLink := by
    intro e x y v w hxy hvw
    rcases hxy with hxy | hxy <;> rcases hvw with hvw | hvw
    · exact Or.inl ((Prod.mk.inj (hxy.trans hvw.symm)).1)
    · exact Or.inr ((Prod.mk.inj (hxy.trans hvw.symm)).1)
    · exact Or.inr ((Prod.mk.inj (hxy.trans hvw.symm)).2)
    · exact Or.inl ((Prod.mk.inj (hxy.trans hvw.symm)).2)
  edge_mem_iff_exists_isLink := by
    intro e
    constructor
    · intro _
      exact ⟨(ends e).1, (ends e).2, Or.inl rfl⟩
    · simp

theorem edgeSet_eq_univ : graph.edgeSet = Set.univ := rfl

theorem query_label_count : Fintype.card Query = 9 := by decide

theorem graph_edge_count : Fintype.card Edge = 19 := by decide

/-- Both copies of query `eᵢⱼ` have the same availability predicate. -/
def availableEdges (A : Set Query) : Set Edge :=
  {e | match e with
    | .target => False
    | .row i j => (i, j) ∈ A
    | .col i j => (i, j) ∈ A}

@[simp] theorem target_not_available (A : Set Query) :
    Edge.target ∉ availableEdges A := by simp [availableEdges]

@[simp] theorem row_available_iff (A : Set Query) (i j : Fin 3) :
    Edge.row i j ∈ availableEdges A ↔ (i, j) ∈ A := by
  rfl

@[simp] theorem col_available_iff (A : Set Query) (i j : Fin 3) :
    Edge.col i j ∈ availableEdges A ↔ (i, j) ∈ A := by
  rfl

def rowQueries (i : Fin 3) : Set Query := {q | q.1 = i}
def colQueries (j : Fin 3) : Set Query := {q | q.2 = j}

/-- A generic path invariant: an edge predicate that has the same truth
value at both ends of every selected edge has the same value at the ends of
every selected finite walk. -/
private theorem reachableOn_preserves (A : Set Query) (P : Vertex → Prop)
    (hP : ∀ e ∈ availableEdges A,
      P (ends e).1 ↔ P (ends e).2)
    {u v : Vertex}
    (hreach : graph.ReachableOn
      (graph.edgeEmbedding ⁻¹' availableEdges A) u v) :
    P u ↔ P v := by
  have hlink : ∀ {x y : Vertex},
      graph.LinkedOn (graph.edgeEmbedding ⁻¹' availableEdges A) x y →
        (P x ↔ P y) := by
    intro x y h
    obtain ⟨e, he, heLink⟩ := h
    have heA : (e : Edge) ∈ availableEdges A := he
    change ((x, y) = ends (e : Edge) ∨ (y, x) = ends (e : Edge)) at heLink
    rcases heLink with h | h
    · rcases Prod.mk.inj h with ⟨rfl, rfl⟩
      exact hP e heA
    · rcases Prod.mk.inj h with ⟨rfl, rfl⟩
      exact (hP e heA).symm
  induction hreach with
  | refl => exact Iff.rfl
  | tail _ h ih => exact ih.trans (hlink h)

/-- Vertices reachable from the source if the middle vertex cannot be
reached through a complete row path. -/
private def sourceRegion (A : Set Query) : Vertex → Prop
  | .source => True
  | .rowFirst i => (i, 0) ∈ A
  | .rowSecond i => (i, 0) ∈ A ∧ (i, 1) ∈ A
  | _ => False

/-- Vertices reachable backwards from the sink if the middle vertex
cannot be reached through a complete column path. -/
private def sinkRegion (A : Set Query) : Vertex → Prop
  | .sink => True
  | .colSecond j => (2, j) ∈ A
  | .colFirst j => (1, j) ∈ A ∧ (2, j) ∈ A
  | _ => False

private theorem sourceRegion_edge (A : Set Query)
    (hNoRow : ∀ i : Fin 3, ¬ ∀ j : Fin 3, (i, j) ∈ A) :
    ∀ e ∈ availableEdges A,
      sourceRegion A (ends e).1 ↔ sourceRegion A (ends e).2 := by
  intro e he
  cases e with
  | target => simp at he
  | row i j =>
      fin_cases j
      · simpa [ends, sourceRegion] using he
      · change (i, (1 : Fin 3)) ∈ A at he
        simp [ends, sourceRegion, he]
      · have h : ¬ ((i, 0) ∈ A ∧ (i, 1) ∈ A) := by
          intro hp
          apply hNoRow i
          intro j
          fin_cases j <;> simp_all
        simp [ends, sourceRegion, h]
  | col i j =>
      fin_cases i <;> simp [ends, sourceRegion]

private theorem sinkRegion_edge (A : Set Query)
    (hNoCol : ∀ j : Fin 3, ¬ ∀ i : Fin 3, (i, j) ∈ A) :
    ∀ e ∈ availableEdges A,
      sinkRegion A (ends e).1 ↔ sinkRegion A (ends e).2 := by
  intro e he
  cases e with
  | target => simp at he
  | row i j =>
      fin_cases j <;> simp [ends, sinkRegion]
  | col i j =>
      fin_cases i
      · have h : ¬ ((1, j) ∈ A ∧ (2, j) ∈ A) := by
          intro hp
          apply hNoCol j
          intro i
          fin_cases i <;> simp_all
        simp [ends, sinkRegion, h]
      · change ((1 : Fin 3), j) ∈ A at he
        simp [ends, sinkRegion, he]
      · simpa [ends, sinkRegion] using he

private theorem reachableOn_has_full_row (A : Set Query)
    (hreach : graph.ReachableOn
      (graph.edgeEmbedding ⁻¹' availableEdges A) .source .sink) :
    ∃ i : Fin 3, ∀ j : Fin 3, (i, j) ∈ A := by
  classical
  by_contra hn
  have hn' : ∀ i : Fin 3, ¬ ∀ j : Fin 3, (i, j) ∈ A := by
    intro i hi
    exact hn ⟨i, hi⟩
  have hsame := reachableOn_preserves A (sourceRegion A)
    (sourceRegion_edge A hn') hreach
  exact hsame.mp trivial

private theorem reachableOn_has_full_col (A : Set Query)
    (hreach : graph.ReachableOn
      (graph.edgeEmbedding ⁻¹' availableEdges A) .source .sink) :
    ∃ j : Fin 3, ∀ i : Fin 3, (i, j) ∈ A := by
  classical
  by_contra hn
  have hn' : ∀ j : Fin 3, ¬ ∀ i : Fin 3, (i, j) ∈ A := by
    intro j hj
    exact hn ⟨j, hj⟩
  have hsame := reachableOn_preserves A (sinkRegion A)
    (sinkRegion_edge A hn') hreach
  exact hsame.mpr trivial

private theorem linkedOn_of_available (A : Set Query) (e : Edge)
    (he : e ∈ availableEdges A) (u v : Vertex)
    (huv : (u, v) = ends e) :
    graph.LinkedOn (graph.edgeEmbedding ⁻¹' availableEdges A) u v := by
  refine ⟨⟨e, by simp [graph]⟩, he, Or.inl huv⟩

private theorem reachableOn_of_full_row_col (A : Set Query)
    {i j : Fin 3} (hr : ∀ k : Fin 3, (i, k) ∈ A)
    (hc : ∀ k : Fin 3, (k, j) ∈ A) :
    graph.ReachableOn (graph.edgeEmbedding ⁻¹' availableEdges A)
      .source .sink := by
  have h₁ := linkedOn_of_available A (.row i 0) (hr 0)
    .source (.rowFirst i) rfl
  have h₂ := linkedOn_of_available A (.row i 1) (hr 1)
    (.rowFirst i) (.rowSecond i) rfl
  have h₃ := linkedOn_of_available A (.row i 2) (hr 2)
    (.rowSecond i) .middle rfl
  have h₄ := linkedOn_of_available A (.col 0 j) (hc 0)
    .middle (.colFirst j) rfl
  have h₅ := linkedOn_of_available A (.col 1 j) (hc 1)
    (.colFirst j) (.colSecond j) rfl
  have h₆ := linkedOn_of_available A (.col 2 j) (hc 2)
    (.colSecond j) .sink rfl
  exact (((((Relation.ReflTransGen.single h₁).tail h₂).tail h₃).tail h₄).tail h₅).tail h₆

/-- Exact target reachability in the six-path graph. Both copies of each
query label are governed by the same Boolean availability. -/
theorem reachableOn_iff_full_row_col (A : Set Query) :
    graph.ReachableOn (graph.edgeEmbedding ⁻¹' availableEdges A)
      .source .sink ↔
      ∃ i j : Fin 3,
        rowQueries i ∪ colQueries j ⊆ A := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := reachableOn_has_full_row A h
    obtain ⟨j, hj⟩ := reachableOn_has_full_col A h
    refine ⟨i, j, ?_⟩
    intro ⟨a, b⟩ hq
    rcases hq with hq | hq
    · change a = i at hq
      subst a
      exact hi b
    · change b = j at hq
      subst b
      exact hj a
  · rintro ⟨i, j, hij⟩
    apply reachableOn_of_full_row_col A
    · intro k
      exact hij (Or.inl rfl)
    · intro k
      exact hij (Or.inr rfl)

/-- N207: the target edge is spanned exactly on inputs containing a full
row and a full column of the nine Boolean query labels. -/
theorem target_mem_graphic_closure_iff (A : Set Query) :
    Edge.target ∈ (Matroid.graphic graph (by rw [edgeSet_eq_univ]; exact Set.finite_univ)).closure
      (availableEdges A) ↔
      ∃ i j : Fin 3, rowQueries i ∪ colQueries j ⊆ A := by
  have hE : graph.edgeSet.Finite := by
    rw [edgeSet_eq_univ]
    exact Set.finite_univ
  have htarget : graph.IsLink Edge.target .source .sink := Or.inl rfl
  have h := Matroid.graphic_mem_closure_iff_reachableOn graph hE
    (availableEdges A) Edge.target (by simp [edgeSet_eq_univ]) htarget
  exact h.trans (reachableOn_iff_full_row_col A)

/-- One of the nine candidate minimal accepting query sets. -/
def support (i j : Fin 3) : Set Query := rowQueries i ∪ colQueries j

/-- Acceptance by the graphic component, stated directly on Boolean query
labels rather than the doubled graph-edge labels. -/
def Accepts (A : Set Query) : Prop :=
  ∃ i j : Fin 3, support i j ⊆ A

theorem target_mem_graphic_closure_iff_accepts (A : Set Query) :
    Edge.target ∈ (Matroid.graphic graph (by rw [edgeSet_eq_univ]; exact Set.finite_univ)).closure
      (availableEdges A) ↔ Accepts A :=
  target_mem_graphic_closure_iff A

private theorem support_subset_forces_indices (i j k l : Fin 3)
    (h : support i j ⊆ support k l) : i = k ∧ j = l := by
  have hfinite : ∀ i j k l : Fin 3,
      (∀ a b : Fin 3, (a = i ∨ b = j) → (a = k ∨ b = l)) →
        i = k ∧ j = l := by decide
  apply hfinite i j k l
  intro a b hab
  have hmem : (a, b) ∈ support i j := by
    simpa [support, rowQueries, colQueries] using hab
  simpa [support, rowQueries, colQueries] using h hmem

theorem support_minimal (i j : Fin 3) :
    Minimal Accepts (support i j) := by
  constructor
  · exact ⟨i, j, subset_rfl⟩
  · intro S hS hSub
    obtain ⟨k, l, hk⟩ := hS
    obtain ⟨rfl, rfl⟩ := support_subset_forces_indices k l i j (hk.trans hSub)
    exact hk

/-- N207: the inclusion-minimal accepting Boolean query sets are exactly
the nine row-column double stars. -/
theorem minimal_accepting_iff (S : Set Query) :
    Minimal Accepts S ↔ ∃ i j : Fin 3, S = support i j := by
  constructor
  · intro h
    obtain ⟨i, j, hij⟩ := h.1
    have hback : S ⊆ support i j := h.2 ⟨i, j, subset_rfl⟩ hij
    exact ⟨i, j, Set.Subset.antisymm hback hij⟩
  · rintro ⟨i, j, rfl⟩
    exact support_minimal i j

/-- Distinct row-column pairs give distinct minimal query sets. -/
theorem support_injective :
    Function.Injective (fun p : Query => support p.1 p.2) := by
  intro ⟨i, j⟩ ⟨k, l⟩ h
  obtain ⟨rfl, rfl⟩ := support_subset_forces_indices i j k l (le_of_eq h)
  rfl

/-- Each double star has three row and three column queries with one
shared query, hence five distinct Boolean labels. -/
theorem support_ncard (i j : Fin 3) : (support i j).ncard = 5 := by
  let F : Finset Query := Finset.univ.filter (fun q => q.1 = i ∨ q.2 = j)
  have hfin : (support i j).Finite := Set.toFinite _
  have hF : hfin.toFinset = F := by
    ext q
    simp [F, support, rowQueries, colQueries]
  rw [Set.ncard_eq_toFinset_card _ hfin, hF]
  fin_cases i <;> fin_cases j <;> decide

end Matroid.DoubleStar
