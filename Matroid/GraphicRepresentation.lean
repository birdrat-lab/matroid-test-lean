import Matroid.Graphic
import Matroid.Representation
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Basic.Real.Basic

/-! # Signed incidence columns for labeled multigraphs -/

namespace Graph

variable {α β : Type*} (G : Graph α β)

/-- Sum of the coordinates of a finitely supported vertex vector on one
side of a cut. -/
noncomputable def sideFunctional (S : Set α) : (α →₀ ℝ) →ₗ[ℝ] ℝ :=
  by
    classical
    exact Finsupp.lsum ℝ (fun x => if x ∈ S then LinearMap.id else 0)

private theorem sideFunctional_endpointDiff (S : Set α) [DecidablePred (· ∈ S)] (u v : α) :
    sideFunctional S (Finsupp.single u 1 - Finsupp.single v 1) =
      (if u ∈ S then (1 : ℝ) else 0) - (if v ∈ S then (1 : ℝ) else 0) := by
  classical
  rw [map_sub]
  simp only [sideFunctional, Finsupp.lsum_single]
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;> simp [hu, hv]

/-- Manuscript ledger N258. An orientation chooses ordered endpoints for each
actual edge. Parallel edges retain separate labels. -/
def IsEdgeOrientation (ends : G.EdgeIndex → α × α) : Prop :=
  ∀ e : G.EdgeIndex, G.IsLink e.1 (ends e).1 (ends e).2

/-- Every actual labeled edge has endpoints, so an orientation exists even
when the ambient vertex or edge-label type is empty. -/
theorem exists_edgeOrientation : ∃ ends : G.EdgeIndex → α × α,
    G.IsEdgeOrientation ends := by
  classical
  let ends : G.EdgeIndex → α × α := fun e =>
    let h := (G.edge_mem_iff_exists_isLink e.1).1 e.2
    ⟨Classical.choose h, Classical.choose (Classical.choose_spec h)⟩
  refine ⟨ends, ?_⟩
  intro e
  exact Classical.choose_spec (Classical.choose_spec
    ((G.edge_mem_iff_exists_isLink e.1).1 e.2))

/-- Manuscript ledger N258; signed real incidence column. A loop has equal
endpoints and hence gives the zero column. -/
noncomputable def incidenceColumn (ends : G.EdgeIndex → α × α) (e : β) : α →₀ ℝ :=
  by
    classical
    exact if he : e ∈ G.edgeSet then
      Finsupp.single (ends ⟨e, he⟩).1 1 - Finsupp.single (ends ⟨e, he⟩).2 1
    else 0

theorem incidenceColumn_loop (ends : G.EdgeIndex → α × α)
    (hends : G.IsEdgeOrientation ends) {e : β} {x : α}
    (hloop : G.IsLoopAt e x) : G.incidenceColumn ends e = 0 := by
  have he : e ∈ G.edgeSet := (G.edge_mem_iff_exists_isLink e).2 ⟨x, x, hloop⟩
  let ê : G.EdgeIndex := ⟨e, he⟩
  have hlink := hends ê
  have hfirst : (ends ê).1 = x := by
    rcases G.eq_or_eq_of_isLink_of_isLink hlink hloop with h | h <;> exact h
  have hsecond : (ends ê).2 = x := by
    rcases G.eq_or_eq_of_isLink_of_isLink
      ((G.isLink_symm he).symm (ends ê).1 (ends ê).2 hlink) hloop with h | h <;> exact h
  simp only [incidenceColumn, dite_eq_left he]
  change Finsupp.single (ends ê).1 1 - Finsupp.single (ends ê).2 1 = 0
  simp [hfirst, hsecond]

/-- A signed incidence column for an edge is one of the two endpoint
differences, according to the chosen orientation. -/
theorem incidenceColumn_eq_or (ends : G.EdgeIndex → α × α)
    (hends : G.IsEdgeOrientation ends) {e : β} {u v : α}
    (hlink : G.IsLink e u v) :
    G.incidenceColumn ends e = Finsupp.single u 1 - Finsupp.single v 1 ∨
      G.incidenceColumn ends e = Finsupp.single v 1 - Finsupp.single u 1 := by
  have he : e ∈ G.edgeSet := hlink.edge_mem
  let ê : G.EdgeIndex := ⟨e, he⟩
  have horient := hends ê
  rcases horient.eq_and_eq_or_eq_and_eq hlink with h | h
  · left
    simp only [incidenceColumn, dite_eq_left he]
    change Finsupp.single (ends ê).1 1 - Finsupp.single (ends ê).2 1 = _
    rw [h.1, h.2]
  · right
    simp only [incidenceColumn, dite_eq_left he]
    change Finsupp.single (ends ê).1 1 - Finsupp.single (ends ê).2 1 = _
    rw [h.1, h.2]

private theorem sideFunctional_incidence_eq_zero_of_not_cut
    (ends : G.EdgeIndex → α × α) (hends : G.IsEdgeOrientation ends)
    (S : Set α) (e : G.EdgeIndex) (hnot : (e : β) ∉ G.edgeCut S) :
    sideFunctional S (G.incidenceColumn ends e.1) = 0 := by
  classical
  have hlink := hends e
  have hside : (ends e).1 ∈ S ↔ (ends e).2 ∈ S := by
    constructor
    · intro hu
      by_contra hv
      exact hnot (hlink.mem_edgeCut_iff.mpr (Or.inl ⟨hu, hv⟩))
    · intro hv
      by_contra hu
      exact hnot (hlink.mem_edgeCut_iff.mpr (Or.inr ⟨hv, hu⟩))
  simp only [incidenceColumn, dite_eq_left e.property]
  change sideFunctional S
      (Finsupp.single (ends e).1 1 - Finsupp.single (ends e).2 1) = 0
  rw [sideFunctional_endpointDiff]
  by_cases hu : (ends e).1 ∈ S
  · have hv := hside.mp hu
    simp [hu, hv]
  · have hv : (ends e).2 ∉ S := fun hv => hu (hside.mpr hv)
    simp [hu, hv]

private theorem sideFunctional_incidence_ne_zero_of_cut
    (ends : G.EdgeIndex → α × α) (hends : G.IsEdgeOrientation ends)
    (S : Set α) (e : G.EdgeIndex) (hcut : (e : β) ∈ G.edgeCut S) :
    sideFunctional S (G.incidenceColumn ends e.1) ≠ 0 := by
  classical
  have hlink := hends e
  rcases hlink.mem_edgeCut_iff.mp hcut with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · simp only [incidenceColumn, dite_eq_left e.property]
    change sideFunctional S
        (Finsupp.single (ends e).1 1 - Finsupp.single (ends e).2 1) ≠ 0
    rw [sideFunctional_endpointDiff]
    simp [hu, hv]
  · simp only [incidenceColumn, dite_eq_left e.property]
    change sideFunctional S
        (Finsupp.single (ends e).1 1 - Finsupp.single (ends e).2 1) ≠ 0
    rw [sideFunctional_endpointDiff]
    simp [hu, hv]

private theorem linkedOn_endpointDiff_mem_span (ends : G.EdgeIndex → α × α)
    (hends : G.IsEdgeOrientation ends) {A : Set G.EdgeIndex} {u v : α}
    (hlink : G.LinkedOn A u v) :
    Finsupp.single u (1 : ℝ) - Finsupp.single v 1 ∈
      Submodule.span ℝ ((fun e : G.EdgeIndex => G.incidenceColumn ends e.1) '' A) := by
  obtain ⟨e, heA, hlink⟩ := hlink
  have hcol : G.incidenceColumn ends e.1 ∈
      Submodule.span ℝ ((fun e : G.EdgeIndex => G.incidenceColumn ends e.1) '' A) :=
    Submodule.subset_span ⟨e, heA, rfl⟩
  rcases G.incidenceColumn_eq_or ends hends hlink with h | h
  · rwa [h] at hcol
  · have hneg := Submodule.neg_mem _ hcol
    rw [h] at hneg
    convert hneg using 1; abel

private theorem reachableOn_endpointDiff_mem_span (ends : G.EdgeIndex → α × α)
    (hends : G.IsEdgeOrientation ends) {A : Set G.EdgeIndex} {u v : α}
    (hreach : G.ReachableOn A u v) :
    Finsupp.single u (1 : ℝ) - Finsupp.single v 1 ∈
      Submodule.span ℝ ((fun e : G.EdgeIndex => G.incidenceColumn ends e.1) '' A) := by
  induction hreach with
  | refl => simp
  | tail _ hlink ih =>
      have hstep := G.linkedOn_endpointDiff_mem_span ends hends hlink
      have hadd := Submodule.add_mem _ ih hstep
      convert hadd using 1; abel

/-- A graph cycle gives a linear dependence among the signed incidence
columns, including the one-edge loop and two-edge parallel cases. -/
theorem not_linearIndepOn_incidence_of_cycle
    (ends : G.EdgeIndex → α × α) (hends : G.IsEdgeOrientation ends)
    {A : Set G.EdgeIndex} (hcycle : G.HasEdgeCycle A) :
    ¬ LinearIndepOn ℝ (fun e : G.EdgeIndex => G.incidenceColumn ends e.1) A := by
  intro hli
  obtain ⟨e, heA, u, v, hlink, hreach⟩ := hcycle
  have hpath := G.reachableOn_endpointDiff_mem_span ends hends hreach
  have hcol : G.incidenceColumn ends e.1 ∈
      Submodule.span ℝ
        ((fun f : G.EdgeIndex => G.incidenceColumn ends f.1) '' (A \ {e})) := by
    rcases G.incidenceColumn_eq_or ends hends hlink with h | h
    · rwa [h]
    · rw [h]
      have hneg := Submodule.neg_mem _ hpath
      convert hneg using 1; abel
  exact ((linearIndepOn_iff_notMem_span).1 hli e heA) hcol

/-- Forest independence supplies a cut functional isolating each incidence
column. This is the hard direction of the N258 representation theorem. -/
theorem linearIndepOn_incidence_of_forest
    (hE : G.edgeSet.Finite) (ends : G.EdgeIndex → α × α)
    (hends : G.IsEdgeOrientation ends) (A : Set G.EdgeIndex)
    (hforest : ¬ G.HasEdgeCycle A) :
    LinearIndepOn ℝ (fun e : G.EdgeIndex => G.incidenceColumn ends e.1) A := by
  have hmat : (G.edgeCutMatroid hE).Indep A :=
    (G.edgeCutMatroid_indep_iff_noEdgeCycle hE A).2 hforest
  apply (linearIndepOn_iff_notMem_span).2
  intro e heA hspan
  obtain ⟨C, ⟨S, hC⟩, hdisj, heC⟩ :=
    (G.edgeCutMatroid_indep_iff hE A).1 hmat e heA
  subst C
  have hno : ∀ f ∈ A \ {e}, (f : β) ∉ G.edgeCut S := by
    intro f hf hcut
    exact (Set.disjoint_left.mp hdisj) hf hcut
  have hker : Submodule.span ℝ
        ((fun f : G.EdgeIndex => G.incidenceColumn ends f.1) '' (A \ {e})) ≤
        LinearMap.ker (sideFunctional S) := by
    apply Submodule.span_le.mpr
    rintro x ⟨f, hf, rfl⟩
    change sideFunctional S (G.incidenceColumn ends f.1) = 0
    exact G.sideFunctional_incidence_eq_zero_of_not_cut ends hends S f (hno f hf)
  have hzero : sideFunctional S (G.incidenceColumn ends e.1) = 0 := hker hspan
  exact (G.sideFunctional_incidence_ne_zero_of_cut ends hends S e heC) hzero

private theorem linearIndependent_incidence_iff_linearIndepOn
    (ends : G.EdgeIndex → α × α) (I : Set β) (hI : I ⊆ G.edgeSet) :
    LinearIndependent ℝ (fun i : I => G.incidenceColumn ends i.1) ↔
      LinearIndepOn ℝ (fun e : G.EdgeIndex => G.incidenceColumn ends e.1)
        (G.edgeEmbedding ⁻¹' I) := by
  let A : Set G.EdgeIndex := G.edgeEmbedding ⁻¹' I
  let f : A ≃ I := {
    toFun := fun a => ⟨a.1.1, a.2⟩
    invFun := fun i => ⟨⟨i.1, hI i.2⟩, i.2⟩
    left_inv := by
      intro a
      apply Subtype.ext
      apply Subtype.ext
      rfl
    right_inv := by
      intro i
      apply Subtype.ext
      rfl }
  have hf : (fun i : I => G.incidenceColumn ends i.1) ∘ f =
      (fun a : A => G.incidenceColumn ends a.1.1) := by
    funext a
    rfl
  change LinearIndependent ℝ (fun i : I => G.incidenceColumn ends i.1) ↔
    LinearIndependent ℝ (fun a : A => G.incidenceColumn ends a.1.1)
  exact (linearIndependent_equiv' (R := ℝ) f hf).symm

/-- Manuscript ledger N258: real signed incidence vectors of a finite
labeled multigraph represent its graphic matroid. Loops give zero columns;
parallel edges remain separate indices. -/
theorem incidence_vectorMatroid_eq_graphic (hE : G.edgeSet.Finite)
    (ends : G.EdgeIndex → α × α) (hends : G.IsEdgeOrientation ends) :
    Matroid.vectorMatroid (K := ℝ) G.edgeSet hE (G.incidenceColumn ends) =
      Matroid.graphic G hE := by
  apply Matroid.ext_indep (by simp)
  intro I hI
  change I ⊆ G.edgeSet at hI
  rw [Matroid.vectorMatroid_indep_iff, Matroid.graphic_indep_iff]
  simp only [hI, true_and]
  rw [G.linearIndependent_incidence_iff_linearIndepOn ends I hI]
  change LinearIndepOn ℝ (fun e : G.EdgeIndex => G.incidenceColumn ends e.1)
      (G.edgeEmbedding ⁻¹' I) ↔ ¬ G.HasEdgeCycle (G.edgeEmbedding ⁻¹' I)
  constructor
  · intro hli hcycle
    exact (G.not_linearIndepOn_incidence_of_cycle ends hends hcycle) hli
  · intro hforest
    exact G.linearIndepOn_incidence_of_forest hE ends hends _ hforest

/-- The signed incidence family represents the existing graphic matroid
over the reals, as used in the manuscript's connectivity example (N258). -/
theorem incidence_represents_graphic (hE : G.edgeSet.Finite)
    (ends : G.EdgeIndex → α × α) (hends : G.IsEdgeOrientation ends) :
    Matroid.Represents (K := ℝ) (Matroid.graphic G hE) (G.incidenceColumn ends) := by
  rw [← G.incidence_vectorMatroid_eq_graphic hE ends hends]
  exact Matroid.vectorMatroid_represents G.edgeSet hE (G.incidenceColumn ends)

/-- Reversing or otherwise changing edge orientations does not change the
represented matroid (N258). -/
theorem incidence_vectorMatroid_orientation_independent (hE : G.edgeSet.Finite)
    (ends ends' : G.EdgeIndex → α × α)
    (hends : G.IsEdgeOrientation ends) (hends' : G.IsEdgeOrientation ends') :
    Matroid.vectorMatroid (K := ℝ) G.edgeSet hE (G.incidenceColumn ends) =
      Matroid.vectorMatroid (K := ℝ) G.edgeSet hE (G.incidenceColumn ends') := by
  rw [G.incidence_vectorMatroid_eq_graphic hE ends hends,
    G.incidence_vectorMatroid_eq_graphic hE ends' hends']
end Graph
