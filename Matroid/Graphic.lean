import Matroid.ClosureConstruction
import Mathlib.Combinatorics.Graph.Connected.EdgeCut

/-! # Matroids from graph edge cuts

For the manuscript graphic-matroid obligation N061, this module constructs the
matroid induced by the graph cut system on labeled edges. The independence
criterion below is a cut-isolation condition for each selected edge. The
comparison with the manuscript's cycle-free forest predicate remains open.
-/

open Set symmDiff

namespace Graph

variable {β : Type*}

private def cutClosure (Cut : Set β → Prop) : ClosureOperator (Set β) where
  toFun A := {e | ∀ C, Cut C → Disjoint A C → e ∉ C}
  monotone' A B hAB e he C hC hBC := he C hC (Disjoint.mono_left hAB hBC)
  le_closure' A e heA C _ hAC heC := (disjoint_left.mp hAC) heA heC
  idempotent' A := by
    apply subset_antisymm
    · intro e he C hC hAC
      apply he C hC
      apply disjoint_left.mpr
      intro x hx hxc
      exact hx C hC hAC hxc
    · intro e he C _ hClC
      exact (disjoint_left.mp hClC) he

private theorem cutClosure_exchange (Cut : Set β → Prop)
    (hxor : ∀ C D, Cut C → Cut D → Cut (C ∆ D)) :
    Matroid.SteinitzExchange (cutClosure Cut) := by
  intro X e f heIncl heNot
  change (∀ C, Cut C → Disjoint (insert f X) C → e ∉ C) at heIncl
  change ¬ (∀ C, Cut C → Disjoint X C → e ∉ C) at heNot
  push Not at heNot
  obtain ⟨C, hC, hXC, heC⟩ := heNot
  have hfC : f ∈ C := by
    by_contra hfC
    have hdisj : Disjoint (insert f X) C := by
      apply disjoint_left.mpr
      intro x hx hxC
      rcases hx with rfl | hxX
      · exact hfC hxC
      · exact (disjoint_left.mp hXC) hxX hxC
    exact heIncl C hC hdisj heC
  change ∀ D, Cut D → Disjoint (insert e X) D → f ∉ D
  intro D hD hXeD hfD
  have hXD : Disjoint X D := disjoint_left.mpr (by
    intro x hxX hxD
    exact (disjoint_left.mp hXeD) (mem_insert_of_mem e hxX) hxD)
  have heD : e ∉ D := fun heD => (disjoint_left.mp hXeD) (mem_insert e X) heD
  have hXxor : Disjoint X (C ∆ D) := by
    apply disjoint_left.mpr
    intro x hxX hxCD
    rcases (mem_symmDiff.mp hxCD) with hx | hx
    · exact (disjoint_left.mp hXC) hxX hx.1
    · exact (disjoint_left.mp hXD) hxX hx.1
  have hfnotxor : f ∉ C ∆ D := by simp [mem_symmDiff, hfC, hfD]
  have hfxor : Disjoint (insert f X) (C ∆ D) := by
    apply disjoint_left.mpr
    intro x hx hxCD
    rcases hx with rfl | hxX
    · exact hfnotxor hxCD
    · exact (disjoint_left.mp hXxor) hxX hxCD
  have hexor : e ∈ C ∆ D := by simp [mem_symmDiff, heC, heD]
  exact heIncl (C ∆ D) (hxor C D hC hD) hfxor hexor

end Graph

namespace Graph

open Set symmDiff

variable {α β : Type*} (G : Graph α β)

/-- A graph edge cut, viewed on the subtype of actual edge labels. -/
def IsLiftedEdgeCut (C : Set {e : β // e ∈ Graph.edgeSet G}) : Prop :=
  ∃ S : Set α, C = {e : {x : β // x ∈ Graph.edgeSet G} | (e : β) ∈ G.edgeCut S}

private theorem isLiftedEdgeCut_symmDiff {C D : Set {e : β // e ∈ Graph.edgeSet G}}
    (hC : IsLiftedEdgeCut G C) (hD : IsLiftedEdgeCut G D) : IsLiftedEdgeCut G (C ∆ D) := by
  obtain ⟨S, rfl⟩ := hC
  obtain ⟨T, rfl⟩ := hD
  refine ⟨S ∆ T, ?_⟩
  ext e
  simp only [Set.mem_symmDiff, Set.mem_ofPred_eq, G.edgeCut_symmDiff]

/-- The matroid constructed from the symmetric-difference-closed family of
edge cuts. Its ground type consists only of actual graph edges. -/
noncomputable def edgeCutMatroid (hE : (Graph.edgeSet G).Finite) :
    Matroid {e : β // e ∈ Graph.edgeSet G} := by
  letI : Finite {e : β // e ∈ Graph.edgeSet G} := hE.to_subtype
  exact Matroid.ofFiniteClosure (cutClosure (IsLiftedEdgeCut G))
    (cutClosure_exchange (IsLiftedEdgeCut G)
      (fun C D hC hD => isLiftedEdgeCut_symmDiff G hC hD))

@[simp] theorem edgeCutMatroid_ground (hE : (Graph.edgeSet G).Finite) :
    (edgeCutMatroid G hE).E = univ := by
  unfold edgeCutMatroid
  simp

instance edgeCutMatroid_finite (hE : (Graph.edgeSet G).Finite) :
    (edgeCutMatroid G hE).Finite := by
  unfold edgeCutMatroid
  infer_instance

end Graph

namespace Graph

open Set

variable {α β : Type*} (G : Graph α β)

/-- Independent edge sets admit an isolating graph cut for each selected edge.
This is the bridge criterion; a multigraph cycle/forest comparison is pending. -/
theorem edgeCutMatroid_indep_iff (hE : (Graph.edgeSet G).Finite)
    (A : Set {e : β // e ∈ Graph.edgeSet G}) :
    (edgeCutMatroid G hE).Indep A ↔
      ∀ e ∈ A, ∃ C, IsLiftedEdgeCut G C ∧ Disjoint (A \ {e}) C ∧ e ∈ C := by
  let _ : Finite {e : β // e ∈ Graph.edgeSet G} := hE.to_subtype
  rw [edgeCutMatroid, Matroid.ofFiniteClosure_indep_iff]
  change (∀ e ∈ A, ¬ ∀ C, IsLiftedEdgeCut G C → Disjoint (A \ {e}) C → e ∉ C) ↔ _
  constructor
  · intro h e he
    have hn := h e he
    push Not at hn
    exact hn
  · intro h e he
    obtain ⟨C, hC, hAC, heC⟩ := h e he
    intro hall
    exact hall C hC hAC heC

end Graph
