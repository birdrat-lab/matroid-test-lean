import Matroid.ClosureConstruction
import Mathlib.Combinatorics.Graph.Connected.EdgeCut
import Mathlib.Combinatorics.Matroid.Map
import Mathlib.Combinatorics.Matroid.Dual
import Mathlib.Combinatorics.Matroid.Circuit

/-! # Matroids from graph edge cuts

For manuscript `def:graphic-cographic` (N061), this module constructs the
graphic matroid on labeled edges. An edge cycle is witnessed by one edge
closing a finite walk through the other selected edges. The proof connects
this walk criterion to graph cuts and derives the matroid through finite
closure exchange. This formulation handles loops and parallel edges.
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

/-- A set spans the cut-closure matroid exactly when it meets every
nonempty graph edge cut. This is the graph side of N062. -/
theorem edgeCutMatroid_spanning_iff (hE : (Graph.edgeSet G).Finite)
    (A : Set {e : β // e ∈ Graph.edgeSet G}) :
    (edgeCutMatroid G hE).Spanning A ↔
      ∀ C, IsLiftedEdgeCut G C → Disjoint A C → C = ∅ := by
  letI : Finite {e : β // e ∈ Graph.edgeSet G} := hE.to_subtype
  have hcl : (edgeCutMatroid G hE).closure A =
      {e | ∀ C, IsLiftedEdgeCut G C → Disjoint A C → e ∉ C} := by
    unfold edgeCutMatroid
    exact Matroid.ofFiniteClosure_closure _ _ A
  rw [Matroid.spanning_iff_closure_eq (by simp), edgeCutMatroid_ground, hcl]
  constructor
  · intro h C hC hAC
    ext e
    constructor
    · intro heC
      have hecl : e ∈ ({e | ∀ D, IsLiftedEdgeCut G D → Disjoint A D → e ∉ D} :
          Set {e : β // e ∈ Graph.edgeSet G}) := by rw [h]; trivial
      exact (hecl C hC hAC heC).elim
    · simp
  · intro h
    apply Set.eq_univ_of_forall
    intro e
    intro C hC hAC heC
    rw [h C hC hAC] at heC
    exact heC.elim

/-- The cocircuits of the cut-closure matroid are exactly inclusion-minimal
nonempty lifted edge cuts. This is the intrinsic cut/bond bridge for N062. -/
theorem edgeCutMatroid_isCocircuit_iff (hE : (Graph.edgeSet G).Finite)
    (X : Set {e : β // e ∈ Graph.edgeSet G}) :
    (edgeCutMatroid G hE).IsCocircuit X ↔
      Minimal (fun C => IsLiftedEdgeCut G C ∧ C.Nonempty) X := by
  let M := edgeCutMatroid G hE
  have hnonspan (Y : Set {e : β // e ∈ Graph.edgeSet G}) :
      ¬ M.Spanning (M.E \ Y) ↔
        ∃ C, IsLiftedEdgeCut G C ∧ C.Nonempty ∧ C ⊆ Y := by
    have hground : M.E = univ := G.edgeCutMatroid_ground hE
    rw [hground, G.edgeCutMatroid_spanning_iff hE]
    constructor
    · intro hn
      by_contra hnone
      apply hn
      intro C hC hdisj
      by_contra hne
      apply hnone
      refine ⟨C, hC, Set.nonempty_iff_ne_empty.mpr hne, ?_⟩
      intro e heC
      by_contra heY
      exact (Set.disjoint_left.mp hdisj) ⟨trivial, heY⟩ heC
    · rintro ⟨C, hC, hne, hCY⟩ hspan
      have hzero := hspan C hC (Set.disjoint_left.mpr (by
        intro e hecomp heC
        exact hecomp.2 (hCY heC)))
      obtain ⟨e, he⟩ := hne
      rw [hzero] at he
      exact he.elim
  rw [Matroid.isCocircuit_iff_minimal_compl_nonspanning]
  change Minimal (fun Y : Set {e : β // e ∈ Graph.edgeSet G} =>
    ¬ M.Spanning (M.E \ Y)) X ↔ _
  simp_rw [hnonspan]
  constructor
  · intro hmin
    obtain ⟨C, hC, hne, hCX⟩ := hmin.prop
    have hCXeq : C = X := (hmin.eq_of_superset ⟨C, hC, hne, Subset.rfl⟩ hCX).symm
    subst X
    refine ⟨⟨hC, hne⟩, ?_⟩
    intro Y hY hYC
    exact (hmin.eq_of_superset ⟨Y, hY.1, hY.2, Subset.rfl⟩ hYC).subset
  · intro hmin
    refine ⟨⟨X, hmin.prop.1, hmin.prop.2, Subset.rfl⟩, ?_⟩
    intro Y hY hYX
    obtain ⟨C, hC, hne, hCY⟩ := hY
    have hCX : C ⊆ X := hCY.trans hYX
    have hCXeq : X = C := hmin.eq_of_superset ⟨hC, hne⟩ hCX
    exact hCXeq.subset.trans hCY

end Graph

namespace Graph

open Set

variable {α β : Type*} (G : Graph α β)

/-- Independent edge sets admit an isolating graph cut for each selected edge.
The walk/cycle comparison below identifies this bridge criterion with forests. -/
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

namespace Graph

variable {α β : Type*} (G : Graph α β)

abbrev EdgeIndex := {e : β // e ∈ Graph.edgeSet G}

def LinkedOn (A : Set (EdgeIndex G)) (u v : α) : Prop :=
  ∃ e : EdgeIndex G, e ∈ A ∧ G.IsLink (e : β) u v

def ReachableOn (A : Set (EdgeIndex G)) (u v : α) : Prop :=
  Relation.ReflTransGen (LinkedOn G A) u v

private theorem linkedOn_symm {A : Set (EdgeIndex G)} {u v : α}
    (h : LinkedOn G A u v) : LinkedOn G A v u := by
  obtain ⟨e, heA, he⟩ := h
  exact ⟨e, heA, he.symm⟩

private theorem reachableOn_symm {A : Set (EdgeIndex G)} {u v : α}
    (h : ReachableOn G A u v) : ReachableOn G A v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hlink ih => exact (Relation.ReflTransGen.single (linkedOn_symm G hlink)).trans ih

private theorem linkedOn_same_side {A : Set (EdgeIndex G)} {S : Set α}
    (hNoCut : ∀ e ∈ A, (e : β) ∉ G.edgeCut S) {u v : α}
    (h : LinkedOn G A u v) : u ∈ S ↔ v ∈ S := by
  obtain ⟨e, heA, he⟩ := h
  have hnot := hNoCut e heA
  constructor
  · intro hu
    by_contra hv
    exact hnot (he.mem_edgeCut_iff.mpr (Or.inl ⟨hu, hv⟩))
  · intro hv
    by_contra hu
    exact hnot (he.mem_edgeCut_iff.mpr (Or.inr ⟨hv, hu⟩))

private theorem reachableOn_same_side {A : Set (EdgeIndex G)} {S : Set α}
    (hNoCut : ∀ e ∈ A, (e : β) ∉ G.edgeCut S) {u v : α}
    (h : ReachableOn G A u v) : u ∈ S ↔ v ∈ S := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hlink ih => exact ih.trans (linkedOn_same_side G hNoCut hlink)

private theorem reachableSet_noCut {A : Set (EdgeIndex G)} {u : α} :
    ∀ e ∈ A, (e : β) ∉ G.edgeCut {v | ReachableOn G A u v} := by
  intro e heA heCut
  obtain ⟨x, y, hlink, hx, hy⟩ := heCut
  have hxy : LinkedOn G A x y := ⟨e, heA, hlink⟩
  exact hy (hx.tail hxy)

private theorem not_reachable_iff_separating_cut {A : Set (EdgeIndex G)}
    {e : EdgeIndex G} {u v : α} (helink : G.IsLink (e : β) u v) :
    ¬ ReachableOn G A u v ↔
      ∃ S : Set α, (e : β) ∈ G.edgeCut S ∧
        ∀ f ∈ A, (f : β) ∉ G.edgeCut S := by
  constructor
  · intro hn
    let S : Set α := {w | ReachableOn G A u w}
    have hu : u ∈ S := Relation.ReflTransGen.refl
    have hv : v ∉ S := hn
    refine ⟨S, ?_, reachableSet_noCut G⟩
    exact helink.mem_edgeCut_iff.mpr (Or.inl ⟨hu, hv⟩)
  · rintro ⟨S, heCut, hNoCut⟩ hreach
    have hside := reachableOn_same_side G hNoCut hreach
    rcases helink.mem_edgeCut_iff.mp heCut with h | h
    · exact h.2 (hside.mp h.1)
    · exact h.2 (hside.mpr h.1)

/-- An edge closes a finite walk through the other selected edges. This is
equivalent to the usual graph-cycle condition: a simple cycle gives such a
walk after removing one edge, and a walk can be shortened to a simple path.
The definition includes loops and parallel-edge cycles. -/
def HasEdgeCycle (A : Set (EdgeIndex G)) : Prop :=
  ∃ e ∈ A, ∃ u v, G.IsLink (e : β) u v ∧ ReachableOn G (A \ {e}) u v

/-- Graphic independence is exactly absence of an edge closing a walk in the
remaining selected edges. -/
theorem edgeCutMatroid_indep_iff_noEdgeCycle
    (hE : (Graph.edgeSet G).Finite) (A : Set (EdgeIndex G)) :
    (G.edgeCutMatroid hE).Indep A ↔ ¬ G.HasEdgeCycle A := by
  rw [G.edgeCutMatroid_indep_iff]
  constructor
  · intro h hcycle
    obtain ⟨e, heA, u, v, hlink, hreach⟩ := hcycle
    obtain ⟨C, ⟨S, hC⟩, hdisj, heC⟩ := h e heA
    subst C
    have hNoCut : ∀ f ∈ A \ {e}, (f : β) ∉ G.edgeCut S := by
      intro f hfA hfCut
      exact (disjoint_left.mp hdisj) hfA hfCut
    exact ((not_reachable_iff_separating_cut G hlink).mpr ⟨S, heC, hNoCut⟩) hreach
  · intro hn e heA
    obtain ⟨u, v, hlink⟩ := G.exists_isLink_of_mem_edgeSet e.property
    have hnot : ¬ ReachableOn G (A \ {e}) u v := by
      intro hreach
      exact hn ⟨e, heA, u, v, hlink, hreach⟩
    obtain ⟨S, heCut, hNoCut⟩ := (not_reachable_iff_separating_cut G hlink).mp hnot
    let C : Set (EdgeIndex G) := {f | (f : β) ∈ G.edgeCut S}
    refine ⟨C, ⟨S, rfl⟩, ?_, heCut⟩
    apply disjoint_left.mpr
    intro f hfA hfC
    exact hNoCut f hfA hfC

/-- A graph loop is a one-edge cycle. -/
theorem hasEdgeCycle_of_loop {A : Set (EdgeIndex G)} {e : EdgeIndex G} {u : α}
    (heA : e ∈ A) (hloop : G.IsLink (e : β) u u) : G.HasEdgeCycle A :=
  ⟨e, heA, u, u, hloop, Relation.ReflTransGen.refl⟩

/-- Two distinct parallel edge labels form a two-edge cycle. -/
theorem hasEdgeCycle_of_parallel {A : Set (EdgeIndex G)} {e f : EdgeIndex G}
    {u v : α} (hne : e ≠ f) (heA : e ∈ A) (hfA : f ∈ A)
    (helink : G.IsLink (e : β) u v) (hflink : G.IsLink (f : β) u v) :
    G.HasEdgeCycle A := by
  have hfDiff : f ∈ A \ {e} := ⟨hfA, by simpa using hne.symm⟩
  exact ⟨e, heA, u, v, helink,
    Relation.ReflTransGen.single ⟨f, hfDiff, hflink⟩⟩

end Graph

namespace Graph

variable {α β : Type*} (G : Graph α β)

/-- An edge set contains no graph cycle: no edge closes a walk on the other edges. -/
def IsForestOn (A : Set (EdgeIndex G)) : Prop := ¬ G.HasEdgeCycle A

/-- Include actual edge labels in the ambient edge-label type. -/
def edgeEmbedding : G.EdgeIndex ↪ β := ⟨Subtype.val, Subtype.val_injective⟩

/-- The cycle-free condition on a set of ambient edge labels. -/
def IsForestIn (A : Set β) : Prop := G.IsForestOn (G.edgeEmbedding ⁻¹' A)

end Graph

namespace Matroid

variable {α β : Type*} (G : Graph α β)

private theorem isCircuit_mapEmbedding_iff {γ δ : Type*} (M : Matroid γ)
    (f : γ ↪ δ) (C : Set δ) (hC : C ⊆ f '' M.E) :
    (M.mapEmbedding f).IsCircuit C ↔ M.IsCircuit (f ⁻¹' C) := by
  have hCrange : C ⊆ Set.range f :=
    hC.trans (Set.image_subset_range _ _)
  have himage : f '' (f ⁻¹' C) = C :=
    (Set.image_preimage_eq_iff).2 hCrange
  have hpreE : f ⁻¹' C ⊆ M.E := by
    intro e he
    obtain ⟨x, hx, hxe⟩ := hC he
    exact (f.injective hxe).symm ▸ hx
  have hground : C ⊆ (M.mapEmbedding f).E := by simpa using hC
  rw [Matroid.isCircuit_iff_forall_ssubset,
    Matroid.isCircuit_iff_forall_ssubset]
  constructor
  · rintro ⟨hdep, hproper⟩
    refine ⟨?_, ?_⟩
    · rw [Matroid.dep_iff] at hdep ⊢
      exact ⟨fun hI => hdep.1 ((Matroid.mapEmbedding_indep_iff).2 ⟨hI, hCrange⟩), hpreE⟩
    · intro I hI
      have hIE : I ⊆ M.E := hI.subset.trans hpreE
      have hmap : f '' I ⊂ C := by
        rw [← himage]
        exact (f.injective.injOn.image_ssubset_image_iff
          (Set.subset_univ _) (Set.subset_univ _)).2 hI
      have hmapind := hproper hmap
      simpa [Set.preimage_image_eq _ f.injective] using
        (Matroid.mapEmbedding_indep_iff.mp hmapind).1
  · rintro ⟨hdep, hproper⟩
    refine ⟨?_, ?_⟩
    · rw [Matroid.dep_iff] at hdep ⊢
      exact ⟨fun hI => hdep.1 (Matroid.mapEmbedding_indep_iff.mp hI).1, hground⟩
    · intro D hD
      have hDrange : D ⊆ Set.range f := hD.subset.trans hCrange
      have himageD : f '' (f ⁻¹' D) = D :=
        (Set.image_preimage_eq_iff).2 hDrange
      have hpre : f ⁻¹' D ⊂ f ⁻¹' C := by
        apply (f.injective.injOn.image_ssubset_image_iff
          (Set.subset_univ _) (Set.subset_univ _)).1
        simpa [himageD, himage] using hD
      exact (Matroid.mapEmbedding_indep_iff).2 ⟨hproper hpre, hDrange⟩

/-- Manuscript `def:graphic-cographic` (N061): the graphic matroid on the
actual labeled edge set of a finite graph. -/
noncomputable def graphic (hE : (Graph.edgeSet G).Finite) :
    Matroid β := (G.edgeCutMatroid hE).mapEmbedding G.edgeEmbedding

@[simp] theorem graphic_ground (hE : (Graph.edgeSet G).Finite) :
    (graphic G hE).E = G.edgeSet := by
  rw [graphic, Matroid.mapEmbedding_ground_eq, G.edgeCutMatroid_ground]
  ext e
  simp [Graph.edgeEmbedding]

instance graphic_finite (hE : (Graph.edgeSet G).Finite) :
    (graphic G hE).Finite := by
  unfold graphic
  infer_instance

/-- Independence is exactly the absence of an edge closing a walk in the
remaining selected edges. This detects loops and parallel-edge cycles. -/
theorem graphic_indep_iff (hE : (Graph.edgeSet G).Finite)
    (A : Set β) :
    (graphic G hE).Indep A ↔ A ⊆ G.edgeSet ∧ G.IsForestIn A := by
  rw [graphic, Matroid.mapEmbedding_indep_iff,
    G.edgeCutMatroid_indep_iff_noEdgeCycle]
  change (¬ G.HasEdgeCycle (G.edgeEmbedding ⁻¹' A) ∧
      A ⊆ Set.range G.edgeEmbedding) ↔ _
  constructor
  · rintro ⟨hforest, hA⟩
    refine ⟨?_, hforest⟩
    intro e heA
    obtain ⟨x, -, rfl⟩ := hA heA
    exact x.property
  · rintro ⟨hA, hforest⟩
    refine ⟨hforest, ?_⟩
    intro e heA
    exact ⟨⟨e, hA heA⟩, rfl⟩

/-- Manuscript: `def:graphic-cographic` (N062). The cographic matroid is
the dual of the graphic matroid on the same labeled edge ground set. -/
noncomputable def cographic (hE : (Graph.edgeSet G).Finite) : Matroid β :=
  (graphic G hE)✶

/-- Manuscript ledger N135: the cographic matroid is the dual of the
graphic matroid, as used at `def:graphic-cographic`. -/
theorem cographic_eq_dual_graphic (hE : (Graph.edgeSet G).Finite) :
    cographic G hE = (graphic G hE)✶ :=
  rfl

/-- The abstract cographic construction retains the graph's edge labels. -/
@[simp] theorem cographic_ground (hE : (Graph.edgeSet G).Finite) :
    (cographic G hE).E = G.edgeSet := by
  simp [cographic]

private theorem liftedEdgeCut_iff_isEdgeCut (C : Set β)
    (hC : C ⊆ G.edgeSet) :
    G.IsLiftedEdgeCut (G.edgeEmbedding ⁻¹' C) ↔ G.IsEdgeCut C := by
  have hCrange : C ⊆ Set.range G.edgeEmbedding := by
    intro e he
    exact ⟨⟨e, hC he⟩, rfl⟩
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨S, ?_⟩
    have himage : G.edgeEmbedding '' (G.edgeEmbedding ⁻¹' C) = C :=
      (Set.image_preimage_eq_iff).2 hCrange
    rw [hS] at himage
    have hcutimage : G.edgeCut S =
        G.edgeEmbedding '' {e : G.EdgeIndex | (e : β) ∈ G.edgeCut S} := by
      ext e
      constructor
      · intro he
        exact ⟨⟨e, G.edgeCut_subset_edgeSet he⟩, he, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact hx
    exact hcutimage.trans himage
  · rintro ⟨S, hS⟩
    refine ⟨S, ?_⟩
    rw [← hS]
    rfl

private theorem liftedEdgeCut_nonempty_iff (C : Set β)
    (hC : C ⊆ G.edgeSet) :
    (G.edgeEmbedding ⁻¹' C).Nonempty ↔ C.Nonempty := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e.1, he⟩
  · rintro ⟨e, he⟩
    exact ⟨⟨e, hC he⟩, he⟩

/-- Manuscript `def:graphic-cographic` (N062): on the finite labeled edge
set, cographic circuits are exactly the minimal nonempty edge cuts. -/
theorem cographic_isCircuit_iff_isBond (hE : (Graph.edgeSet G).Finite)
    (C : Set β) : (cographic G hE).IsCircuit C ↔ G.IsBond C := by
  have hdual : (graphic G hE)✶ =
      ((G.edgeCutMatroid hE)✶).mapEmbedding G.edgeEmbedding := by
    simp [graphic, Matroid.mapEmbedding]
  have hBondE (hB : G.IsBond C) : C ⊆ G.edgeSet :=
    hB.isEdgeCut.subset_edgeSet
  have hCircE (hB : (cographic G hE).IsCircuit C) : C ⊆ G.edgeSet := by
    simpa using hB.subset_ground
  constructor
  · intro hB
    have hCE := hCircE hB
    have hCimage : C ⊆ G.edgeEmbedding '' (G.edgeCutMatroid hE)✶.E := by
      simpa [Graph.edgeEmbedding] using hCE
    have hsub : ((G.edgeCutMatroid hE)✶).IsCircuit (G.edgeEmbedding ⁻¹' C) :=
      (isCircuit_mapEmbedding_iff _ _ _ hCimage).1 (by simpa [cographic, hdual] using hB)
    have hmin := (G.edgeCutMatroid_isCocircuit_iff hE _).1 hsub
    have hcut : G.IsEdgeCut C :=
      (liftedEdgeCut_iff_isEdgeCut G C hCE).1 hmin.prop.1
    have hne : C.Nonempty := (liftedEdgeCut_nonempty_iff G C hCE).1 hmin.prop.2
    refine ⟨⟨hcut, hne⟩, ?_⟩
    intro D hD hDC
    have hDE : D ⊆ G.edgeSet := hDC.trans hCE
    have hpreD : G.edgeEmbedding ⁻¹' D ⊆ G.edgeEmbedding ⁻¹' C :=
      Set.preimage_mono hDC
    have hpreCsub := (hmin.eq_of_superset
      ⟨(liftedEdgeCut_iff_isEdgeCut G D hDE).2 hD.1,
        (liftedEdgeCut_nonempty_iff G D hDE).2 hD.2⟩ hpreD).subset
    have hCrange : C ⊆ Set.range G.edgeEmbedding := by
      intro e he; exact ⟨⟨e, hCE he⟩, rfl⟩
    have hDrange : D ⊆ Set.range G.edgeEmbedding := by
      intro e he; exact ⟨⟨e, hDE he⟩, rfl⟩
    have himageC : G.edgeEmbedding '' (G.edgeEmbedding ⁻¹' C) = C :=
      (Set.image_preimage_eq_iff).2 hCrange
    have himageD : G.edgeEmbedding '' (G.edgeEmbedding ⁻¹' D) = D :=
      (Set.image_preimage_eq_iff).2 hDrange
    have himageSub : G.edgeEmbedding '' (G.edgeEmbedding ⁻¹' C) ⊆
        G.edgeEmbedding '' (G.edgeEmbedding ⁻¹' D) := Set.image_mono hpreCsub
    simpa only [himageC, himageD] using himageSub
  · intro hB
    have hCE := hBondE hB
    have hCimage : C ⊆ G.edgeEmbedding '' (G.edgeCutMatroid hE)✶.E := by
      simpa [Graph.edgeEmbedding] using hCE
    have hmin : Minimal
        (fun D => G.IsLiftedEdgeCut D ∧ D.Nonempty)
        (G.edgeEmbedding ⁻¹' C) := by
      refine ⟨⟨(liftedEdgeCut_iff_isEdgeCut G C hCE).2 hB.prop.1,
        (liftedEdgeCut_nonempty_iff G C hCE).2 hB.prop.2⟩, ?_⟩
      intro D hD hDC
      have hDimage : G.edgeEmbedding '' D ⊆ C := by
        have himageC : G.edgeEmbedding '' (G.edgeEmbedding ⁻¹' C) = C :=
          (Set.image_preimage_eq_iff).2 (by
            intro e he; exact ⟨⟨e, hCE he⟩, rfl⟩)
        rw [← himageC]
        exact Set.image_mono hDC
      have hDed : G.edgeEmbedding '' D ⊆ G.edgeSet := by
        rintro e ⟨x, -, rfl⟩
        exact x.property
      have hcutD : G.IsEdgeCut (G.edgeEmbedding '' D) := by
        apply (liftedEdgeCut_iff_isEdgeCut G _ hDed).1
        simpa [Set.preimage_image_eq _ G.edgeEmbedding.injective] using hD.1
      have hneD : (G.edgeEmbedding '' D).Nonempty := hD.2.image _
      have hCsub := hB.eq_of_superset ⟨hcutD, hneD⟩ hDimage
      have hCpre : G.edgeEmbedding ⁻¹' C ⊆ D := by
        rw [hCsub, Set.preimage_image_eq _ G.edgeEmbedding.injective]
      exact hCpre
    have hsub := (G.edgeCutMatroid_isCocircuit_iff hE _).2 hmin
    have hmap := (isCircuit_mapEmbedding_iff _ _ _ hCimage).2 hsub
    simpa [cographic, hdual] using hmap

end Matroid
