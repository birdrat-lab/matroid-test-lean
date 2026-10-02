import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Combinatorics.Matroid.Closure
import Mathlib.Order.Closure

/-! # Finite matroids from closure exchange

Manuscript: `def:matroidal-query-system` (N080). The index type represents
the finite query set; the resulting matroid has ground set `Set.univ`.
-/

open Set

namespace Matroid

variable {α : Type*} (c : ClosureOperator (Set α))

/-- Independence induced by a closure: no member is in the closure of the others. -/
def ClosureIndependent (I : Set α) : Prop := ∀ e ∈ I, e ∉ c (I \ {e})

/-- The Steinitz exchange condition from `def:matroidal-query-system` (N080). -/
def SteinitzExchange : Prop :=
  ∀ (X : Set α) (e f : α), e ∈ c (insert f X) → e ∉ c X → f ∈ c (insert e X)

private theorem indep_empty : ClosureIndependent c ∅ := by
  intro e he
  simp at he

private theorem indep_subset {I J : Set α} (hJ : ClosureIndependent c J) (hIJ : I ⊆ J) :
    ClosureIndependent c I := by
  intro e heI hecl
  exact hJ e (hIJ heI) (c.monotone (sdiff_subset_sdiff hIJ Subset.rfl) hecl)

private theorem indep_insert {I : Set α} {e : α} (hex : SteinitzExchange c)
    (hI : ClosureIndependent c I) (he : e ∉ c I) : ClosureIndependent c (insert e I) := by
  intro x hx hxcl
  by_cases hxe : x = e
  · subst x
    have hnot : e ∉ I := fun heI => he ((c.le_closure I) heI)
    have hdiff : insert e I \ {e} = I := by
      ext y
      simp [hnot]
    exact he (hdiff ▸ hxcl)
  · have hxI : x ∈ I := (mem_insert_iff.mp hx).resolve_left hxe
    have hsub : insert e I \ {x} ⊆ insert e (I \ {x}) := by
      intro y hy
      rcases hy.1 with rfl | hyI
      · simp
      · exact mem_insert_of_mem e ⟨hyI, hy.2⟩
    have hxcl' : x ∈ c (insert e (I \ {x})) := c.monotone hsub hxcl
    have hecl : e ∈ c (insert x (I \ {x})) :=
      hex (I \ {x}) x e hxcl' (hI x hxI)
    have hIeq : insert x (I \ {x}) = I := by
      ext y
      by_cases hy : y = x <;> simp [hy, hxI]
    exact he (hIeq ▸ hecl)

private theorem exists_maximal_indep {α : Type*} [Finite α]
    (c : ClosureOperator (Set α)) (hex : SteinitzExchange c) (X : Set α) :
    ∃ I : Set α, I ⊆ X ∧ ClosureIndependent c I ∧ X ⊆ c I := by
  let P : Set (Set α) := {I | I ⊆ X ∧ ClosureIndependent c I}
  have hfin : P.Finite := Set.toFinite P
  have hne : P.Nonempty := ⟨∅, by simp [P, indep_empty]⟩
  obtain ⟨I, hmax⟩ := hfin.exists_maximal hne
  have hI : I ⊆ X ∧ ClosureIndependent c I := hmax.prop
  refine ⟨I, hI.1, hI.2, ?_⟩
  intro e heX
  by_contra hecl
  have heI : e ∉ I := fun heI => hecl ((c.le_closure I) heI)
  have hP : insert e I ∈ P :=
    ⟨insert_subset heX hI.1, indep_insert c hex hI.2 hecl⟩
  have heq : I = insert e I := (maximal_subset_iff.mp hmax).2 hP (subset_insert e I)
  exact heI (heq ▸ mem_insert e I)

variable {α : Type*} (c : ClosureOperator (Set α))

private def closureBasis (B : Set α) : Prop := ClosureIndependent c B ∧ c B = univ

private theorem indep_insert_iff {I : Set α} {e : α} (hex : SteinitzExchange c)
    (hI : ClosureIndependent c I) (heI : e ∉ I) :
    ClosureIndependent c (insert e I) ↔ e ∉ c I := by
  constructor
  · intro h
    have hs : insert e I \ {e} = I := by ext y; simp [heI]
    intro he
    have hh := h e (mem_insert e I)
    rw [hs] at hh
    exact hh he
  · exact indep_insert c hex hI

private theorem closure_eq_of_subset_subset_closure {I X : Set α}
    (hIX : I ⊆ X) (hXI : X ⊆ c I) : c I = c X := by
  apply subset_antisymm
  · exact c.monotone hIX
  · calc
      c X ⊆ c (c I) := c.monotone hXI
      _ = c I := c.idempotent I

private theorem base_exists [Finite α] (hex : SteinitzExchange c) : ∃ B, closureBasis c B := by
  obtain ⟨B, -, hB, hspan⟩ := exists_maximal_indep c hex univ
  exact ⟨B, hB, eq_univ_of_univ_subset hspan⟩

private theorem base_exchange (hex : SteinitzExchange c) :
    Matroid.ExchangeProperty (closureBasis c) := by
  intro B D hB hD e heBD
  have heB : e ∈ B := heBD.1
  have heD : e ∉ D := heBD.2
  let I := B \ {e}
  have hIB : I ⊆ B := sdiff_subset
  have hI : ClosureIndependent c I := indep_subset c hB.1 hIB
  have heno : e ∉ c I := hB.1 e heB
  have hB_eq : insert e I = B := by
    ext x
    by_cases hx : x = e <;> simp [I, hx, heB]
  have hf_exists : ∃ f ∈ D, f ∉ c I := by
    by_contra hn
    have hDsub : D ⊆ c I := by
      intro f hfD
      by_contra hfnot
      exact hn ⟨f, hfD, hfnot⟩
    have htop : c I = univ := by
      have hs : (univ : Set α) ⊆ c I := by
        rw [← hD.2]
        calc
          c D ⊆ c (c I) := c.monotone hDsub
          _ = c I := c.idempotent I
      exact eq_univ_of_univ_subset hs
    exact heno (htop ▸ mem_univ e)
  obtain ⟨f, hfD, hfnot⟩ := hf_exists
  have hfB : f ∉ B := by
    intro hfB
    by_cases hfe : f = e
    · exact heD (hfe ▸ hfD)
    · exact hfnot ((c.le_closure I) ⟨hfB, by simp [hfe]⟩)
  have hnew : ClosureIndependent c (insert f I) := indep_insert c hex hI hfnot
  have hfclB : f ∈ c (insert e I) := by rw [hB_eq, hB.2]; trivial
  have hecl : e ∈ c (insert f I) := hex I f e hfclB hfnot
  have hBsub : B ⊆ c (insert f I) := by
    rw [← hB_eq]
    exact insert_subset hecl ((subset_insert f I).trans (c.le_closure (insert f I)))
  have hnew_span : c (insert f I) = univ := by
    apply eq_univ_of_univ_subset
    rw [← hB.2]
    calc
      c B ⊆ c (c (insert f I)) := c.monotone hBsub
      _ = c (insert f I) := c.idempotent (insert f I)
  exact ⟨f, ⟨hfD, hfB⟩, ⟨hnew, hnew_span⟩⟩

private theorem exists_indep_extension {α : Type*} [Finite α]
    (c : ClosureOperator (Set α)) (hex : SteinitzExchange c) {I X : Set α}
    (hI : ClosureIndependent c I) (hIX : I ⊆ X) :
    ∃ B : Set α, I ⊆ B ∧ B ⊆ X ∧ ClosureIndependent c B ∧ X ⊆ c B := by
  let P : Set (Set α) := {B | I ⊆ B ∧ B ⊆ X ∧ ClosureIndependent c B}
  have hfin : P.Finite := Set.toFinite P
  have hne : P.Nonempty := ⟨I, Subset.rfl, hIX, hI⟩
  obtain ⟨B, hmax⟩ := hfin.exists_maximal hne
  have hB : I ⊆ B ∧ B ⊆ X ∧ ClosureIndependent c B := hmax.prop
  refine ⟨B, hB.1, hB.2.1, hB.2.2, ?_⟩
  intro e heX
  by_contra hecl
  have heB : e ∉ B := fun heB => hecl ((c.le_closure B) heB)
  have hP : insert e B ∈ P :=
    ⟨hB.1.trans (subset_insert e B), insert_subset heX hB.2.1,
      indep_insert c hex hB.2.2 hecl⟩
  have heq : B = insert e B := (maximal_subset_iff.mp hmax).2 hP (subset_insert e B)
  exact heB (heq ▸ mem_insert e B)

/-- Manuscript `def:matroidal-query-system` (N080). A finite closure operator
satisfying Steinitz exchange determines a matroid on its index type. -/
noncomputable def ofFiniteClosure {α : Type*} [Finite α]
    (c : ClosureOperator (Set α)) (hex : SteinitzExchange c) : Matroid α :=
  Matroid.ofIsBaseOfFinite (E := univ) (Set.finite_univ)
    (closureBasis c) (base_exists c hex) (base_exchange c hex)
    (by intro B hB; exact subset_univ B)

instance ofFiniteClosure_finite {α : Type*} [Finite α]
    (c : ClosureOperator (Set α)) (hex : SteinitzExchange c) :
    (ofFiniteClosure c hex).Finite := by
  unfold ofFiniteClosure
  infer_instance

@[simp] theorem ofFiniteClosure_ground {α : Type*} [Finite α]
    (c : ClosureOperator (Set α)) (hex : SteinitzExchange c) :
    (ofFiniteClosure c hex).E = univ := rfl

/-- Independence is exactly closure independence. -/
theorem ofFiniteClosure_indep_iff {α : Type*} [Finite α]
    (c : ClosureOperator (Set α)) (hex : SteinitzExchange c) (I : Set α) :
    (ofFiniteClosure c hex).Indep I ↔ ClosureIndependent c I := by
  change (∃ B, closureBasis c B ∧ I ⊆ B) ↔ ClosureIndependent c I
  constructor
  · rintro ⟨B, hB, hIB⟩
    exact indep_subset c hB.1 hIB
  · intro hI
    obtain ⟨B, hIB, -, hB, hspan⟩ := exists_indep_extension c hex hI (subset_univ I)
    exact ⟨B, ⟨hB, eq_univ_of_univ_subset hspan⟩, hIB⟩

/-- The constructed matroid recovers the supplied closure, as required by N080. -/
theorem ofFiniteClosure_closure {α : Type*} [Finite α]
    (c : ClosureOperator (Set α)) (hex : SteinitzExchange c) (X : Set α) :
    (ofFiniteClosure c hex).closure X = c X := by
  let M := ofFiniteClosure c hex
  obtain ⟨I, hIX⟩ := M.exists_isBasis X (by change X ⊆ univ; exact subset_univ X)
  have hIc : ClosureIndependent c I := (ofFiniteClosure_indep_iff c hex I).mp hIX.indep
  have hXc : X ⊆ c I := by
    intro e heX
    by_contra hecl
    have hIns : ClosureIndependent c (insert e I) := indep_insert c hex hIc hecl
    have hInsM : M.Indep (insert e I) := (ofFiniteClosure_indep_iff c hex _).mpr hIns
    have heI : e ∈ I := hIX.mem_of_insert_indep heX hInsM
    exact hecl ((c.le_closure I) heI)
  have hcIX : c I = c X := closure_eq_of_subset_subset_closure c hIX.subset hXc
  have hcI : M.closure I = c I := by
    ext e
    rw [hIX.indep.mem_closure_iff']
    change (e ∈ univ ∧ (M.Indep (insert e I) → e ∈ I)) ↔ e ∈ c I
    simp only [mem_univ, true_and]
    by_cases heI : e ∈ I
    · simp [heI, (c.le_closure I) heI]
    · rw [ofFiniteClosure_indep_iff c hex, indep_insert_iff c hex hIc heI]
      simp [heI]
  calc
    M.closure X = M.closure I := hIX.closure_eq_closure.symm
    _ = c I := hcI
    _ = c X := hcIX

end Matroid
