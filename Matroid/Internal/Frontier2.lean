import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Combinatorics.Matroid.Closure
import Mathlib.Combinatorics.Matroid.Constructions
import Mathlib.Combinatorics.Matroid.Loop
import Mathlib.Combinatorics.Matroid.Dual
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Order.Lattice.Nat
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Matroid.Internal.Basic

/-!
# Matroid interfaces from the second dependency frontier

The standard closure, flat, free, loop, coloop, restriction, fundamental-circuit,
and dual-base notions are supplied directly by mathlib. This file contains only
manuscript-facing constructions that are absent from that API.
-/

open Set

namespace Matroid

/-- Manuscript: `def:matroid-cycle` (N063). A finite disjoint union of circuits,
including the empty union, is a cycle in the manuscript's terminology. -/
def IsCircuitUnion {α : Type*} (M : Matroid α) (X : Set α) : Prop :=
  ∃ Cs : Finset (Set α),
    (∀ C ∈ Cs, M.IsCircuit C) ∧
    (∀ C ∈ Cs, ∀ D ∈ Cs, C ≠ D → Disjoint C D) ∧
    X = ⋃₀ (Cs : Set (Set α))

/-- Manuscript: `def:colored-matroid` (N073). The color map is defined exactly
on the ground set; no matroid operation depends on it. -/
structure Colored (α Color : Type*) where
  matroid : Matroid α
  finite : matroid.Finite
  color : matroid.E → Color

/-- Manuscript: `def:matroid-representability` (N042). The elements remain
indexed even when two elements have equal vectors. -/
def Represents {α K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (M : Matroid α) (φ : α → V) : Prop :=
  ∀ I : Set α, I ⊆ M.E →
    (M.Indep I ↔ LinearIndependent K (fun i : I => φ i.1))

/-- Manuscript: `def:matroid-representability` (N042). -/
def RepresentableOver.{u,v,w} {α : Type u} (K : Type v) [Field K]
    (M : Matroid α) : Prop :=
  ∃ (V : Type w) (g : AddCommGroup V) (m : Module K V),
    letI := g
    letI := m
    ∃ φ : α → V, Represents (K := K) M φ

/-- Manuscript: uniform-matroid notation at `prop:grover-source-value` (N129).
The independent sets are exactly the subsets of `E` of size at most `r`. -/
noncomputable def uniformOn {α : Type*} (E : Set α) (hE : E.Finite) (r : ℕ) : Matroid α :=
  (IndepMatroid.ofFinite hE (fun I : Set α => I ⊆ E ∧ I.ncard ≤ r)
    (by simp)
    (by
      intro I J hJ hIJ
      exact ⟨hIJ.trans hJ.1, (Set.ncard_le_ncard hIJ (hE.subset hJ.1)).trans hJ.2⟩)
    (by
      intro I J hI hJ hcard
      obtain ⟨e, heJ, heI⟩ :=
        Set.exists_mem_notMem_of_ncard_lt_ncard hcard (hE.subset hI.1)
      refine ⟨e, heJ, heI, ?_⟩
      refine ⟨insert_subset (hJ.1 heJ) hI.1, ?_⟩
      have hlt : I.ncard < r := lt_of_lt_of_le hcard hJ.2
      rw [Set.ncard_insert_of_notMem heI (hE.subset hI.1)]
      exact Nat.succ_le_of_lt hlt)
    (fun _ hI => hI.1)).matroid

/-- Manuscript: uniform-matroid notation at `prop:grover-source-value` (N129).
This is the manuscript's independent-set characterization of `U_{r,n}`. -/
theorem uniformOn_indep_iff {α : Type*} (E : Set α) (hE : E.Finite)
    (r : ℕ) (I : Set α) : (uniformOn E hE r).Indep I ↔ I ⊆ E ∧ I.ncard ≤ r := by
  rfl

/-- Manuscript: prose before `lem:seymour-three-sum-five` (N158).
A triangle has only the five listed possible closure intersections. The
independence, cospanning, and coindependence conditions on the side set are
unneeded for this particular conclusion. -/
theorem triangle_closure_five_classes {α : Type*} {M : Matroid α}
    {S : Set α} {a b c : α} (hT : M.IsCircuit ({a, b, c} : Set α))
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    M.closure S ∩ ({a, b, c} : Set α) = ∅ ∨
    M.closure S ∩ ({a, b, c} : Set α) = {a} ∨
    M.closure S ∩ ({a, b, c} : Set α) = {b} ∨
    M.closure S ∩ ({a, b, c} : Set α) = {c} ∨
    M.closure S ∩ ({a, b, c} : Set α) = {a, b, c} := by
  classical
  let T : Set α := {a, b, c}
  have third (x : α) (hx : x ∈ T) (hsub : T \ {x} ⊆ M.closure S) :
      x ∈ M.closure S := by
    have hxcl : x ∈ M.closure (T \ {x}) := hT.mem_closure_sdiff_singleton_of_mem hx
    exact M.closure_closure S ▸ (M.closure_subset_closure hsub hxcl)
  have habc : a ∈ M.closure S → b ∈ M.closure S → c ∈ M.closure S := by
    intro ha hb
    apply third c (by simp [T])
    intro x hx
    simp only [T, mem_sdiff, mem_insert_iff, mem_singleton_iff] at hx
    rcases hx.1 with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact (hx.2 rfl).elim
  have hacb : a ∈ M.closure S → c ∈ M.closure S → b ∈ M.closure S := by
    intro ha hc
    apply third b (by simp [T])
    intro x hx
    simp only [T, mem_sdiff, mem_insert_iff, mem_singleton_iff] at hx
    rcases hx.1 with rfl | rfl | rfl
    · exact ha
    · exact (hx.2 rfl).elim
    · exact hc
  have hbca : b ∈ M.closure S → c ∈ M.closure S → a ∈ M.closure S := by
    intro hb hc
    apply third a (by simp [T])
    intro x hx
    simp only [T, mem_sdiff, mem_insert_iff, mem_singleton_iff] at hx
    rcases hx.1 with rfl | rfl | rfl
    · exact (hx.2 rfl).elim
    · exact hb
    · exact hc
  by_cases ha : a ∈ M.closure S <;>
    by_cases hb : b ∈ M.closure S <;>
    by_cases hc : c ∈ M.closure S <;>
    simp_all [Set.inter_insert_of_mem, Set.inter_insert_of_notMem]

/-- Manuscript: port discussion preceding `def:target-query-matroid` and
`prop:minimal-query-circuits` (N081). A minimal set spanning the distinguished
element is exactly the non-target part of a circuit through it. -/
theorem minimal_spanning_iff_circuit {α : Type*} {M : Matroid α}
    {τ : α} {S : Set α} [M.Finite] (hS : S ⊆ M.E) (hτS : τ ∉ S) :
    (τ ∈ M.closure S ∧ ∀ T : Set α, T ⊂ S → τ ∉ M.closure T) ↔
      M.IsCircuit (insert τ S) := by
  constructor
  · rintro ⟨hcl, hmin⟩
    obtain ⟨C, hC, hτC, hCsub⟩ :=
      (M.mem_closure_iff_exists_circuit_sdiff hS hτS).mp hcl
    have hDcl : τ ∈ M.closure (C \ {τ}) :=
      hC.mem_closure_sdiff_singleton_of_mem hτC
    have hDS : C \ {τ} = S := by
      by_contra hne
      exact hmin _ (Set.ssubset_iff_subset_ne.mpr ⟨hCsub, hne⟩) hDcl
    have hCS : C = insert τ S := by
      rw [← hDS, insert_sdiff_singleton, insert_eq_of_mem hτC]
    rwa [← hCS]
  · intro hC
    have hτC : τ ∈ (insert τ S : Set α) := mem_insert τ S
    have hcl : τ ∈ M.closure S := by
      have h := hC.mem_closure_sdiff_singleton_of_mem hτC
      simpa [hτS] using h
    refine ⟨hcl, ?_⟩
    intro T hTS hclT
    have hτT : τ ∉ T := fun h => hτS (hTS.subset h)
    obtain ⟨C, hC', hτC', hDsub⟩ :=
      (M.mem_closure_iff_exists_circuit_sdiff (hTS.subset.trans hS) hτT).mp hclT
    have hCsub : C ⊆ insert τ S := by
      intro x hx
      by_cases hxτ : x = τ
      · exact hxτ ▸ mem_insert τ S
      · exact mem_insert_of_mem τ (hTS.subset (hDsub ⟨hx, by simpa using hxτ⟩))
    have hCeq : C = insert τ S := hC'.eq_of_subset_isCircuit hC hCsub
    have hST : S ⊆ T := by
      intro x hxS
      apply hDsub
      rw [hCeq]
      exact ⟨mem_insert_of_mem τ hxS, by
        intro hxτ
        exact hτS (hxτ ▸ hxS)⟩
    exact hTS.not_subset hST

/-- Manuscript: `def:positive-support` (N105), matroid-side content. The
spanning hypothesis makes the set of candidate cardinalities nonempty. -/
noncomputable def positiveTargetSupport {α : Type*} (M : Matroid α)
    [M.Finite] (τ : α) (A : Set α) (_hA : A ⊆ M.E)
    (_hspan : τ ∈ M.closure A) : ℕ :=
  sInf {n : ℕ | ∃ S : Set α, S ⊆ A ∧ τ ∈ M.closure S ∧ S.ncard = n}

/-- Manuscript: prose before `thm:regular-matroid-energy` (N122).
The product omits the distinguished element even for bases containing it. -/
noncomputable def weightedBasesIn {α R : Type*} [CommSemiring R]
    (M : Matroid α) (hE : M.E.Finite) (τ : α) (w : α → R) : R := by
  classical
  exact ∑ B ∈ hE.toFinset.powerset,
    if M.IsBase (B : Set α) ∧ τ ∈ B then ∏ e ∈ B.erase τ, w e else 0

/-- Manuscript: prose before `thm:regular-matroid-energy` (N122).
This is the target-omitting part of the same finite weighted basis sum. -/
noncomputable def weightedBasesOut {α R : Type*} [CommSemiring R]
    (M : Matroid α) (hE : M.E.Finite) (τ : α) (w : α → R) : R := by
  classical
  exact ∑ B ∈ hE.toFinset.powerset,
    if M.IsBase (B : Set α) ∧ τ ∉ B then ∏ e ∈ B.erase τ, w e else 0

end Matroid
