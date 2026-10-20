import Matroid.Cycles
import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Combinatorics.Matroid.Closure

/-! # ThreeSum -/

open Set

namespace Matroid

/-- The cycle family specified for the manuscript's proper three-sum.
The input cycles agree on the common triangle, so that their symmetric
difference contains no triangle element. This predicate does not assert
that the family is the cycle family of a matroid. -/
def ThreeSumCycle {α : Type*} (M N : Matroid α)
    (T X : Set α) : Prop :=
  ∃ C D : Set α, M.IsCircuitUnion C ∧ N.IsCircuitUnion D ∧
    C ∩ T = D ∩ T ∧ X = symmDiff C D

/-- The exact properness and cycle specification in the manuscript's
three-sum case. Existence of a matroid satisfying it remains N066's
substantive open obligation. -/
def IsProperThreeSum {α : Type*} (M N P : Matroid α)
    (T : Set α) : Prop :=
  M.E ∩ N.E = T ∧ T.ncard = 3 ∧
  M.IsCircuit T ∧ N.IsCircuit T ∧
  (∀ K : Set α, M.IsCocircuit K → ¬ K ⊆ T) ∧
  (∀ K : Set α, N.IsCocircuit K → ¬ K ⊆ T) ∧
  7 ≤ M.E.ncard ∧ 7 ≤ N.E.ncard ∧
  P.E = symmDiff M.E N.E ∧
  ∀ X : Set α, P.IsCircuitUnion X ↔ ThreeSumCycle M N T X

/-- Every selected subset of the common triangle yields an element of the
paired-column span used by the binary quotient candidate. -/
theorem triangle_pair_sum_mem_span {α V W : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (T : Set α) (φM : α → V) (φN : α → W)
    (s : Finset T) :
    (∑ t ∈ s, (φM t.1, φN t.1)) ∈
      Submodule.span (ZMod 2)
        (Set.range (fun t : T => (φM t.1, φN t.1))) := by
  apply Submodule.sum_mem
  intro t ht
  apply Submodule.subset_span
  exact ⟨t, rfl⟩

/-- Over `F₂`, every member of the finite paired-triangle span is a sum
of a subset of its indexed generators. This is the finite kernel step
needed to recover a matching triangle trace from the quotient. -/
theorem triangle_pair_mem_span_iff_exists_subset_sum {α V W : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (T : Set α) [Fintype T] (φM : α → V) (φN : α → W)
    (z : V × W) :
    z ∈ Submodule.span (ZMod 2)
      (Set.range (fun t : T => (φM t.1, φN t.1))) ↔
      ∃ s : Finset T, z = ∑ t ∈ s, (φM t.1, φN t.1) := by
  classical
  let v : T → V × W := fun t => (φM t.1, φN t.1)
  constructor
  · intro hz
    obtain ⟨c, hc⟩ :=
      (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hz
    let s : Finset T := Finset.univ.filter (fun t => c t = 1)
    refine ⟨s, ?_⟩
    rw [← hc]
    simp only [s, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hct : c t = 1
    · simp [hct]
    · have hz : c t = 0 := by
        have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
        exact (h01 (c t)).resolve_right hct
      simp [hz]
  · rintro ⟨s, rfl⟩
    exact triangle_pair_sum_mem_span T φM φN s

theorem threeSumCycle_empty {α : Type*} (M N : Matroid α) (T : Set α) :
    ThreeSumCycle M N T ∅ := by
  refine ⟨∅, ∅, ?_, ?_, ?_, ?_⟩
  · exact ⟨∅, by simp, by simp, by simp⟩
  · exact ⟨∅, by simp, by simp, by simp⟩
  · rfl
  · simp

/-- Matching traces on the entire common triangle ensure that proposed
three-sum cycles lie on the symmetric-difference ground set. -/
theorem ThreeSumCycle.subset_symmDiff_ground {α : Type*}
    {M N : Matroid α} {T X : Set α}
    (hX : ThreeSumCycle M N T X)
    (hinter : M.E ∩ N.E = T) : X ⊆ symmDiff M.E N.E := by
  obtain ⟨C, D, hC, hD, htrace, rfl⟩ := hX
  intro x hx
  have hCE := hC.subset_ground
  have hDE := hD.subset_ground
  rcases Set.mem_symmDiff.mp hx with ⟨hxC, hxD⟩ | ⟨hxD, hxC⟩
  · apply Set.mem_symmDiff.mpr
    refine Or.inl ⟨hCE hxC, ?_⟩
    intro hxN
    have hxT : x ∈ T := by
      rw [← hinter]
      exact ⟨hCE hxC, hxN⟩
    have hxDT : x ∈ D ∩ T := htrace ▸ (show x ∈ C ∩ T from ⟨hxC, hxT⟩)
    exact hxD hxDT.1
  · apply Set.mem_symmDiff.mpr
    refine Or.inr ⟨hDE hxD, ?_⟩
    intro hxM
    have hxT : x ∈ T := by
      rw [← hinter]
      exact ⟨hxM, hDE hxD⟩
    have hxCT : x ∈ C ∩ T := htrace.symm ▸ (show x ∈ D ∩ T from ⟨hxD, hxT⟩)
    exact hxC hxCT.1

/-- Binary cycle addition preserves the matching trace condition. -/
theorem ThreeSumCycle.symmDiff {α : Type u}
    {M N : Matroid α} [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    {T X Y : Set α}
    (hX : ThreeSumCycle M N T X) (hY : ThreeSumCycle M N T Y) :
    ThreeSumCycle M N T (_root_.symmDiff X Y) := by
  obtain ⟨C₁, D₁, hC₁, hD₁, hT₁, rfl⟩ := hX
  obtain ⟨C₂, D₂, hC₂, hD₂, hT₂, rfl⟩ := hY
  refine ⟨_root_.symmDiff C₁ C₂, _root_.symmDiff D₁ D₂,
    hM.isCircuitUnion_symmDiff hC₁ hC₂,
    hN.isCircuitUnion_symmDiff hD₁ hD₂, ?_, ?_⟩
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_symmDiff]
    have h₁ := Set.ext_iff.mp hT₁ x
    have h₂ := Set.ext_iff.mp hT₂ x
    simp only [Set.mem_inter_iff] at h₁ h₂
    tauto
  · ext x
    simp only [Set.mem_symmDiff]
    grind

/-- Binary quotient candidate for the three-sum. The quotient identifies
the two copies of each triangle column; proving that its cycles are exactly
`ThreeSumCycle` is the remaining matroid-existence obligation. -/
noncomputable def binaryThreeSumCandidate {α V W : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (M N : Matroid α) [M.Finite] [N.Finite]
    (T : Set α) (φM : α → V) (φN : α → W) : Matroid α := by
  classical
  let U : Submodule (ZMod 2) (V × W) :=
    Submodule.span (ZMod 2) (Set.range
      (fun t : T => (φM t, φN t)))
  exact vectorMatroid (K := ZMod 2) (symmDiff M.E N.E)
    (M.ground_finite.symmDiff N.ground_finite)
    (fun e => Submodule.Quotient.mk (p := U)
      (if e ∈ M.E then φM e else 0, if e ∈ N.E then φN e else 0))

theorem binaryThreeSumCandidate_ground {α V W : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (M N : Matroid α) [M.Finite] [N.Finite]
    (T : Set α) (φM : α → V) (φN : α → W) :
    (binaryThreeSumCandidate M N T φM φN).E = symmDiff M.E N.E := by
  simp [binaryThreeSumCandidate]

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

end Matroid
