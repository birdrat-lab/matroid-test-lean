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

/-- The quotient relation in the binary three-sum candidate is exactly a
finite matched triangle correction. This retains all original edge labels
and is the algebraic step in the cycle correspondence. -/
theorem triangle_quotient_sum_eq_zero_iff {α V W : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (E F T : Set α) [Fintype T]
    [DecidablePred (· ∈ E)] [DecidablePred (· ∈ F)]
    (φM : α → V) (φN : α → W) (s : Finset α) :
    let U : Submodule (ZMod 2) (V × W) :=
      Submodule.span (ZMod 2)
        (Set.range (fun t : T => (φM t.1, φN t.1)))
    (∑ e ∈ s, Submodule.Quotient.mk (p := U)
      (if e ∈ E then φM e else 0, if e ∈ F then φN e else 0)) = 0 ↔
      ∃ t : Finset T,
        (∑ e ∈ s.filter (· ∈ E), φM e,
         ∑ e ∈ s.filter (· ∈ F), φN e) =
          ∑ x ∈ t, (φM x.1, φN x.1) := by
  classical
  intro U
  change (∑ e ∈ s, (Submodule.mkQ U)
    (if e ∈ E then φM e else 0,
     if e ∈ F then φN e else 0)) = 0 ↔ _
  rw [← map_sum, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hsum : (∑ e ∈ s,
      (if e ∈ E then φM e else 0,
       if e ∈ F then φN e else 0)) =
      (∑ e ∈ s.filter (· ∈ E), φM e,
       ∑ e ∈ s.filter (· ∈ F), φN e) := by
    induction s using Finset.induction_on with
    | empty => rfl
    | @insert e s he ih =>
        by_cases hE : e ∈ E <;> by_cases hF : e ∈ F <;>
          simp [Finset.sum_insert, he, ih, Finset.filter_insert, hE, hF]
  rw [hsum]
  exact triangle_pair_mem_span_iff_exists_subset_sum T φM φN _

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

/-- On each surviving side, a matched pair's symmetric difference is
the corresponding input cycle with the whole common triangle removed. -/
theorem threeSumCycle_side_restrict {α : Type*}
    {M N : Matroid α} {T C D : Set α}
    (hC : C ⊆ M.E) (hD : D ⊆ N.E)
    (hinter : M.E ∩ N.E = T) (htrace : C ∩ T = D ∩ T) :
    (_root_.symmDiff C D) ∩ M.E = C \ T ∧
      (_root_.symmDiff C D) ∩ N.E = D \ T := by
  constructor <;> ext x
  · have hEF : (x ∈ M.E ∧ x ∈ N.E) ↔ x ∈ T := by
      simpa only [Set.mem_inter_iff] using Set.ext_iff.mp hinter x
    have hCD : (x ∈ C ∧ x ∈ T) ↔ (x ∈ D ∧ x ∈ T) := by
      simpa only [Set.mem_inter_iff] using Set.ext_iff.mp htrace x
    simp only [Set.mem_inter_iff, Set.mem_symmDiff, Set.mem_sdiff]
    have hcE : x ∈ C → x ∈ M.E := fun hx => hC hx
    have hdF : x ∈ D → x ∈ N.E := fun hx => hD hx
    tauto
  · have hEF : (x ∈ M.E ∧ x ∈ N.E) ↔ x ∈ T := by
      simpa only [Set.mem_inter_iff] using Set.ext_iff.mp hinter x
    have hCD : (x ∈ C ∧ x ∈ T) ↔ (x ∈ D ∧ x ∈ T) := by
      simpa only [Set.mem_inter_iff] using Set.ext_iff.mp htrace x
    simp only [Set.mem_inter_iff, Set.mem_symmDiff, Set.mem_sdiff]
    have hcE : x ∈ C → x ∈ M.E := fun hx => hC hx
    have hdF : x ∈ D → x ∈ N.E := fun hx => hD hx
    tauto

/-- A matching pair of factor cycles can be described by a single
triangle trace and its two surviving parts. This is the set-theoretic
normal form needed before applying the binary quotient criterion. -/
theorem threeSumCycle_iff_common_trace {α : Type*}
    {M N : Matroid α} {T X : Set α}
    (hinter : M.E ∩ N.E = T) :
    ThreeSumCycle M N T X ↔
      X ⊆ symmDiff M.E N.E ∧
      ∃ Q : Set α, Q ⊆ T ∧
        M.IsCircuitUnion ((X ∩ M.E) ∪ Q) ∧
        N.IsCircuitUnion ((X ∩ N.E) ∪ Q) := by
  constructor
  · rintro ⟨C, D, hC, hD, htrace, rfl⟩
    have hside := threeSumCycle_side_restrict hC.subset_ground
      hD.subset_ground hinter htrace
    refine ⟨ThreeSumCycle.subset_symmDiff_ground
      ⟨C, D, hC, hD, htrace, rfl⟩ hinter,
      C ∩ T, Set.inter_subset_right, ?_, ?_⟩
    · convert hC using 1
      rw [hside.1]
      ext x
      simp only [Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]
      tauto
    · convert hD using 1
      rw [hside.2, htrace]
      ext x
      simp only [Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]
      tauto
  · rintro ⟨hX, Q, hQT, hC, hD⟩
    refine ⟨(X ∩ M.E) ∪ Q, (X ∩ N.E) ∪ Q,
      hC, hD, ?_, ?_⟩
    · ext x
      have hEF : (x ∈ M.E ∧ x ∈ N.E) ↔ x ∈ T := by
        simpa only [Set.mem_inter_iff] using Set.ext_iff.mp hinter x
      have hX' : x ∈ X → (x ∈ M.E ∧ x ∉ N.E) ∨
          (x ∈ N.E ∧ x ∉ M.E) := by
        intro hx
        exact Set.mem_symmDiff.mp (hX hx)
      have hQ' : x ∈ Q → x ∈ T := fun hx => hQT hx
      simp only [Set.mem_inter_iff, Set.mem_union]
      tauto
    · ext x
      have hEF : (x ∈ M.E ∧ x ∈ N.E) ↔ x ∈ T := by
        simpa only [Set.mem_inter_iff] using Set.ext_iff.mp hinter x
      have hX' : x ∈ X → (x ∈ M.E ∧ x ∉ N.E) ∨
          (x ∈ N.E ∧ x ∉ M.E) := by
        intro hx
        exact Set.mem_symmDiff.mp (hX hx)
      have hQ' : x ∈ Q → x ∈ T := fun hx => hQT hx
      simp only [Set.mem_symmDiff, Set.mem_union, Set.mem_inter_iff]
      tauto

/-- The common trace can be chosen as an actual finite set of triangle
labels. This is the form used by the finite binary-span calculation. -/
theorem threeSumCycle_iff_finite_common_trace {α : Type*}
    {M N : Matroid α} {T X : Set α}
    (hinter : M.E ∩ N.E = T) (hT : T.Finite) :
    ThreeSumCycle M N T X ↔
      X ⊆ symmDiff M.E N.E ∧
      ∃ q : Finset α, (q : Set α) ⊆ T ∧
        M.IsCircuitUnion ((X ∩ M.E) ∪ (q : Set α)) ∧
        N.IsCircuitUnion ((X ∩ N.E) ∪ (q : Set α)) := by
  rw [threeSumCycle_iff_common_trace hinter]
  constructor
  · rintro ⟨hX, Q, hQT, hC, hD⟩
    let hQ : Q.Finite := hT.subset hQT
    refine ⟨hX, hQ.toFinset, ?_, ?_, ?_⟩
    · simpa only [Set.Finite.coe_toFinset] using hQT
    · simpa only [Set.Finite.coe_toFinset] using hC
    · simpa only [Set.Finite.coe_toFinset] using hD
  · rintro ⟨hX, q, hqT, hC, hD⟩
    exact ⟨hX, q, hqT, hC, hD⟩
/-- A binary cycle has the same column sum on a finite retained part as
on the removed triangle trace. -/
theorem binary_sum_sdiff_eq_sum_inter {α V : Type*}
    [DecidableEq α]
    [AddCommGroup V] [Module (ZMod 2) V]
    (φ : α → V) (s t : Finset α)
    (hzero : ∑ e ∈ s, φ e = 0) :
    ∑ e ∈ s \ t, φ e = ∑ e ∈ s ∩ t, φ e := by
  classical
  have hsplit := Finset.sum_inter_add_sum_sdiff s t φ
  rw [hzero] at hsplit
  have hneg : -(∑ e ∈ s ∩ t, φ e) = ∑ e ∈ s ∩ t, φ e := by
    have htwo : (2 : ZMod 2) = 0 := by decide
    have hz : (2 : ZMod 2) • (∑ e ∈ s ∩ t, φ e) = 0 := by simp [htwo]
    exact (neg_eq_iff_add_eq_zero).2 (by simpa only [two_smul] using hz)
  have hsplit' : (∑ e ∈ s \ t, φ e) + (∑ e ∈ s ∩ t, φ e) = 0 := by
    simpa only [add_comm] using hsplit
  exact (eq_neg_of_add_eq_zero_left hsplit').trans hneg

/-- In characteristic two, adjoining a disjoint triangle trace gives a
binary cycle exactly when the retained and trace column sums agree. -/
theorem binary_sum_union_eq_zero_iff {α V : Type*}
    [DecidableEq α] [AddCommGroup V] [Module (ZMod 2) V]
    (φ : α → V) (s t : Finset α) (hdisj : Disjoint s t) :
    (∑ e ∈ s ∪ t, φ e = 0) ↔
      (∑ e ∈ s, φ e) = ∑ e ∈ t, φ e := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  have hneg : -(∑ e ∈ t, φ e) = ∑ e ∈ t, φ e := by
    have hz : (2 : ZMod 2) • (∑ e ∈ t, φ e) = 0 := by simp [htwo]
    exact (neg_eq_iff_add_eq_zero).2 (by simpa only [two_smul] using hz)
  rw [Finset.sum_union hdisj, add_eq_zero_iff_eq_neg, hneg]

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
