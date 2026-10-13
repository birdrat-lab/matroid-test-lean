import Matroid.Cycles

/-! # Cycles proposed by the proper two-sum construction

These are the matching-port cycle pairs in `def:regular-matroid-sums`.
The matroid-existence part of that definition remains a separate obligation.
-/

namespace Matroid

open Set

universe u w

/-- The manuscript's proposed two-sum cycles, retaining the original ground
labels. Matching membership at the sole shared element removes that element
from the symmetric difference. -/
def TwoSumCycle {α : Type*} (M N : Matroid α) (p : α) (X : Set α) : Prop :=
  ∃ C D : Set α,
    M.IsCircuitUnion C ∧ N.IsCircuitUnion D ∧
      (p ∈ C ↔ p ∈ D) ∧ X = symmDiff C D

theorem twoSumCycle_empty {α : Type*} (M N : Matroid α) (p : α) :
    TwoSumCycle M N p ∅ := by
  refine ⟨∅, ∅, ?_, ?_, ?_, ?_⟩
  · exact ⟨∅, by simp, by simp, by simp⟩
  · exact ⟨∅, by simp, by simp, by simp⟩
  · simp
  · simp

theorem TwoSumCycle.subset_symmDiff_ground {α : Type*}
    {M N : Matroid α} {p : α} {X : Set α}
    (hX : TwoSumCycle M N p X)
    (hinter : M.E ∩ N.E = {p}) : X ⊆ symmDiff M.E N.E := by
  obtain ⟨C, D, hC, hD, hport, rfl⟩ := hX
  intro x hx
  have hCE := hC.subset_ground
  have hDE := hD.subset_ground
  rcases Set.mem_symmDiff.mp hx with ⟨hxC, hxD⟩ | ⟨hxD, hxC⟩
  · apply Set.mem_symmDiff.mpr
    refine Or.inl ⟨hCE hxC, ?_⟩
    intro hxN
    have hxp : x = p := by
      have : x ∈ M.E ∩ N.E := ⟨hCE hxC, hxN⟩
      simpa only [hinter, Set.mem_singleton_iff] using this
    subst x
    exact hxD (hport.mp hxC)
  · apply Set.mem_symmDiff.mpr
    refine Or.inr ⟨hDE hxD, ?_⟩
    intro hxM
    have hxp : x = p := by
      have : x ∈ M.E ∩ N.E := ⟨hxM, hDE hxD⟩
      simpa only [hinter, Set.mem_singleton_iff] using this
    subst x
    exact hxC (hport.mpr hxD)

/-- The proposed cycle family is closed under symmetric difference because
the two regular inputs are binary. This does not by itself establish matroid
existence. -/
theorem TwoSumCycle.symmDiff {α : Type u}
    {M N : Matroid α} [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    {p : α} {X Y : Set α}
    (hX : TwoSumCycle M N p X) (hY : TwoSumCycle M N p Y) :
    TwoSumCycle M N p (symmDiff X Y) := by
  obtain ⟨C₁, D₁, hC₁, hD₁, hp₁, rfl⟩ := hX
  obtain ⟨C₂, D₂, hC₂, hD₂, hp₂, rfl⟩ := hY
  refine ⟨_root_.symmDiff C₁ C₂, _root_.symmDiff D₁ D₂,
    hM.isCircuitUnion_symmDiff hC₁ hC₂,
    hN.isCircuitUnion_symmDiff hD₁ hD₂, ?_, ?_⟩
  · simp only [Set.mem_symmDiff]
    tauto
  · ext x
    simp only [Set.mem_symmDiff]
    grind

/-- Binary fiber-product candidate for the proper two-sum. The shared
column pair is killed in the quotient. At a surviving label, exactly one
component is nonzero when the ground intersection is the port singleton.
The still-open step is proving that its cycles are exactly `TwoSumCycle`. -/
noncomputable def binaryTwoSumCandidate {α V W : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (M N : Matroid α) [M.Finite] [N.Finite]
    (p : α) (φM : α → V) (φN : α → W) : Matroid α := by
  classical
  let U : Submodule (ZMod 2) (V × W) :=
    Submodule.span (ZMod 2) {(φM p, φN p)}
  exact vectorMatroid (K := ZMod 2) (symmDiff M.E N.E)
    (M.ground_finite.symmDiff N.ground_finite)
    (fun e => Submodule.Quotient.mk (p := U)
      (if e ∈ M.E then φM e else 0, if e ∈ N.E then φN e else 0))

theorem binaryTwoSumCandidate_ground {α V W : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (M N : Matroid α) [M.Finite] [N.Finite]
    (p : α) (φM : α → V) (φN : α → W) :
    (binaryTwoSumCandidate M N p φM φN).E = symmDiff M.E N.E := by
  simp [binaryTwoSumCandidate]

private theorem sum_pair_restricted {α V W : Type*}
    [AddCommGroup V] [AddCommGroup W]
    (E F : Set α) [DecidablePred (· ∈ E)] [DecidablePred (· ∈ F)]
    (φ : α → V) (ψ : α → W) (s : Finset α) :
    (∑ e ∈ s, (if e ∈ E then φ e else 0,
                if e ∈ F then ψ e else 0)) =
      (∑ e ∈ s.filter (· ∈ E), φ e,
       ∑ e ∈ s.filter (· ∈ F), ψ e) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert e s he ih =>
    by_cases hE : e ∈ E <;> by_cases hF : e ∈ F <;>
      simp [Finset.sum_insert, he, ih, Finset.filter_insert, hE, hF]

private theorem quotient_sum_eq_zero_iff {α V W : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (E F : Set α) [DecidablePred (· ∈ E)] [DecidablePred (· ∈ F)]
    (φ : α → V) (ψ : α → W) (p : α) (s : Finset α) :
    let U : Submodule (ZMod 2) (V × W) :=
      Submodule.span (ZMod 2) {(φ p, ψ p)}
    (∑ e ∈ s, Submodule.Quotient.mk (p := U)
      (if e ∈ E then φ e else 0, if e ∈ F then ψ e else 0)) = 0 ↔
    ∃ t : ZMod 2,
      (∑ e ∈ s.filter (· ∈ E), φ e,
       ∑ e ∈ s.filter (· ∈ F), ψ e) = t • (φ p, ψ p) := by
  intro U
  change (∑ e ∈ s, (Submodule.mkQ U)
    (if e ∈ E then φ e else 0,
     if e ∈ F then ψ e else 0)) = 0 ↔ _
  rw [← map_sum]
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rw [sum_pair_restricted E F φ ψ s]
  simpa only [eq_comm] using (Submodule.mem_span_singleton (R := ZMod 2)
    (x := (∑ e ∈ s.filter (· ∈ E), φ e,
           ∑ e ∈ s.filter (· ∈ F), ψ e))
    (y := (φ p, ψ p)))

private theorem cycle_pair_restrict {α : Type*} {E F C D : Set α}
    {p : α} (hE : C ⊆ E) (hF : D ⊆ F)
    (hinter : E ∩ F = {p}) (hport : p ∈ C ↔ p ∈ D) :
    (symmDiff C D) ∩ E = C \ {p} ∧
      (symmDiff C D) ∩ F = D \ {p} := by
  have hboth (x : α) (hxE : x ∈ E) (hxF : x ∈ F) : x = p := by
    have hx : x ∈ E ∩ F := ⟨hxE, hxF⟩
    simpa only [hinter, Set.mem_singleton_iff] using hx
  constructor <;> ext x <;> simp only [Set.mem_inter_iff,
    Set.mem_symmDiff, Set.mem_diff, Set.mem_singleton_iff]
  · constructor
    · rintro ⟨(⟨hxC, hxD⟩ | ⟨hxD, hxC⟩), hxE⟩
      · refine ⟨hxC, ?_⟩
        intro hxp
        subst x
        exact hxD (hport.mp hxC)
      · exact (hxC (by
          have : x = p := hboth x hxE (hF hxD)
          subst x
          exact hport.mpr hxD)).elim
    · rintro ⟨hxC, hxp⟩
      refine ⟨Or.inl ⟨hxC, ?_⟩, hE hxC⟩
      intro hxD
      exact hxp (hboth x (hE hxC) (hF hxD))
  · constructor
    · rintro ⟨(⟨hxC, hxD⟩ | ⟨hxD, hxC⟩), hxF⟩
      · exact (hxD (by
          have : x = p := hboth x (hE hxC) hxF
          subst x
          exact hport.mp hxC)).elim
      · refine ⟨hxD, ?_⟩
        intro hxp
        subst x
        exact hxC (hport.mpr hxD)
    · rintro ⟨hxD, hxp⟩
      refine ⟨Or.inr ⟨hxD, ?_⟩, hF hxD⟩
      intro hxC
      exact hxp (hboth x (hE hxC) (hF hxD))

private theorem binary_sum_erase_port {α V : Type*}
    [DecidableEq α] [AddCommGroup V] [Module (ZMod 2) V]
    (φ : α → V) {C : Set α} (hC : C.Finite) (p : α)
    [Decidable (p ∈ C)]
    (hzero : ∑ e ∈ hC.toFinset, φ e = 0) :
    ∑ e ∈ hC.toFinset.erase p, φ e =
      if p ∈ C then φ p else 0 := by
  classical
  by_cases hp : p ∈ C
  · have hpin : p ∈ hC.toFinset := by simpa using hp
    have hsum := Finset.sum_erase_add hC.toFinset φ hpin
    rw [hzero] at hsum
    have hneg : -φ p = φ p := by
      have htwo : (2 : ZMod 2) • φ p = 0 := by
        have hz : (2 : ZMod 2) = 0 := by decide
        simp [hz]
      have hadd : φ p + φ p = 0 := by simpa only [two_smul] using htwo
      exact (neg_eq_iff_add_eq_zero).2 hadd
    simp only [if_pos hp]
    exact (eq_neg_of_add_eq_zero_left hsum).trans hneg
  · have hpout : p ∉ hC.toFinset := by simpa using hp
    simp [hpout, hp, hzero]

/-- One verified direction of the manuscript's two-sum cycle formula. -/
theorem TwoSumCycle.candidate_isCircuitUnion {α V W : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    {M N : Matroid α} [M.Finite] [N.Finite]
    {p : α} {φM : α → V} {φN : α → W}
    (hφM : M.Represents (K := ZMod 2) φM)
    (hφN : N.Represents (K := ZMod 2) φN)
    (hinter : M.E ∩ N.E = {p})
    {X : Set α} (hX : TwoSumCycle M N p X) :
    (binaryTwoSumCandidate M N p φM φN).IsCircuitUnion X := by
  classical
  obtain ⟨C, D, hC, hD, hport, rfl⟩ := hX
  have hCE := hC.subset_ground
  have hDE := hD.subset_ground
  have hXE : _root_.symmDiff C D ⊆ _root_.symmDiff M.E N.E :=
    (TwoSumCycle.subset_symmDiff_ground
      ⟨C, D, hC, hD, hport, rfl⟩ hinter)
  let E : Set α := _root_.symmDiff M.E N.E
  let hE : E.Finite := M.ground_finite.symmDiff N.ground_finite
  let hXfin : (_root_.symmDiff C D).Finite := hE.subset hXE
  let U : Submodule (ZMod 2) (V × W) :=
    Submodule.span (ZMod 2) {(φM p, φN p)}
  let χ : α → (V × W) ⧸ U := fun e => Submodule.Quotient.mk (p := U)
    (if e ∈ M.E then φM e else 0, if e ∈ N.E then φN e else 0)
  have hrep : (binaryTwoSumCandidate M N p φM φN).Represents (K := ZMod 2) χ := by
    unfold binaryTwoSumCandidate
    exact vectorMatroid_represents E hE χ
  letI : (binaryTwoSumCandidate M N p φM φN).Finite := by
    unfold binaryTwoSumCandidate
    infer_instance
  apply (isCircuitUnion_iff_binary_sum_eq_zero χ hrep
    (by simpa only [binaryTwoSumCandidate_ground] using hXE)).2
  · have hCfin : C.Finite := M.ground_finite.subset hCE
    have hDfin : D.Finite := N.ground_finite.subset hDE
    have hCsum : ∑ e ∈ hCfin.toFinset, φM e = 0 :=
      (isCircuitUnion_iff_binary_sum_eq_zero φM hφM hCE).1 hC
    have hDsum : ∑ e ∈ hDfin.toFinset, φN e = 0 :=
      (isCircuitUnion_iff_binary_sum_eq_zero φN hφN hDE).1 hD
    have hrestrict := cycle_pair_restrict hCE hDE hinter hport
    have hfilterM : hXfin.toFinset.filter (· ∈ M.E) = hCfin.toFinset.erase p := by
      ext e
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_erase]
      have he := Set.ext_iff.mp hrestrict.1 e
      simpa only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_singleton_iff, and_comm] using he
    have hfilterN : hXfin.toFinset.filter (· ∈ N.E) = hDfin.toFinset.erase p := by
      ext e
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_erase]
      have he := Set.ext_iff.mp hrestrict.2 e
      simpa only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_singleton_iff, and_comm] using he
    have hquot := quotient_sum_eq_zero_iff M.E N.E φM φN p hXfin.toFinset
    change (∑ e ∈ hXfin.toFinset, χ e) = 0
    apply hquot.mpr
    refine ⟨if p ∈ C then 1 else 0, ?_⟩
    rw [hfilterM, hfilterN]
    have hCM := binary_sum_erase_port φM hCfin p hCsum
    have hDN := binary_sum_erase_port φN hDfin p hDsum
    rw [hCM, hDN]
    by_cases hp : p ∈ C
    · have hpD := hport.mp hp
      simp [hp, hpD]
    · have hpD : p ∉ D := fun h => hp (hport.mpr h)
      simp [hp, hpD]

/-- The other direction reduces to a binary port coefficient. -/
theorem TwoSumCycle.of_candidate_isCircuitUnion {α V W : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    {M N : Matroid α} [M.Finite] [N.Finite]
    {p : α} {φM : α → V} {φN : α → W}
    (hφM : M.Represents (K := ZMod 2) φM)
    (hφN : N.Represents (K := ZMod 2) φN)
    (hinter : M.E ∩ N.E = {p})
    {X : Set α}
    (hX : (binaryTwoSumCandidate M N p φM φN).IsCircuitUnion X) :
    TwoSumCycle M N p X := by
  classical
  let E : Set α := _root_.symmDiff M.E N.E
  let hE : E.Finite := M.ground_finite.symmDiff N.ground_finite
  have hXE : X ⊆ E := by
    simpa only [E, binaryTwoSumCandidate_ground] using hX.subset_ground
  let hXfin : X.Finite := hE.subset hXE
  let A : Set α := X ∩ M.E
  let B : Set α := X ∩ N.E
  let hAfin : A.Finite := hXfin.subset Set.inter_subset_left
  let hBfin : B.Finite := hXfin.subset Set.inter_subset_left
  have hAground : A ⊆ M.E := Set.inter_subset_right
  have hBground : B ⊆ N.E := Set.inter_subset_right
  have hpBoth : p ∈ M.E ∩ N.E := by rw [hinter]; simp
  have hpM : p ∈ M.E := hpBoth.1
  have hpN : p ∈ N.E := hpBoth.2
  have hpX : p ∉ X := by
    intro hp
    have hpe := hXE hp
    simp [E, Set.mem_symmDiff, hpM, hpN] at hpe
  have hpA : p ∉ A := fun h => hpX h.1
  have hpB : p ∉ B := fun h => hpX h.1
  have hsplit : X = _root_.symmDiff A B := by
    ext x
    have hsingle : x ∈ X → ¬(x ∈ M.E ∧ x ∈ N.E) := by
      intro hx
      have he := hXE hx
      simp only [E, Set.mem_symmDiff] at he
      tauto
    simp only [A, B, Set.mem_symmDiff, Set.mem_inter_iff]
    constructor
    · intro hx
      have he := hXE hx
      simp only [E, Set.mem_symmDiff] at he
      rcases he with ⟨hm, hn⟩ | ⟨hn, hm⟩
      · exact Or.inl ⟨⟨hx, hm⟩, fun h => hn h.2⟩
      · exact Or.inr ⟨⟨hx, hn⟩, fun h => hm h.2⟩
    · rintro (⟨⟨hx, _⟩, _⟩ | ⟨⟨hx, _⟩, _⟩) <;> exact hx
  let U : Submodule (ZMod 2) (V × W) :=
    Submodule.span (ZMod 2) {(φM p, φN p)}
  let χ : α → (V × W) ⧸ U := fun e => Submodule.Quotient.mk (p := U)
    (if e ∈ M.E then φM e else 0, if e ∈ N.E then φN e else 0)
  have hrep : (binaryTwoSumCandidate M N p φM φN).Represents (K := ZMod 2) χ := by
    unfold binaryTwoSumCandidate
    exact vectorMatroid_represents E hE χ
  letI : (binaryTwoSumCandidate M N p φM φN).Finite := by
    unfold binaryTwoSumCandidate
    infer_instance
  have hzero : ∑ e ∈ hXfin.toFinset, χ e = 0 :=
    (isCircuitUnion_iff_binary_sum_eq_zero χ hrep hX.subset_ground).1 hX
  obtain ⟨t, ht⟩ :=
    (quotient_sum_eq_zero_iff M.E N.E φM φN p hXfin.toFinset).mp hzero
  have hfilterM : hXfin.toFinset.filter (· ∈ M.E) = hAfin.toFinset := by
    ext e
    simp [A]
  have hfilterN : hXfin.toFinset.filter (· ∈ N.E) = hBfin.toFinset := by
    ext e
    simp [B]
  rw [hfilterM, hfilterN] at ht
  have hsumM : ∑ e ∈ hAfin.toFinset, φM e = t • φM p := by
    exact congrArg Prod.fst ht
  have hsumN : ∑ e ∈ hBfin.toFinset, φN e = t • φN p := by
    exact congrArg Prod.snd ht
  have ht01 : t = 0 ∨ t = 1 := by
    fin_cases t
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases ht01 with ht0 | ht1
  · rw [ht0, zero_smul] at hsumM hsumN
    refine ⟨A, B, ?_, ?_, by simp [hpA, hpB], hsplit⟩
    · apply (isCircuitUnion_iff_binary_sum_eq_zero φM hφM hAground).2
      change ∑ e ∈ hAfin.toFinset, φM e = 0
      simpa using hsumM
    · apply (isCircuitUnion_iff_binary_sum_eq_zero φN hφN hBground).2
      change ∑ e ∈ hBfin.toFinset, φN e = 0
      simpa using hsumN
  · rw [ht1, one_smul] at hsumM hsumN
    refine ⟨insert p A, insert p B, ?_, ?_, by simp, ?_⟩
    · apply (isCircuitUnion_iff_binary_sum_eq_zero φM hφM
        (Set.insert_subset hpM hAground)).2
      rw [Set.Finite.toFinset_insert, Finset.sum_insert (by simpa using hpA)]
      change φM p + ∑ e ∈ hAfin.toFinset, φM e = 0
      rw [hsumM]
      exact (show φM p + φM p = 0 from by
        have hz : (2 : ZMod 2) = 0 := by decide
        have htwo : (2 : ZMod 2) • φM p = 0 := by simp [hz]
        simpa only [two_smul] using htwo)
    · apply (isCircuitUnion_iff_binary_sum_eq_zero φN hφN
        (Set.insert_subset hpN hBground)).2
      rw [Set.Finite.toFinset_insert, Finset.sum_insert (by simpa using hpB)]
      change φN p + ∑ e ∈ hBfin.toFinset, φN e = 0
      rw [hsumN]
      exact (show φN p + φN p = 0 from by
        have hz : (2 : ZMod 2) = 0 := by decide
        have htwo : (2 : ZMod 2) • φN p = 0 := by simp [hz]
        simpa only [two_smul] using htwo)
    · rw [hsplit]
      ext x
      by_cases hx : x = p
      · subst x
        simp [Set.mem_symmDiff, hpA, hpB]
      · simp [Set.mem_symmDiff, hx]

/-- Matroid existence and the exact cycle formula for finite regular inputs.
The binary quotient is independent of a choice of representation because the
cycle formula characterizes the result on its fixed labeled ground set. -/
theorem exists_twoSum_of_regular {α : Type u}
    {M N : Matroid α} [M.Finite] [N.Finite]
    (hM : Regular.{u,0,w} M) (hN : Regular.{u,0,w} N)
    (p : α) (hinter : M.E ∩ N.E = {p}) :
    ∃ P : Matroid α,
      P.E = _root_.symmDiff M.E N.E ∧
      ∀ X : Set α, P.IsCircuitUnion X ↔ TwoSumCycle M N p X := by
  classical
  obtain ⟨V, gV, mV, φM, hφM⟩ := hM.representableF2
  obtain ⟨W, gW, mW, φN, hφN⟩ := hN.representableF2
  letI : AddCommGroup V := gV
  letI : Module (ZMod 2) V := mV
  letI : AddCommGroup W := gW
  letI : Module (ZMod 2) W := mW
  refine ⟨binaryTwoSumCandidate M N p φM φN,
    binaryTwoSumCandidate_ground M N p φM φN, ?_⟩
  intro X
  exact ⟨TwoSumCycle.of_candidate_isCircuitUnion hφM hφN hinter,
    TwoSumCycle.candidate_isCircuitUnion hφM hφN hinter⟩

/-- The proper labeled two-sum from the manuscript. Its binary construction
works under weaker hypotheses; the properness assumptions here record the
definition's required nonloop, noncoloop, and size conditions. -/
noncomputable def regularTwoSum {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u,0,w} M) (hN : Regular.{u,0,w} N)
    (p : α) (hinter : M.E ∩ N.E = {p})
    (_ : ¬ M.IsLoop p) (_ : ¬ N.IsLoop p)
    (_ : ¬ M.IsColoop p) (_ : ¬ N.IsColoop p)
    (_ : 3 ≤ M.E.ncard) (_ : 3 ≤ N.E.ncard) : Matroid α :=
  Classical.choose (exists_twoSum_of_regular hM hN p hinter)

theorem regularTwoSum_ground {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u,0,w} M) (hN : Regular.{u,0,w} N)
    (p : α) (hinter : M.E ∩ N.E = {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard) :
    (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN).E =
      _root_.symmDiff M.E N.E :=
  (Classical.choose_spec (exists_twoSum_of_regular hM hN p hinter)).1

/-- Exact manuscript cycle characterization on the surviving labels. -/
theorem regularTwoSum_isCircuitUnion_iff {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u,0,w} M) (hN : Regular.{u,0,w} N)
    (p : α) (hinter : M.E ∩ N.E = {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard)
    (X : Set α) :
    (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN).IsCircuitUnion X ↔
      ∃ C D : Set α, M.IsCircuitUnion C ∧ N.IsCircuitUnion D ∧
        X = _root_.symmDiff C D ∧ X ⊆ _root_.symmDiff M.E N.E := by
  constructor
  · intro hX
    obtain ⟨C, D, hC, hD, hp, hEq⟩ :=
      (Classical.choose_spec (exists_twoSum_of_regular hM hN p hinter)).2 X |>.1 hX
    exact ⟨C, D, hC, hD, hEq,
      TwoSumCycle.subset_symmDiff_ground ⟨C, D, hC, hD, hp, hEq⟩ hinter⟩
  · rintro ⟨C, D, hC, hD, hEq, hsub⟩
    have hp : p ∈ C ↔ p ∈ D := by
      have hpBoth : p ∈ M.E ∩ N.E := by rw [hinter]; simp
      have hpNot : p ∉ _root_.symmDiff M.E N.E := by
        simp [Set.mem_symmDiff, hpBoth.1, hpBoth.2]
      have hpX : p ∉ X := fun h => hpNot (hsub h)
      rw [hEq] at hpX
      simp only [Set.mem_symmDiff] at hpX
      tauto
    exact (Classical.choose_spec
      (exists_twoSum_of_regular hM hN p hinter)).2 X |>.2
      ⟨C, D, hC, hD, hp, hEq⟩

end Matroid
