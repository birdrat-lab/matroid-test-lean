import Matroid.Regular
import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Algebra.Field.ZMod

/-! # Cycles -/

open Set

namespace Matroid

/-- Manuscript: `def:matroid-cycle` (N063). A finite disjoint union of circuits,
including the empty union, is a cycle in the manuscript's terminology. -/
def IsCircuitUnion {α : Type*} (M : Matroid α) (X : Set α) : Prop :=
  ∃ Cs : Finset (Set α),
    (∀ C ∈ Cs, M.IsCircuit C) ∧
    (∀ C ∈ Cs, ∀ D ∈ Cs, C ≠ D → Disjoint C D) ∧
    X = ⋃₀ (Cs : Set (Set α))

/-- Every element of a manuscript cycle lies in the matroid ground set. -/
theorem IsCircuitUnion.subset_ground {α : Type*} {M : Matroid α}
    {X : Set α} (hX : M.IsCircuitUnion X) : X ⊆ M.E := by
  obtain ⟨Cs, hCs, _, rfl⟩ := hX
  intro x hx
  obtain ⟨C, hC, hxC⟩ := Set.mem_sUnion.mp hx
  exact (hCs C (by simpa using hC)).subset_ground hxC

universe u w

/-- Manuscript prose after `def:matroid-cycle` (N256): a regular matroid
has a representation over the binary field. -/
theorem Regular.representableF2 {α : Type u} {M : Matroid α}
    (hM : Regular.{u, 0, w} M) : RepresentableOver.{u, 0, w} (ZMod 2) M :=
  hM (ZMod 2)

private theorem zmod2_eq_one_of_ne_zero (a : ZMod 2) (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact False.elim (ha rfl)
  · rfl

private theorem binary_linearIndependent_iff {ι V : Type*}
    [Finite ι] [AddCommGroup V] [Module (ZMod 2) V]
    (v : ι → V) :
    LinearIndependent (ZMod 2) v ↔
      ∀ s : Finset ι, s.Nonempty → ∑ i ∈ s, v i ≠ 0 := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  constructor
  · intro hli s hs hsum
    let g : ι → ZMod 2 := fun i => if i ∈ s then 1 else 0
    have hsum' : ∑ i, g i • v i = 0 := by
      simpa [g, Finset.sum_ite, Finset.sum_filter] using hsum
    obtain ⟨i, hi⟩ := hs
    have hzero := (Fintype.linearIndependent_iff.mp hli g hsum') i
    simp [g, hi] at hzero
  · intro h
    apply Fintype.linearIndependent_iff.mpr
    intro g hsum i
    by_contra hi
    let s : Finset ι := Finset.univ.filter (fun j => g j ≠ 0)
    have hs : s.Nonempty := ⟨i, by simp [s, hi]⟩
    have hpoint (j : ι) : (if g j ≠ 0 then v j else 0) = g j • v j := by
      by_cases hj : g j = 0
      · simp [hj]
      · simp [zmod2_eq_one_of_ne_zero (g j) hj]
    have hsum' : ∑ j ∈ s, v j = 0 := by
      simpa [s, Finset.sum_filter, hpoint] using hsum
    exact (h s hs) hsum'

private theorem binary_linearIndepOn_iff {α V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    (v : α → V) (X : Set α) (hX : X.Finite) :
    LinearIndepOn (ZMod 2) v X ↔
      ∀ s : Finset α, (s : Set α) ⊆ X → s.Nonempty → ∑ i ∈ s, v i ≠ 0 := by
  classical
  letI : Fintype X := hX.fintype
  constructor
  · intro hli s hs hne
    have hli_s : LinearIndependent (ZMod 2) (fun i : (s : Set α) => v i.1) :=
      hli.mono hs
    letI : Fintype (s : Set α) := Finset.Subtype.fintype s
    have hne' : (Finset.univ : Finset (s : Set α)).Nonempty := by
      obtain ⟨i, hi⟩ := hne
      exact ⟨⟨i, hi⟩, Finset.mem_univ _⟩
    have hz := (binary_linearIndependent_iff (fun i : (s : Set α) => v i.1)).1
      hli_s Finset.univ hne'
    rw [← Finset.sum_coe_sort s v]
    exact hz
  · intro h
    apply (binary_linearIndependent_iff (fun i : X => v i.1)).2
    intro s hne
    let t : Finset α := s.image Subtype.val
    have htX : (t : Set α) ⊆ X := by
      intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
      exact j.property
    have htne : t.Nonempty := by
      obtain ⟨j, hj⟩ := hne
      exact ⟨j.1, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
    have ht := h t htX htne
    simpa only [t, Finset.sum_image Subtype.val_injective.injOn] using ht

private theorem binary_circuit_sum_eq_zero {α V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    {M : Matroid α} (φ : α → V) (hRep : M.Represents (K := ZMod 2) φ)
    {C : Set α} (hC : M.IsCircuit C) [M.Finite] :
    ∑ i ∈ (M.ground_finite.subset hC.subset_ground).toFinset, φ i = 0 := by
  classical
  let hfin : C.Finite := M.ground_finite.subset hC.subset_ground
  have hnotLI : ¬ LinearIndepOn (ZMod 2) φ C := by
    intro hli
    exact hC.not_indep ((hRep C hC.subset_ground).2 hli)
  rw [binary_linearIndepOn_iff φ C hfin] at hnotLI
  push Not at hnotLI
  obtain ⟨s, hsC, hsne, hsum⟩ := hnotLI
  have hnotLI_s : ¬ LinearIndepOn (ZMod 2) φ (s : Set α) := by
    intro hli
    exact ((binary_linearIndepOn_iff φ (s : Set α) s.finite_toSet).1
      hli s Set.Subset.rfl hsne) hsum
  have hnotIndep : ¬ M.Indep (s : Set α) := by
    intro hi
    exact hnotLI_s ((hRep (s : Set α) (hsC.trans hC.subset_ground)).1 hi)
  have hsEq : (s : Set α) = C := hC.eq_of_not_indep_subset hnotIndep hsC
  have hsfin : s = hfin.toFinset := by
    ext i
    simpa only [Set.Finite.mem_toFinset, Finset.mem_coe] using (Set.ext_iff.mp hsEq i)
  simpa only [hsfin] using hsum

private theorem circuitUnion_union_circuit {α : Type*} {M : Matroid α}
    {C Y : Set α} (hC : M.IsCircuit C) (hY : M.IsCircuitUnion Y)
    (hdisj : Disjoint C Y) : M.IsCircuitUnion (C ∪ Y) := by
  classical
  obtain ⟨Cs, hCs, hpair, rfl⟩ := hY
  refine ⟨insert C Cs, ?_, ?_, ?_⟩
  · intro D hD
    rcases Finset.mem_insert.mp hD with rfl | hD
    · exact hC
    · exact hCs D hD
  · intro D hD F hF hne
    rcases Finset.mem_insert.mp hD with rfl | hDC
    · rcases Finset.mem_insert.mp hF with rfl | hFC
      · exact False.elim (hne rfl)
      · apply hdisj.mono_right
        intro x hx
        exact Set.mem_sUnion.mpr ⟨F, hFC, hx⟩
    · rcases Finset.mem_insert.mp hF with rfl | hFC
      · apply (hdisj.mono_right ?_).symm
        intro x hx
        exact Set.mem_sUnion.mpr ⟨D, hDC, hx⟩
      · exact hpair D hDC F hFC hne
  · ext x
    simp [Set.mem_sUnion]

private theorem binary_zero_sum_isCircuitUnion {α V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    {M : Matroid α} (φ : α → V) (hRep : M.Represents (K := ZMod 2) φ)
    [M.Finite] (s : Finset α) (hsE : (s : Set α) ⊆ M.E)
    (hsum : ∑ i ∈ s, φ i = 0) : M.IsCircuitUnion (s : Set α) := by
  classical
  revert hsE hsum
  refine Finset.strongInductionOn s ?_
  intro s ih hsE hsum
  by_cases hsempty : s = ∅
  · subst s
    refine ⟨∅, ?_, ?_, ?_⟩ <;> simp
  have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hsempty
  have hnotLI : ¬ LinearIndepOn (ZMod 2) φ (s : Set α) := by
    intro hli
    exact ((binary_linearIndepOn_iff φ (s : Set α) s.finite_toSet).1
      hli s Set.Subset.rfl hsne) hsum
  have hdep : M.Dep (s : Set α) :=
    (Matroid.not_indep_iff hsE).1 (fun hi => hnotLI ((hRep (s : Set α) hsE).1 hi))
  obtain ⟨C, hCs, hC⟩ := hdep.exists_isCircuit_subset
  let hcfin : C.Finite := M.ground_finite.subset hC.subset_ground
  let c : Finset α := hcfin.toFinset
  have hcSub : c ⊆ s := by
    intro i hi
    exact hCs (by simpa [c] using hi)
  have hcne : c.Nonempty := by
    obtain ⟨i, hi⟩ := hC.nonempty
    exact ⟨i, by simpa [c] using hi⟩
  have hcsum : ∑ i ∈ c, φ i = 0 :=
    binary_circuit_sum_eq_zero φ hRep hC
  have hYsum : ∑ i ∈ s \ c, φ i = 0 := by
    have h := Finset.sum_sdiff (f := φ) hcSub
    simpa [hsum, hcsum] using h
  have hYE : ((s \ c : Finset α) : Set α) ⊆ M.E := by
    intro i hi
    exact hsE (Finset.sdiff_subset hi)
  have hY := ih (s \ c) (Finset.sdiff_ssubset hcSub hcne) hYE hYsum
  have hdisj : Disjoint C ((s \ c : Finset α) : Set α) := by
    apply Set.disjoint_left.mpr
    intro i hiC hiY
    have hic : i ∈ c := by simpa [c] using hiC
    exact (Finset.mem_sdiff.mp hiY).2 hic
  have hcycle := circuitUnion_union_circuit hC hY hdisj
  have hEq : C ∪ ((s \ c : Finset α) : Set α) = (s : Set α) := by
    have hCeq : (c : Set α) = C := by ext i; simp [c]
    rw [← hCeq]
    ext i
    simp only [Set.mem_union, Finset.mem_coe, Finset.mem_sdiff]
    constructor
    · rintro (hi | hi)
      · exact hcSub hi
      · exact hi.1
    · intro hi
      by_cases hic : i ∈ c
      · exact Or.inl hic
      · exact Or.inr ⟨hi, hic⟩
  exact hEq ▸ hcycle

private theorem binary_sum_union_of_disjoint {α V : Type*}
    [AddCommGroup V] (φ : α → V) {X Y : Set α}
    (hX : X.Finite) (hY : Y.Finite) (hdisj : Disjoint X Y)
    (hXsum : ∑ i ∈ hX.toFinset, φ i = 0)
    (hYsum : ∑ i ∈ hY.toFinset, φ i = 0) :
    ∑ i ∈ (hX.union hY).toFinset, φ i = 0 := by
  classical
  rw [hX.toFinset_union hY (hX.union hY)]
  have hdisjFin : Disjoint hX.toFinset hY.toFinset := by
    apply Finset.disjoint_left.mpr
    intro i hiX hiY
    exact Set.disjoint_left.mp hdisj
      (by simpa using hiX) (by simpa using hiY)
  rw [Finset.sum_union hdisjFin, hXsum, hYsum, add_zero]

private theorem binary_circuitUnion_sum_eq_zero {α V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    {M : Matroid α} (φ : α → V) (hRep : M.Represents (K := ZMod 2) φ)
    [M.Finite] {X : Set α} (hX : M.IsCircuitUnion X) :
    ∑ i ∈ (M.ground_finite.subset hX.subset_ground).toFinset, φ i = 0 := by
  classical
  obtain ⟨Cs, hCs, hpair, rfl⟩ := hX
  have aux : ∀ Cs : Finset (Set α),
      (∀ C ∈ Cs, M.IsCircuit C) →
      (∀ C ∈ Cs, ∀ D ∈ Cs, C ≠ D → Disjoint C D) →
      ∀ hU : (⋃₀ (Cs : Set (Set α))).Finite,
        ∑ i ∈ hU.toFinset, φ i = 0 := by
    intro Cs
    induction Cs using Finset.induction_on with
    | empty =>
      intro _ _ hU
      simp
    | @insert C Cs hnot ih =>
      intro hCs hpair hU
      let U : Set α := ⋃₀ (Cs : Set (Set α))
      have hC : M.IsCircuit C := hCs C (Finset.mem_insert_self C Cs)
      have hCs' : ∀ D ∈ Cs, M.IsCircuit D := by
        intro D hD
        exact hCs D (Finset.mem_insert_of_mem hD)
      have hpair' : ∀ D ∈ Cs, ∀ F ∈ Cs, D ≠ F → Disjoint D F := by
        intro D hD F hF hne
        exact hpair D (Finset.mem_insert_of_mem hD) F
          (Finset.mem_insert_of_mem hF) hne
      have hUsub : U ⊆ ⋃₀ ((insert C Cs : Finset (Set α)) : Set (Set α)) := by
        intro x hx
        obtain ⟨D, hD, hxD⟩ := Set.mem_sUnion.mp hx
        exact Set.mem_sUnion.mpr ⟨D, by simpa using Finset.mem_insert_of_mem hD, hxD⟩
      have hUfin : U.Finite := hU.subset hUsub
      have hCfin : C.Finite := M.ground_finite.subset hC.subset_ground
      have hdisj : Disjoint C U := by
        apply Set.disjoint_left.mpr
        intro x hxC hxU
        obtain ⟨D, hD, hxD⟩ := Set.mem_sUnion.mp hxU
        have hDC : D ≠ C := by
          intro h
          exact hnot (h ▸ hD)
        exact Set.disjoint_left.mp (hpair C (Finset.mem_insert_self C Cs) D
          (Finset.mem_insert_of_mem hD) hDC.symm) hxC hxD
      have hCsum : ∑ i ∈ hCfin.toFinset, φ i = 0 :=
        binary_circuit_sum_eq_zero φ hRep hC
      have hUsum : ∑ i ∈ hUfin.toFinset, φ i = 0 :=
        ih hCs' hpair' hUfin
      have hjoin := binary_sum_union_of_disjoint φ hCfin hUfin hdisj hCsum hUsum
      have hset : (⋃₀ ((insert C Cs : Finset (Set α)) : Set (Set α))) = C ∪ U := by
        ext x
        simp [U, Set.mem_sUnion]
      simpa only [hset] using hjoin
  exact aux Cs hCs hpair (M.ground_finite.subset
    (Matroid.IsCircuitUnion.subset_ground ⟨Cs, hCs, hpair, rfl⟩))

private theorem binary_add_self_eq_zero {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] (v : V) : v + v = 0 := by
  have h : (2 : ZMod 2) • v = 0 := by
    have h2 : (2 : ZMod 2) = 0 := by decide
    simp [h2]
  simpa only [two_smul] using h

private theorem binary_sum_symmDiff {α V : Type*}
    [DecidableEq α] [AddCommGroup V] [Module (ZMod 2) V]
    (φ : α → V) (s t : Finset α) :
    ∑ i ∈ symmDiff s t, φ i = (∑ i ∈ s, φ i) + (∑ i ∈ t, φ i) := by
  classical
  have hd : Disjoint (s \ t) (t \ s) := by
    apply Finset.disjoint_left.mpr
    intro i hiA hiB
    exact (Finset.mem_sdiff.mp hiA).2 (Finset.mem_sdiff.mp hiB).1
  rw [Finset.symmDiff_def, Finset.sum_union hd]
  have hs := Finset.sum_inter_add_sum_sdiff s t φ
  have ht' := Finset.sum_inter_add_sum_sdiff t s φ
  rw [Finset.inter_comm t s] at ht'
  calc
    (∑ i ∈ s \ t, φ i) + (∑ i ∈ t \ s, φ i) =
        ((∑ i ∈ s ∩ t, φ i) + (∑ i ∈ s \ t, φ i)) +
          ((∑ i ∈ s ∩ t, φ i) + (∑ i ∈ t \ s, φ i)) := by
      have hzero := binary_add_self_eq_zero (∑ i ∈ s ∩ t, φ i)
      calc
        _ = (∑ i ∈ s \ t, φ i) + (∑ i ∈ t \ s, φ i) +
            ((∑ i ∈ s ∩ t, φ i) + (∑ i ∈ s ∩ t, φ i)) := by
              rw [hzero, add_zero]
        _ = _ := by abel
    _ = (∑ i ∈ s, φ i) + (∑ i ∈ t, φ i) := by rw [hs, ht']

/-- Manuscript prose after `def:matroid-cycle` (N256). In a finite binary
representation, a ground-set subset is a cycle exactly when its indexed
columns sum to zero. -/
theorem isCircuitUnion_iff_binary_sum_eq_zero {α V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    {M : Matroid α} (φ : α → V) (hRep : M.Represents (K := ZMod 2) φ)
    [M.Finite] {X : Set α} (hXE : X ⊆ M.E) :
    M.IsCircuitUnion X ↔
      ∑ i ∈ (M.ground_finite.subset hXE).toFinset, φ i = 0 := by
  classical
  constructor
  · intro hX
    exact binary_circuitUnion_sum_eq_zero φ hRep hX
  · intro hsum
    let hXfin : X.Finite := M.ground_finite.subset hXE
    have hfinE : (hXfin.toFinset : Set α) ⊆ M.E := by
      simpa only [Set.Finite.coe_toFinset] using hXE
    have hcycle := binary_zero_sum_isCircuitUnion φ hRep hXfin.toFinset hfinE hsum
    simpa only [Set.Finite.coe_toFinset] using hcycle

/-- Manuscript prose after `def:matroid-cycle` (N256): cycles of a finite
regular matroid are closed under symmetric difference. -/
theorem Regular.isCircuitUnion_symmDiff {α : Type u} {M : Matroid α}
    [M.Finite] (hM : Regular.{u, 0, w} M)
    {X Y : Set α} (hX : M.IsCircuitUnion X) (hY : M.IsCircuitUnion Y) :
    M.IsCircuitUnion (symmDiff X Y) := by
  classical
  obtain ⟨V, g, m, φ, hRep⟩ := hM.representableF2
  letI : AddCommGroup V := g
  letI : Module (ZMod 2) V := m
  have hXE : X ⊆ M.E := hX.subset_ground
  have hYE : Y ⊆ M.E := hY.subset_ground
  let hXfin : X.Finite := M.ground_finite.subset hXE
  let hYfin : Y.Finite := M.ground_finite.subset hYE
  let hDfin : (symmDiff X Y).Finite := hXfin.symmDiff hYfin
  have hDE : symmDiff X Y ⊆ M.E := by
    intro i hi
    rcases Set.mem_symmDiff.mp hi with ⟨hiX, _⟩ | ⟨hiY, _⟩
    · exact hXE hiX
    · exact hYE hiY
  have hXsum : ∑ i ∈ hXfin.toFinset, φ i = 0 :=
    binary_circuitUnion_sum_eq_zero φ hRep hX
  have hYsum : ∑ i ∈ hYfin.toFinset, φ i = 0 :=
    binary_circuitUnion_sum_eq_zero φ hRep hY
  have hDsum : ∑ i ∈ hDfin.toFinset, φ i = 0 := by
    rw [hXfin.toFinset_symmDiff hYfin hDfin,
      binary_sum_symmDiff φ hXfin.toFinset hYfin.toFinset,
      hXsum, hYsum, add_zero]
  exact (isCircuitUnion_iff_binary_sum_eq_zero φ hRep hDE).2 hDsum

end Matroid
