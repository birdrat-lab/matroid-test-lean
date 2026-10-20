import Matroid.ThreeSum

/-! The exact binary three-sum cycle family and existence construction. -/

namespace Matroid

private theorem sum_pair {ι V W : Type*}
    [DecidableEq ι] [AddCommMonoid V] [AddCommMonoid W]
    (s : Finset ι) (v : ι → V) (w : ι → W) :
    (∑ t ∈ s, v t, ∑ t ∈ s, w t) = ∑ t ∈ s, (v t, w t) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      simp only [Finset.sum_insert hx]
      have ihV := congrArg Prod.fst ih
      have ihW := congrArg Prod.snd ih
      apply Prod.ext
      · simpa only [Prod.fst_add] using congrArg (fun z : V => v x + z) ihV
      · simpa only [Prod.snd_add] using congrArg (fun z : W => w x + z) ihW

theorem ThreeSumCycle.candidate_isCircuitUnion {α V W : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    {M N : Matroid α} [M.Finite] [N.Finite]
    {T X : Set α} {φM : α → V} {φN : α → W}
    (hφM : M.Represents (K := ZMod 2) φM)
    (hφN : N.Represents (K := ZMod 2) φN)
    (hinter : M.E ∩ N.E = T) (hT : T.Finite)
    (hX : ThreeSumCycle M N T X) :
    (binaryThreeSumCandidate M N T φM φN).IsCircuitUnion X := by
  classical
  letI : Fintype T := hT.fintype
  obtain ⟨hXE, q, hqT, hC, hD⟩ :=
    (threeSumCycle_iff_finite_common_trace hinter hT).mp hX
  let A : Set α := X ∩ M.E
  let B : Set α := X ∩ N.E
  let hXfin : X.Finite :=
    (M.ground_finite.symmDiff N.ground_finite).subset hXE
  let hAfin : A.Finite := hXfin.subset Set.inter_subset_left
  let hBfin : B.Finite := hXfin.subset Set.inter_subset_left
  have hTsubM : T ⊆ M.E := by rw [← hinter]; exact Set.inter_subset_left
  have hTsubN : T ⊆ N.E := by rw [← hinter]; exact Set.inter_subset_right
  have hqM : (q : Set α) ⊆ M.E := hqT.trans hTsubM
  have hqN : (q : Set α) ⊆ N.E := hqT.trans hTsubN
  have hAq : Disjoint hAfin.toFinset q := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxq
    have hxT := hqT (by simpa using hxq)
    have hxAset : x ∈ A := by simpa using hxA
    have hxE := hXE hxAset.1
    rw [← hinter] at hxT
    exact (Set.mem_symmDiff.mp hxE).elim
      (fun h => h.2 hxT.2) (fun h => h.2 hxT.1)
  have hBq : Disjoint hBfin.toFinset q := by
    apply Finset.disjoint_left.mpr
    intro x hxB hxq
    have hxT := hqT (by simpa using hxq)
    have hxBset : x ∈ B := by simpa using hxB
    have hxE := hXE hxBset.1
    rw [← hinter] at hxT
    exact (Set.mem_symmDiff.mp hxE).elim
      (fun h => h.2 hxT.2) (fun h => h.2 hxT.1)
  have hAground : A ∪ (q : Set α) ⊆ M.E :=
    Set.union_subset Set.inter_subset_right hqM
  have hBground : B ∪ (q : Set α) ⊆ N.E :=
    Set.union_subset Set.inter_subset_right hqN
  have hAsum : ∑ e ∈ hAfin.toFinset, φM e = ∑ e ∈ q, φM e := by
    have hz := (isCircuitUnion_iff_binary_sum_eq_zero φM hφM hAground).mp hC
    have hfin : (M.ground_finite.subset hAground).toFinset =
        hAfin.toFinset ∪ q := by ext x; simp [A]
    rw [hfin] at hz
    exact (binary_sum_union_eq_zero_iff φM hAfin.toFinset q hAq).mp hz
  have hBsum : ∑ e ∈ hBfin.toFinset, φN e = ∑ e ∈ q, φN e := by
    have hz := (isCircuitUnion_iff_binary_sum_eq_zero φN hφN hBground).mp hD
    have hfin : (N.ground_finite.subset hBground).toFinset =
        hBfin.toFinset ∪ q := by ext x; simp [B]
    rw [hfin] at hz
    exact (binary_sum_union_eq_zero_iff φN hBfin.toFinset q hBq).mp hz
  let qT : Finset T := q.subtype (· ∈ T)
  have hqmap : qT.image Subtype.val = q := by
    change qT.image (Function.Embedding.subtype (fun x => x ∈ T)) = q
    simpa only [qT, Finset.map_eq_image] using
      (Finset.subtype_map_of_mem (p := fun x => x ∈ T) (s := q)
        (by intro x hx; exact hqT (by simpa using hx)))
  have hqsum : (∑ e ∈ q, φM e, ∑ e ∈ q, φN e) =
      ∑ t ∈ qT, (φM t.1, φN t.1) := by
    simp only [← hqmap, Finset.sum_image Subtype.val_injective.injOn]
    exact sum_pair qT (fun t => φM t.1) (fun t => φN t.1)
  let U : Submodule (ZMod 2) (V × W) :=
    Submodule.span (ZMod 2)
      (Set.range (fun t : T => (φM t.1, φN t.1)))
  let χ : α → (V × W) ⧸ U := fun e => Submodule.Quotient.mk (p := U)
    (if e ∈ M.E then φM e else 0, if e ∈ N.E then φN e else 0)
  have hrep : (binaryThreeSumCandidate M N T φM φN).Represents
      (K := ZMod 2) χ := by
    unfold binaryThreeSumCandidate
    exact vectorMatroid_represents _ _ _
  letI : (binaryThreeSumCandidate M N T φM φN).Finite := by
    unfold binaryThreeSumCandidate
    infer_instance
  apply (isCircuitUnion_iff_binary_sum_eq_zero χ hrep
    (by simpa only [binaryThreeSumCandidate_ground] using hXE)).2
  have hfilterM : hXfin.toFinset.filter (· ∈ M.E) = hAfin.toFinset := by
    ext e; simp [A]
  have hfilterN : hXfin.toFinset.filter (· ∈ N.E) = hBfin.toFinset := by
    ext e; simp [B]
  change (∑ e ∈ hXfin.toFinset, χ e) = 0
  apply (triangle_quotient_sum_eq_zero_iff M.E N.E T φM φN
    hXfin.toFinset).2
  refine ⟨qT, ?_⟩
  rw [hfilterM, hfilterN, hAsum, hBsum]
  exact hqsum

theorem ThreeSumCycle.of_candidate_isCircuitUnion {α V W : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    {M N : Matroid α} [M.Finite] [N.Finite]
    {T X : Set α} {φM : α → V} {φN : α → W}
    (hφM : M.Represents (K := ZMod 2) φM)
    (hφN : N.Represents (K := ZMod 2) φN)
    (hinter : M.E ∩ N.E = T) (hT : T.Finite)
    (hX : (binaryThreeSumCandidate M N T φM φN).IsCircuitUnion X) :
    ThreeSumCycle M N T X := by
  classical
  letI : Fintype T := hT.fintype
  letI : (binaryThreeSumCandidate M N T φM φN).Finite := by
    unfold binaryThreeSumCandidate
    infer_instance
  have hXE : X ⊆ _root_.symmDiff M.E N.E := by
    simpa only [binaryThreeSumCandidate_ground] using hX.subset_ground
  let hXfin : X.Finite :=
    (M.ground_finite.symmDiff N.ground_finite).subset hXE
  let A : Set α := X ∩ M.E
  let B : Set α := X ∩ N.E
  let hAfin : A.Finite := hXfin.subset Set.inter_subset_left
  let hBfin : B.Finite := hXfin.subset Set.inter_subset_left
  let U : Submodule (ZMod 2) (V × W) :=
    Submodule.span (ZMod 2)
      (Set.range (fun t : T => (φM t.1, φN t.1)))
  let χ : α → (V × W) ⧸ U := fun e => Submodule.Quotient.mk (p := U)
    (if e ∈ M.E then φM e else 0, if e ∈ N.E then φN e else 0)
  have hrep : (binaryThreeSumCandidate M N T φM φN).Represents
      (K := ZMod 2) χ := by
    unfold binaryThreeSumCandidate
    exact vectorMatroid_represents _ _ _
  have hzero : ∑ e ∈ hXfin.toFinset, χ e = 0 :=
    (isCircuitUnion_iff_binary_sum_eq_zero χ hrep hX.subset_ground).mp hX
  obtain ⟨qT, hpair⟩ :=
    (triangle_quotient_sum_eq_zero_iff M.E N.E T φM φN
      hXfin.toFinset).mp hzero
  let q : Finset α := qT.image Subtype.val
  have hqT : (q : Set α) ⊆ T := by
    intro x hx
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx
    exact t.property
  have hfilterM : hXfin.toFinset.filter (· ∈ M.E) = hAfin.toFinset := by
    ext e; simp [A]
  have hfilterN : hXfin.toFinset.filter (· ∈ N.E) = hBfin.toFinset := by
    ext e; simp [B]
  have hpairSum : (∑ e ∈ q, φM e, ∑ e ∈ q, φN e) =
      ∑ t ∈ qT, (φM t.1, φN t.1) := by
    simp only [q, Finset.sum_image Subtype.val_injective.injOn]
    exact sum_pair qT (fun t => φM t.1) (fun t => φN t.1)
  have hAsum : ∑ e ∈ hAfin.toFinset, φM e = ∑ e ∈ q, φM e := by
    rw [hfilterM, hfilterN] at hpair
    exact (congrArg Prod.fst (hpair.trans hpairSum.symm))
  have hBsum : ∑ e ∈ hBfin.toFinset, φN e = ∑ e ∈ q, φN e := by
    rw [hfilterM, hfilterN] at hpair
    exact (congrArg Prod.snd (hpair.trans hpairSum.symm))
  have hTsubM : T ⊆ M.E := by rw [← hinter]; exact Set.inter_subset_left
  have hTsubN : T ⊆ N.E := by rw [← hinter]; exact Set.inter_subset_right
  have hqM : (q : Set α) ⊆ M.E := hqT.trans hTsubM
  have hqN : (q : Set α) ⊆ N.E := hqT.trans hTsubN
  have hAq : Disjoint hAfin.toFinset q := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxq
    have hxT := hqT (by simpa using hxq)
    have hxAset : x ∈ A := by simpa using hxA
    have hxE := hXE hxAset.1
    rw [← hinter] at hxT
    exact (Set.mem_symmDiff.mp hxE).elim
      (fun h => h.2 hxT.2) (fun h => h.2 hxT.1)
  have hBq : Disjoint hBfin.toFinset q := by
    apply Finset.disjoint_left.mpr
    intro x hxB hxq
    have hxT := hqT (by simpa using hxq)
    have hxBset : x ∈ B := by simpa using hxB
    have hxE := hXE hxBset.1
    rw [← hinter] at hxT
    exact (Set.mem_symmDiff.mp hxE).elim
      (fun h => h.2 hxT.2) (fun h => h.2 hxT.1)
  have hAground : A ∪ (q : Set α) ⊆ M.E :=
    Set.union_subset Set.inter_subset_right hqM
  have hBground : B ∪ (q : Set α) ⊆ N.E :=
    Set.union_subset Set.inter_subset_right hqN
  have hC : M.IsCircuitUnion (A ∪ (q : Set α)) := by
    apply (isCircuitUnion_iff_binary_sum_eq_zero φM hφM hAground).2
    have hfin : (M.ground_finite.subset hAground).toFinset =
        hAfin.toFinset ∪ q := by ext x; simp [A]
    rw [hfin]
    exact (binary_sum_union_eq_zero_iff φM hAfin.toFinset q hAq).mpr hAsum
  have hD : N.IsCircuitUnion (B ∪ (q : Set α)) := by
    apply (isCircuitUnion_iff_binary_sum_eq_zero φN hφN hBground).2
    have hfin : (N.ground_finite.subset hBground).toFinset =
        hBfin.toFinset ∪ q := by ext x; simp [B]
    rw [hfin]
    exact (binary_sum_union_eq_zero_iff φN hBfin.toFinset q hBq).mpr hBsum
  exact (threeSumCycle_iff_finite_common_trace hinter hT).2
    ⟨hXE, q, hqT, hC, hD⟩

/-- N066: the matching-trace cycles of two finite regular factors across
their proper common triangle are exactly the cycle family of a matroid on
the symmetric-difference ground. -/
theorem exists_properThreeSum {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (T : Set α) (hinter : M.E ∩ N.E = T)
    (hcard : T.ncard = 3)
    (hCM : M.IsCircuit T) (hCN : N.IsCircuit T)
    (hcM : ∀ K : Set α, M.IsCocircuit K → ¬ K ⊆ T)
    (hcN : ∀ K : Set α, N.IsCocircuit K → ¬ K ⊆ T)
    (hnM : 7 ≤ M.E.ncard) (hnN : 7 ≤ N.E.ncard) :
    ∃ P : Matroid α, IsProperThreeSum M N P T := by
  classical
  obtain ⟨V, gV, mV, φM, hφM⟩ := hM.representableF2
  obtain ⟨W, gW, mW, φN, hφN⟩ := hN.representableF2
  letI : AddCommGroup V := gV
  letI : Module (ZMod 2) V := mV
  letI : AddCommGroup W := gW
  letI : Module (ZMod 2) W := mW
  let hT : T.Finite := M.ground_finite.subset (by
    rw [← hinter]
    exact Set.inter_subset_left)
  refine ⟨binaryThreeSumCandidate M N T φM φN,
    hinter, hcard, hCM, hCN, hcM, hcN, hnM, hnN,
    binaryThreeSumCandidate_ground M N T φM φN, ?_⟩
  intro X
  exact ⟨ThreeSumCycle.of_candidate_isCircuitUnion hφM hφN hinter hT,
    ThreeSumCycle.candidate_isCircuitUnion hφM hφN hinter hT⟩

end Matroid
