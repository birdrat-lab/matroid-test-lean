import JordanPick.JordanCurve

/-! # Closed path to Jordan curve bridge

A simple closed path in the product plane factors through the endpoint
quotient of the unit interval. This quotient is homeomorphic to the circle
used by the imported Jordan theorem. -/

namespace JordanPath

open unitInterval

private noncomputable def pathExtend {x : ℝ × ℝ} (p : Path x x) (t : ℝ) : ℝ × ℝ :=
  if h : t ∈ Set.Icc (0 : ℝ) 1 then p ⟨t, h⟩ else x

private theorem pathExtend_zero {x : ℝ × ℝ} (p : Path x x) :
    pathExtend p 0 = x := by
  simp [pathExtend, Path.source]

private theorem pathExtend_one {x : ℝ × ℝ} (p : Path x x) :
    pathExtend p 1 = x := by
  simp [pathExtend, Path.target]

private theorem pathExtend_continuousOn {x : ℝ × ℝ} (p : Path x x) :
    ContinuousOn (pathExtend p) (Set.Icc (0 : ℝ) 1) := by
  have hp : Continuous (fun t : Set.Icc (0 : ℝ) 1 => p t) := p.continuous
  have heq : (Set.Icc (0 : ℝ) 1).domRestrict (pathExtend p) =
      (fun t : Set.Icc (0 : ℝ) 1 => p t) := by
    funext t
    dsimp [Set.domRestrict, pathExtend]
    rw [dite_eq_left t.property]
  exact (continuousOn_iff_continuous_domRestrict).2 (heq ▸ hp)

private noncomputable def pathCircleMap {x : ℝ × ℝ} (p : Path x x) :
    AddCircle (1 : ℝ) → ℝ × ℝ :=
  AddCircle.liftIco 1 0 (pathExtend p)

private theorem pathCircleMap_continuous {x : ℝ × ℝ} (p : Path x x) :
    Continuous (pathCircleMap p) := by
  exact AddCircle.liftIco_zero_continuous
    ((pathExtend_zero p).trans (pathExtend_one p).symm)
    (pathExtend_continuousOn p)

private theorem pathCircleMap_injective {x : ℝ × ℝ} (p : Path x x)
    (h : ∀ s t : I, (s : ℝ) < 1 → (t : ℝ) < 1 → p s = p t → s = t) :
    Function.Injective (pathCircleMap p) := by
  intro a b hab
  let u := (AddCircle.equivIco 1 0) a
  let v := (AddCircle.equivIco 1 0) b
  have hua : (u : AddCircle (1 : ℝ)) = a := AddCircle.coe_equivIco
  have hvb : (v : AddCircle (1 : ℝ)) = b := AddCircle.coe_equivIco
  have hu : (u : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨u.property.1, le_of_lt (by simpa using u.property.2)⟩
  have hv : (v : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨v.property.1, le_of_lt (by simpa using v.property.2)⟩
  have hpEq : p ⟨u, hu⟩ = p ⟨v, hv⟩ := by
    rw [← hua, ← hvb] at hab
    change AddCircle.liftIco 1 0 (pathExtend p) (u : AddCircle (1 : ℝ)) =
      AddCircle.liftIco 1 0 (pathExtend p) (v : AddCircle (1 : ℝ)) at hab
    rw [AddCircle.liftIco_coe_apply u.property,
      AddCircle.liftIco_coe_apply v.property] at hab
    simpa only [pathExtend, dite_eq_left hu, dite_eq_left hv] using hab
  have huv := h ⟨u, hu⟩ ⟨v, hv⟩ (by simpa using u.property.2)
    (by simpa using v.property.2) hpEq
  have huv' : (u : ℝ) = (v : ℝ) := congrArg (fun z : I => (z : ℝ)) huv
  have huv'' : u = v := Subtype.ext huv'
  calc
    a = (u : AddCircle (1 : ℝ)) := hua.symm
    _ = (v : AddCircle (1 : ℝ)) := congrArg (fun z : Set.Ico (0 : ℝ) (0 + 1) =>
      (z : AddCircle (1 : ℝ))) huv''
    _ = b := hvb

private theorem pathCircleMap_range {x : ℝ × ℝ} (p : Path x x) :
    Set.range (pathCircleMap p) = Set.range p := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    let u := (AddCircle.equivIco 1 0) a
    have hua : (u : AddCircle (1 : ℝ)) = a := AddCircle.coe_equivIco
    have hu : (u : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨u.property.1, le_of_lt (by simpa using u.property.2)⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    rw [← hua]
    change p ⟨u, hu⟩ = AddCircle.liftIco 1 0 (pathExtend p) (u : AddCircle (1 : ℝ))
    rw [AddCircle.liftIco_coe_apply u.property]
    simp [pathExtend, hu]
  · rintro ⟨t, rfl⟩
    by_cases ht : (t : ℝ) < 1
    · have htIco : (t : ℝ) ∈ Set.Ico (0 : ℝ) (0 + 1) :=
        ⟨t.property.1, by simpa using ht⟩
      refine ⟨((t : ℝ) : AddCircle (1 : ℝ)), ?_⟩
      change AddCircle.liftIco 1 0 (pathExtend p) ((t : ℝ) : AddCircle (1 : ℝ)) = _
      rw [AddCircle.liftIco_coe_apply htIco]
      simp [pathExtend, t.property]
    · have ht1 : t = 1 := Subtype.ext (le_antisymm t.property.2 (le_of_not_gt ht))
      subst t
      refine ⟨(0 : AddCircle (1 : ℝ)), ?_⟩
      change AddCircle.liftIco 1 0 (pathExtend p)
        ((0 : ℝ) : AddCircle (1 : ℝ)) = p 1
      rw [AddCircle.liftIco_coe_apply (by norm_num :
        (0 : ℝ) ∈ Set.Ico (0 : ℝ) (0 + 1))]
      rw [pathExtend_zero]
      exact (Path.target p).symm

private noncomputable def pathSphereMap {x : ℝ × ℝ} (p : Path x x) :
    Metric.sphere (0 : JordanCurve.Plane) 1 → ℝ × ℝ :=
  pathCircleMap p ∘ (AddCircle.homeomorphCircle
    (by norm_num : (1 : ℝ) ≠ 0)).symm ∘ JordanCurve.Arcs.circleHomeoSphere.symm

private theorem pathSphereMap_continuous {x : ℝ × ℝ} (p : Path x x) :
    Continuous (pathSphereMap p) := by
  exact (pathCircleMap_continuous p).comp
    ((AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).symm.continuous.comp
      JordanCurve.Arcs.circleHomeoSphere.symm.continuous)

private theorem pathSphereMap_injective {x : ℝ × ℝ} (p : Path x x)
    (h : ∀ s t : I, (s : ℝ) < 1 → (t : ℝ) < 1 → p s = p t → s = t) :
    Function.Injective (pathSphereMap p) := by
  exact (pathCircleMap_injective p h).comp
    ((AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).symm.injective.comp
      JordanCurve.Arcs.circleHomeoSphere.symm.injective)

private theorem pathSphereMap_range {x : ℝ × ℝ} (p : Path x x) :
    Set.range (pathSphereMap p) = Set.range p := by
  change Set.range (pathCircleMap p ∘ _ ∘ _) = _
  rw [Set.range_comp, Set.range_comp]
  simp only [EquivLike.range_eq_univ, Set.image_univ]
  exact pathCircleMap_range p

/-- A closed path with no repeated points before its final endpoint has a
continuous injective sphere trace with precisely the same image. This is the
path-level bridge to the imported Jordan curve theorem. -/
theorem exists_jordanTrace {x : ℝ × ℝ} (p : Path x x)
    (h : ∀ s t : I, (s : ℝ) < 1 → (t : ℝ) < 1 → p s = p t → s = t) :
    ∃ r : Metric.sphere (0 : JordanCurve.Plane) 1 → ℝ × ℝ,
      Continuous r ∧ Function.Injective r ∧ Set.range r = Set.range p := by
  exact ⟨pathSphereMap p, pathSphereMap_continuous p,
    pathSphereMap_injective p h, pathSphereMap_range p⟩

/-- Concatenating two injective paths preserves injectivity when their
images meet only at the shared endpoint. This is the path gluing step needed
for a simple graph walk with distinct drawn vertices. -/
theorem trans_injective_of_intersection {X : Type*} [TopologicalSpace X]
    {x y z : X} (p : Path x y) (q : Path y z)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hinter : Set.range p ∩ Set.range q ⊆ {y}) :
    Function.Injective (p.trans q) := by
  intro s t hst
  rw [Path.trans_apply, Path.trans_apply] at hst
  split_ifs at hst with hs ht
  · have hparam := hp hst
    apply Subtype.ext
    have hv := congrArg (fun z : I => (z : ℝ)) hparam
    dsimp at hv
    linarith
  · have hval : p ⟨2 * s, (mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩ =
        q ⟨2 * t - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩ := hst
    have hy : p ⟨2 * s, (mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩ = y := by
      exact Set.mem_singleton_iff.mp (hinter ⟨⟨_, rfl⟩, ⟨_, hval.symm⟩⟩)
    have ha := hp (hy.trans (Path.target p).symm)
    have hb := hq (hval.symm.trans (hy.trans (Path.source q).symm))
    have ha' := congrArg (fun z : I => (z : ℝ)) ha
    have hb' := congrArg (fun z : I => (z : ℝ)) hb
    dsimp at ha' hb'
    exfalso
    have ht' : 1 / 2 < (t : ℝ) := lt_of_not_ge ht
    linarith
  · have ht : (t : ℝ) ≤ 1 / 2 := by assumption
    have hval : q ⟨2 * s - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩ =
        p ⟨2 * t, (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩ := hst
    have hy : p ⟨2 * t, (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩ = y := by
      exact Set.mem_singleton_iff.mp (hinter ⟨⟨_, rfl⟩, ⟨_, hval⟩⟩)
    have ha := hp (hy.trans (Path.target p).symm)
    have hb := hq (hval.trans (hy.trans (Path.source q).symm))
    have ha' := congrArg (fun z : I => (z : ℝ)) ha
    have hb' := congrArg (fun z : I => (z : ℝ)) hb
    dsimp at ha' hb'
    exfalso
    have hs' : 1 / 2 < (s : ℝ) := lt_of_not_ge hs
    linarith
  · have hparam := hq hst
    apply Subtype.ext
    have hv := congrArg (fun z : I => (z : ℝ)) hparam
    dsimp at hv
    linarith

/-- Two injective arcs that meet only at their common endpoints give a
simple closed path after concatenation. -/
theorem trans_simpleClosed_of_two_arcs {X : Type*} [TopologicalSpace X]
    {x y : X} (p : Path x y) (q : Path y x)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hinter : Set.range p ∩ Set.range q ⊆ {x, y}) :
    ∀ s t : I, (s : ℝ) < 1 → (t : ℝ) < 1 →
      p.trans q s = p.trans q t → s = t := by
  intro s t hsone htone hst
  rw [Path.trans_apply, Path.trans_apply] at hst
  split_ifs at hst with hs ht
  · have hparam := hp hst
    apply Subtype.ext
    have hv := congrArg (fun z : I => (z : ℝ)) hparam
    dsimp at hv
    linarith
  · have hval : p ⟨2 * s, (mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩ =
        q ⟨2 * t - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩ := hst
    have hmeet := hinter ⟨⟨_, rfl⟩, ⟨_, hval.symm⟩⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmeet
    rcases hmeet with hx | hy
    · have ha := hp (hx.trans (Path.source p).symm)
      have hb := hq (hval.symm.trans (hx.trans (Path.target q).symm))
      have ha' := congrArg (fun z : I => (z : ℝ)) ha
      have hb' := congrArg (fun z : I => (z : ℝ)) hb
      dsimp at ha' hb'
      exfalso
      linarith
    · have ha := hp (hy.trans (Path.target p).symm)
      have hb := hq (hval.symm.trans (hy.trans (Path.source q).symm))
      have ha' := congrArg (fun z : I => (z : ℝ)) ha
      have hb' := congrArg (fun z : I => (z : ℝ)) hb
      dsimp at ha' hb'
      exfalso
      have ht' : 1 / 2 < (t : ℝ) := lt_of_not_ge ht
      linarith
  · have ht' : (t : ℝ) ≤ 1 / 2 := by assumption
    have hval : q ⟨2 * s - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩ =
        p ⟨2 * t, (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht'⟩⟩ := hst
    have hmeet := hinter ⟨⟨_, rfl⟩, ⟨_, hval⟩⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmeet
    rcases hmeet with hx | hy
    · have ha := hp (hx.trans (Path.source p).symm)
      have hb := hq (hval.trans (hx.trans (Path.target q).symm))
      have ha' := congrArg (fun z : I => (z : ℝ)) ha
      have hb' := congrArg (fun z : I => (z : ℝ)) hb
      dsimp at ha' hb'
      exfalso
      linarith
    · have ha := hp (hy.trans (Path.target p).symm)
      have hb := hq (hval.trans (hy.trans (Path.source q).symm))
      have ha' := congrArg (fun z : I => (z : ℝ)) ha
      have hb' := congrArg (fun z : I => (z : ℝ)) hb
      dsimp at ha' hb'
      exfalso
      have hs' : 1 / 2 < (s : ℝ) := lt_of_not_ge hs
      linarith
  · have hparam := hq hst
    apply Subtype.ext
    have hv := congrArg (fun z : I => (z : ℝ)) hparam
    dsimp at hv
    linarith

end JordanPath
