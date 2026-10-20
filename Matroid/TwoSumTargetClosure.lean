import Matroid.TwoSumTargetCircuits

/-! The manuscript-local target-closure substitution for proper 2-sums. -/

namespace Matroid

universe u w

/-- The available elements on the two sides survive on the exact labeled
ground of the proper two-sum. This is the ground-set part of N147. -/
theorem regularTwoSum_available_subset_ground {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p : α) (hinter : M.E ∩ N.E = {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard)
    (A B : Set α) (hA : A ⊆ M.E \ {p}) (hB : B ⊆ N.E \ {p}) :
    A ∪ B ⊆
      (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN).E := by
  rw [regularTwoSum_ground]
  intro x hx
  rcases hx with hxA | hxB
  · have hxM : x ∈ M.E := (hA hxA).1
    have hxp : x ≠ p := (hA hxA).2
    have hxN : x ∉ N.E := by
      intro hxN
      have hp : x ∈ ({p} : Set α) := by
        rw [← hinter]
        exact ⟨hxM, hxN⟩
      exact hxp (by simpa using hp)
    simp [Set.mem_symmDiff, hxM, hxN]
  · have hxN : x ∈ N.E := (hB hxB).1
    have hxp : x ≠ p := (hB hxB).2
    have hxM : x ∉ M.E := by
      intro hxM
      have hp : x ∈ ({p} : Set α) := by
        rw [← hinter]
        exact ⟨hxM, hxN⟩
      exact hxp (by simpa using hp)
    simp [Set.mem_symmDiff, hxM, hxN]

/-- N147: the target closure of a proper two-sum substitutes the child's
port-spanning condition into the parent. The right side is the explicit
Boolean version of declaring the port available exactly when the child
spans it. -/
theorem regularTwoSum_target_mem_closure_iff {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p τ : α) (hinter : M.E ∩ N.E = {p})
    (hτ : τ ∈ M.E \ {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard)
    (A B : Set α) (hA : A ⊆ M.E \ {p, τ}) (hB : B ⊆ N.E \ {p}) :
    τ ∈ (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN).closure
      (A ∪ B) ↔
    τ ∈ M.closure A ∨
      (p ∈ N.closure B ∧ τ ∈ M.closure (A ∪ {p})) := by
  let P := regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN
  have hpMN : p ∈ M.E ∩ N.E := by rw [hinter]; simp
  have hτN : τ ∉ N.E := by
    intro hNτ
    have hp : τ ∈ ({p} : Set α) := by
      rw [← hinter]
      exact ⟨hτ.1, hNτ⟩
    exact hτ.2 (by simpa using hp)
  have hA0 : A ⊆ M.E \ {p} := by
    intro x hx
    exact ⟨(hA hx).1, fun hxp => (hA hx).2 (by
      have hxe : x = p := by simpa using hxp
      simp [hxe])⟩
  have hB0 : B ⊆ N.E \ {p} := hB
  have hPground : A ∪ B ⊆ P.E := by
    exact regularTwoSum_available_subset_ground M N hM hN p hinter
      hlM hlN hcM hcN hnM hnN A B hA0 hB0
  have hτAB : τ ∉ A ∪ B := by
    intro h
    rcases h with h | h
    · exact (hA h).2 (by simp)
    · exact hτN (hB h).1
  have hpB : p ∉ B := by intro h; exact (hB h).2 rfl
  have hτA : τ ∉ A := by intro h; exact (hA h).2 (by simp)
  have hAground : A ⊆ M.E := fun _ h => (hA h).1
  have hBground : B ⊆ N.E := fun _ h => (hB h).1
  have hAportGround : A ∪ {p} ⊆ M.E :=
    Set.union_subset hAground (Set.singleton_subset_iff.mpr hpMN.1)
  have hτAport : τ ∉ A ∪ {p} := by
    intro h
    rcases h with h | h
    · exact hτA h
    · exact hτ.2 (by simpa using h)
  letI : P.Finite := ⟨by
    change (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN).E.Finite
    rw [regularTwoSum_ground]
    exact M.ground_finite.symmDiff N.ground_finite⟩
  have hsplit (C : Set α) :=
    regularTwoSum_targetCircuit_iff M N hM hN p τ hinter hτ
      hlM hlN hcM hcN hnM hnN C
  constructor
  · intro hcl
    obtain ⟨C, hC, hτC, hCsub⟩ :=
      (P.mem_closure_iff_exists_circuit_sdiff hPground hτAB).mp hcl
    rcases (hsplit C).mp ⟨hC, hτC⟩ with
      ⟨hCM, hpC, hτC⟩ | ⟨C₁, C₂, hC₁, hC₂, hp₁, hp₂, hτ₁, hEq⟩
    · left
      apply (M.mem_closure_iff_exists_circuit_sdiff hAground hτA).mpr
      refine ⟨C, hCM, hτC, ?_⟩
      intro x hx
      have hxAB := hCsub hx
      rcases hxAB with hxA | hxB
      · exact hxA
      · have hxM := hCM.subset_ground hx.1
        have hxp : x ∈ ({p} : Set α) := by
          rw [← hinter]
          exact ⟨hxM, hBground hxB⟩
        exact False.elim (hpC (by simpa only [Set.mem_singleton_iff] using hxp ▸ hx.1))
    · right
      constructor
      · apply (N.mem_closure_iff_exists_circuit_sdiff hBground hpB).mpr
        refine ⟨C₂, hC₂, hp₂, ?_⟩
        intro x hx
        have hxp : x ≠ p := by simpa using hx.2
        have hxC : x ∈ C := by
          rw [hEq]
          exact ⟨Or.inr hx.1, by simpa using hxp⟩
        have hxAB := hCsub ⟨hxC, by
          intro heτ
          have hxN := hC₂.subset_ground hx.1
          exact hτN (heτ ▸ hxN)⟩
        rcases hxAB with hxA | hxB
        · have hxN := hC₂.subset_ground hx.1
          have hp : x ∈ ({p} : Set α) := by
            rw [← hinter]
            exact ⟨hAground hxA, hxN⟩
          exact False.elim (hxp (by simpa using hp))
        · exact hxB
      · apply (M.mem_closure_iff_exists_circuit_sdiff hAportGround hτAport).mpr
        refine ⟨C₁, hC₁, hτ₁, ?_⟩
        intro x hx
        by_cases hxp : x = p
        · exact Or.inr (by simp [hxp])
        · have hxC : x ∈ C := by
            rw [hEq]
            exact ⟨Or.inl hx.1, by simpa using hxp⟩
          have hxAB := hCsub ⟨hxC, hx.2⟩
          rcases hxAB with hxA | hxB
          · exact Or.inl hxA
          · have hxM := hC₁.subset_ground hx.1
            have hp : x ∈ ({p} : Set α) := by
              rw [← hinter]
              exact ⟨hxM, hBground hxB⟩
            exact False.elim (hxp (by simpa using hp))
  · rintro (hclA | ⟨hclB, hclAp⟩)
    · obtain ⟨C, hCM, hτC, hCsub⟩ :=
        (M.mem_closure_iff_exists_circuit_sdiff hAground hτA).mp hclA
      have hpC : p ∉ C := by
        intro hpC
        have hpτ : p ≠ τ := by
          intro h
          exact hτ.2 (by simp [h.symm])
        have hpA : p ∈ A := hCsub ⟨hpC, by simpa using hpτ⟩
        exact (hA0 hpA).2 rfl
      have hPC : P.IsCircuit C :=
        ((hsplit C).mpr (Or.inl ⟨hCM, hpC, hτC⟩)).1
      apply (P.mem_closure_iff_exists_circuit_sdiff hPground hτAB).mpr
      exact ⟨C, hPC, hτC, fun x hx => Or.inl (hCsub hx)⟩
    · obtain ⟨C₁, hC₁, hτ₁, hC₁sub⟩ :=
        (M.mem_closure_iff_exists_circuit_sdiff hAportGround hτAport).mp hclAp
      by_cases hp₁ : p ∈ C₁
      · obtain ⟨C₂, hC₂, hp₂, hC₂sub⟩ :=
          (N.mem_closure_iff_exists_circuit_sdiff hBground hpB).mp hclB
        let C := (C₁ ∪ C₂) \ {p}
        have hPC : P.IsCircuit C ∧ τ ∈ C :=
          (hsplit C).mpr (Or.inr ⟨C₁, C₂, hC₁, hC₂, hp₁, hp₂, hτ₁, rfl⟩)
        apply (P.mem_closure_iff_exists_circuit_sdiff hPground hτAB).mpr
        refine ⟨C, hPC.1, hPC.2, ?_⟩
        intro x hx
        have hxp : x ≠ p := by simpa [C] using hx.1.2
        rcases hx.1.1 with hx₁ | hx₂
        · rcases hC₁sub ⟨hx₁, hx.2⟩ with hxA | hxport
          · exact Or.inl hxA
          · exact False.elim (hxp (by simpa using hxport))
        · exact Or.inr (hC₂sub ⟨hx₂, by simpa using hxp⟩)
      · have hC₁subA : C₁ \ {τ} ⊆ A := by
          intro x hx
          rcases hC₁sub hx with hxA | hxport
          · exact hxA
          · have hxp : x = p := by simpa using hxport
            exact False.elim (hp₁ (hxp ▸ hx.1))
        have hPC : P.IsCircuit C₁ :=
          ((hsplit C₁).mpr (Or.inl ⟨hC₁, hp₁, hτ₁⟩)).1
        apply (P.mem_closure_iff_exists_circuit_sdiff hPground hτAB).mpr
        exact ⟨C₁, hPC, hτ₁, fun x hx => Or.inl (hC₁subA hx)⟩

end Matroid
