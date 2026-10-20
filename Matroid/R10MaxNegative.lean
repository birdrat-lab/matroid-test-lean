import Matroid.R10TargetCircuits
import Matroid.MaximalNonspanning
import Mathlib.Tactic.FinCases

/-! Finite certificate route for N196, on the exact ten displayed labels. -/

namespace Matroid

/-- A decidable span test using the complete target-circuit list. -/
def r10SpansTargetCert (s : Finset (Fin 10)) : Prop :=
  (∃ i : Fin 6, (r10TargetFourCircuit i).erase 0 ⊆ s) ∨
  (∃ i : Fin 9, (r10TargetSixCandidate i).erase 0 ⊆ s)

instance (s : Finset (Fin 10)) : Decidable (r10SpansTargetCert s) := by
  unfold r10SpansTargetCert
  infer_instance

/-- The nine double-star sets with their common edge removed. -/
def r10MaxNegativeStar (i j : Fin 3) : Finset (Fin 10) :=
  (r10Row i ∪ r10Column j).erase (r10Edge i j)

/-- The fifteen maximal-negative candidates from the manuscript. -/
def r10MaxNegativeCert (s : Finset (Fin 10)) : Prop :=
  (∃ i j : Fin 3, s = r10MaxNegativeStar i j) ∨
  (∃ i : Fin 3, s = (Finset.univ.erase 0) \ r10Row i) ∨
  (∃ j : Fin 3, s = (Finset.univ.erase 0) \ r10Column j)

instance (s : Finset (Fin 10)) : Decidable (r10MaxNegativeCert s) := by
  unfold r10MaxNegativeCert
  infer_instance

-- The finite certificate checks all 1024 labeled subsets against 15 supports.
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 16384 in
theorem r10_maxNegative_finite_certificate :
    ∀ s : Finset (Fin 10), 0 ∉ s →
      ((¬ r10SpansTargetCert s ∧
        ∀ e ∈ (Finset.univ.erase 0) \ s,
          r10SpansTargetCert (insert e s)) ↔
      r10MaxNegativeCert s) := by
  decide

/-- The finite span predicate checks exactly the target closure condition
of the displayed R10, using the complete N195 target-circuit list. -/
theorem r10_mem_closure_zero_iff_cert (s : Finset (Fin 10)) (h0 : 0 ∉ s) :
    0 ∈ r10.closure (s : Set (Fin 10)) ↔ r10SpansTargetCert s := by
  have hground : (s : Set (Fin 10)) ⊆ r10.E := by simp
  have h0s : 0 ∉ (s : Set (Fin 10)) := by simpa using h0
  constructor
  · intro hcl
    obtain ⟨C, hC, h0C, hCsub⟩ :=
      (r10.mem_closure_iff_exists_circuit_sdiff hground h0s).mp hcl
    rcases (r10_targetCircuit_iff C).mp ⟨hC, h0C⟩ with
      ⟨i, hEq⟩ | ⟨i, hEq⟩
    · left
      refine ⟨i, ?_⟩
      intro e he
      apply hCsub
      rw [hEq]
      simpa [and_comm] using he
    · right
      refine ⟨i, ?_⟩
      intro e he
      apply hCsub
      rw [hEq]
      simpa [and_comm] using he
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · have hcl := (r10TargetFourCircuit_isCircuit i).mem_closure_sdiff_singleton_of_mem
        (r10TargetFourCircuit_target i)
      exact r10.closure_subset_closure (by
        intro e he
        exact hi (by simpa [and_comm] using he)) hcl
    · have hcl := (r10TargetSixCandidate_isCircuit i).mem_closure_sdiff_singleton_of_mem
        (r10TargetSixCandidate_target i)
      exact r10.closure_subset_closure (by
        intro e he
        exact hi (by simpa [and_comm] using he)) hcl

/-- N196: exactly the nine punctured double stars and six complements of
row/column stars are maximal nonspanning subsets of the pointed R10. -/
theorem r10_maximal_negative_iff (s : Finset (Fin 10)) (h0 : 0 ∉ s) :
    (0 ∉ r10.closure (s : Set (Fin 10)) ∧
      ∀ B : Set (Fin 10), (s : Set (Fin 10)) ⊂ B →
        B ⊆ r10.E \ {0} → 0 ∈ r10.closure B) ↔
      r10MaxNegativeCert s := by
  rw [← r10_maxNegative_finite_certificate s h0]
  constructor
  · rintro ⟨hnot, hmax⟩
    refine ⟨fun h => hnot ((r10_mem_closure_zero_iff_cert s h0).2 h), ?_⟩
    intro e he
    have heparts := Finset.mem_sdiff.mp he
    have he0 : e ≠ 0 := (Finset.mem_erase.mp heparts.1).1
    have hes : e ∉ s := heparts.2
    have hproper : (s : Set (Fin 10)) ⊂ insert e (s : Set (Fin 10)) :=
      Set.ssubset_iff_exists.mpr
        ⟨Set.subset_insert e _, e, Set.mem_insert e _, by simpa using hes⟩
    have hground : insert e (s : Set (Fin 10)) ⊆ r10.E \ {0} := by
      intro x hx
      rcases hx with rfl | hx
      · simp [he0]
      · exact ⟨by simp, by intro hx0; subst x; exact h0 hx⟩
    have hcl := hmax _ hproper hground
    exact (r10_mem_closure_zero_iff_cert (insert e s)
      (by simp [he0.symm, h0])).1 (by simpa using hcl)
  · rintro ⟨hnot, hsingle⟩
    refine ⟨fun h => hnot ((r10_mem_closure_zero_iff_cert s h0).1 h), ?_⟩
    intro B hproper hB
    obtain ⟨e, heB, heS⟩ := Set.exists_of_ssubset hproper
    have he0 : e ≠ 0 := by
      intro he
      exact (hB heB).2 he
    have hecert : r10SpansTargetCert (insert e s) :=
      hsingle e (by simpa [he0] using heS)
    have hcl := (r10_mem_closure_zero_iff_cert (insert e s)
      (by simp [he0.symm, h0])).2 hecert
    have hclSet : 0 ∈ r10.closure (insert e (s : Set (Fin 10))) := by
      simpa using hcl
    apply r10.closure_subset_closure (by
      intro x hx
      rcases (Set.mem_insert_iff.mp hx) with rfl | hx
      · exact heB
      · exact hproper.subset hx) hclSet
end Matroid
