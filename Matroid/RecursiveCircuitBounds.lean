import Matroid.CycleExtensionality
import Matroid.RecursiveR10
import Matroid.TwoSumTargetCircuits

/-! Checked bridges toward the recursive target-circuit substitution claim. -/

namespace Matroid

universe u w

/-- A proper two-sum stage specified by its full cycle family is the exact
existing regular two-sum on the original labels. -/
theorem IsProperTwoSum.eq_regularTwoSum {α : Type u}
    {M N P : Matroid α} [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N) (p : α)
    (hinter : M.E ∩ N.E = {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard)
    (h : IsProperTwoSum M N P p) :
    P = regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN := by
  rcases h with ⟨_, _, _, _, _, _, _, hground, hcycle⟩
  apply ext_isCircuitUnion
  · simpa only [regularTwoSum_ground] using hground
  · intro X
    exact (hcycle X).trans
      ((Classical.choose_spec (exists_twoSum_of_regular hM hN p hinter)).2 X).symm

/-- The target-circuit substitution dichotomy for an arbitrary recorded
recursive proper-sum stage. Its only transitive cited premise is N146. -/
theorem IsProperTwoSum.targetCircuit_iff {α : Type u}
    {M N P : Matroid α} [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p τ : α) (hinter : M.E ∩ N.E = {p})
    (hτ : τ ∈ M.E \ {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard)
    (h : IsProperTwoSum M N P p) (C : Set α) :
    (P.IsCircuit C ∧ τ ∈ C) ↔
      (M.IsCircuit C ∧ p ∉ C ∧ τ ∈ C) ∨
      ∃ C₁ C₂ : Set α, M.IsCircuit C₁ ∧ N.IsCircuit C₂ ∧
        p ∈ C₁ ∧ p ∈ C₂ ∧ τ ∈ C₁ ∧ C = (C₁ ∪ C₂) \ {p} := by
  rw [h.eq_regularTwoSum hM hN p hinter hlM hlN hcM hcN hnM hnN]
  exact regularTwoSum_targetCircuit_iff M N hM hN p τ hinter hτ
    hlM hlN hcM hcN hnM hnN C

/-- The cardinality step in the recursive circuit bound: at a proper
two-sum stage, a target circuit either stays on the parent side or is a
union of the two port-deleted circuits. The side estimates are stated on
port-deleted sets, exactly as the leaf induction uses them. -/
theorem IsProperTwoSum.targetCircuit_ncard_le {α : Type u}
    {M N P : Matroid α} [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p τ : α) (hinter : M.E ∩ N.E = {p})
    (hτ : τ ∈ M.E \ {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard)
    (h : IsProperTwoSum M N P p) (k l : ℕ)
    (hparent : ∀ C, M.IsCircuit C → τ ∈ C → p ∉ C → C.ncard ≤ k)
    (hparentPort : ∀ C, M.IsCircuit C → τ ∈ C → p ∈ C →
      (C \ {p}).ncard ≤ k)
    (hchildPort : ∀ C, N.IsCircuit C → p ∈ C →
      (C \ {p}).ncard ≤ l)
    (C : Set α) (hC : P.IsCircuit C) (ht : τ ∈ C) :
    C.ncard ≤ k + l := by
  rcases (h.targetCircuit_iff hM hN p τ hinter hτ hlM hlN hcM hcN hnM hnN C).1
      ⟨hC, ht⟩ with hstay | ⟨C₁, C₂, hC₁, hC₂, hp₁, hp₂, ht₁, hEq⟩
  · exact (hparent C hstay.1 hstay.2.2 hstay.2.1).trans (Nat.le_add_right k l)
  · rw [hEq, Set.union_sdiff_distrib]
    exact (Set.ncard_union_le (C₁ \ {p}) (C₂ \ {p})).trans
      (Nat.add_le_add (hparentPort C₁ hC₁ ht₁ hp₁)
        (hchildPort C₂ hC₂ hp₂))

end Matroid
