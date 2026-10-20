import Matroid.RecursiveCircuitBounds
import Matroid.TwoSumTargetCocircuits

/-! Checked one-stage cocircuit substitution and size bound toward the
natural recursive R10 program. -/

namespace Matroid

universe u w

/-- The exact cocircuit alternatives at any recorded proper two-sum
stage; the only transitive cited premise is N148. -/
theorem IsProperTwoSum.targetCocircuit_iff {α : Type u}
    {M N P : Matroid α} [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p τ : α) (hinter : M.E ∩ N.E = {p})
    (hτ : τ ∈ M.E \ {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard)
    (h : IsProperTwoSum M N P p) (D : Set α) :
    (P.IsHyperplaneCocircuit D ∧ τ ∈ D) ↔
      (M.IsHyperplaneCocircuit D ∧ p ∉ D ∧ τ ∈ D) ∨
      ∃ D₁ D₂ : Set α,
        M.IsHyperplaneCocircuit D₁ ∧ N.IsHyperplaneCocircuit D₂ ∧
        p ∈ D₁ ∧ p ∈ D₂ ∧ τ ∈ D₁ ∧ D = (D₁ ∪ D₂) \ {p} := by
  rw [h.eq_regularTwoSum hM hN p hinter hlM hlN hcM hcN hnM hnN]
  exact regularTwoSum_targetCocircuit_iff M N hM hN p τ hinter hτ
    hlM hlN hcM hcN hnM hnN D

/-- The cocircuit side of the one-stage leaf-cardinality induction. -/
theorem IsProperTwoSum.targetCocircuit_ncard_le {α : Type u}
    {M N P : Matroid α} [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p τ : α) (hinter : M.E ∩ N.E = {p})
    (hτ : τ ∈ M.E \ {p})
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard)
    (h : IsProperTwoSum M N P p) (k l : ℕ)
    (hparent : ∀ D, M.IsHyperplaneCocircuit D → τ ∈ D → p ∉ D → D.ncard ≤ k)
    (hparentPort : ∀ D, M.IsHyperplaneCocircuit D → τ ∈ D → p ∈ D →
      (D \ {p}).ncard ≤ k)
    (hchildPort : ∀ D, N.IsHyperplaneCocircuit D → p ∈ D →
      (D \ {p}).ncard ≤ l)
    (D : Set α) (hD : P.IsHyperplaneCocircuit D) (ht : τ ∈ D) :
    D.ncard ≤ k + l := by
  rcases (h.targetCocircuit_iff hM hN p τ hinter hτ hlM hlN hcM hcN hnM hnN D).1
      ⟨hD, ht⟩ with hstay | ⟨D₁, D₂, hD₁, hD₂, hp₁, hp₂, ht₁, hEq⟩
  · exact (hparent D hstay.1 hstay.2.2 hstay.2.1).trans (Nat.le_add_right k l)
  · rw [hEq, Set.union_sdiff_distrib]
    exact (Set.ncard_union_le (D₁ \ {p}) (D₂ \ {p})).trans
      (Nat.add_le_add (hparentPort D₁ hD₁ ht₁ hp₁)
        (hchildPort D₂ hD₂ hp₂))

end Matroid
