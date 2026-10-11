import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Combinatorics.Matroid.Loop

/-! # WeightedBases -/

open Set

namespace Matroid

/-- Manuscript: prose before `thm:regular-matroid-energy` (N122).
The product omits the distinguished element even for bases containing it. -/
noncomputable def weightedBasesIn {α R : Type*} [CommSemiring R]
    (M : Matroid α) (hE : M.E.Finite) (τ : α) (w : α → R) : R := by
  classical
  exact ∑ B ∈ hE.toFinset.powerset,
    if M.IsBase (B : Set α) ∧ τ ∈ B then ∏ e ∈ B.erase τ, w e else 0

/-- Manuscript: prose before `thm:regular-matroid-energy` (N122).
This is the target-omitting part of the same finite weighted basis sum. -/
noncomputable def weightedBasesOut {α R : Type*} [CommSemiring R]
    (M : Matroid α) (hE : M.E.Finite) (τ : α) (w : α → R) : R := by
  classical
  exact ∑ B ∈ hE.toFinset.powerset,
    if M.IsBase (B : Set α) ∧ τ ∉ B then ∏ e ∈ B.erase τ, w e else 0

/-- A coloop belongs to every basis, so the target-omitting weighted
basis sum vanishes for any commutative semiring of weights. -/
theorem weightedBasesOut_eq_zero_of_isColoop {α R : Type*} [CommSemiring R]
    (M : Matroid α) (hE : M.E.Finite) (τ : α) (w : α → R)
    (hτ : M.IsColoop τ) : weightedBasesOut M hE τ w = 0 := by
  classical
  unfold weightedBasesOut
  apply Finset.sum_eq_zero
  intro B hB
  split_ifs with h
  · exact (h.2 (hτ.mem_of_isBase h.1)).elim
  · rfl

/-- A finite subset of a disjoint union is uniquely the union of its two
intersections. This is the finite-index sum bridge for N137's basis
factorization; it does not itself assert a matroid basis identity. -/
theorem sum_powerset_union_of_disjoint {α R : Type*} [DecidableEq α]
    [AddCommMonoid R] (s t : Finset α) (h : Disjoint s t)
    (f : Finset α → R) :
    (∑ B ∈ (s ∪ t).powerset, f B) =
      ∑ p ∈ s.powerset ×ˢ t.powerset, f (p.1 ∪ p.2) := by
  classical
  apply Finset.sum_bij (fun B _ => (B ∩ s, B ∩ t))
  · intro B hB
    simp only [Finset.mem_product, Finset.mem_powerset]
    exact ⟨Finset.inter_subset_right, Finset.inter_subset_right⟩
  · intro B hB C hC hpair
    have hBs : B ⊆ s ∪ t := Finset.mem_powerset.mp hB
    have hCs : C ⊆ s ∪ t := Finset.mem_powerset.mp hC
    have hsplitB : B = (B ∩ s) ∪ (B ∩ t) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · intro hx
        rcases Finset.mem_union.mp (hBs hx) with hs | ht
        · exact Or.inl ⟨hx, hs⟩
        · exact Or.inr ⟨hx, ht⟩
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    have hsplitC : C = (C ∩ s) ∪ (C ∩ t) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · intro hx
        rcases Finset.mem_union.mp (hCs hx) with hs | ht
        · exact Or.inl ⟨hx, hs⟩
        · exact Or.inr ⟨hx, ht⟩
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    calc
      B = (B ∩ s) ∪ (B ∩ t) := hsplitB
      _ = (C ∩ s) ∪ (C ∩ t) := by
        have hs : B ∩ s = C ∩ s := congrArg Prod.fst hpair
        have ht : B ∩ t = C ∩ t := congrArg Prod.snd hpair
        rw [hs, ht]
      _ = C := hsplitC.symm
  · intro p hp
    have hp1 : p.1 ⊆ s := Finset.mem_powerset.mp (Finset.mem_product.mp hp).1
    have hp2 : p.2 ⊆ t := Finset.mem_powerset.mp (Finset.mem_product.mp hp).2
    refine ⟨p.1 ∪ p.2, ?_, ?_⟩
    · exact Finset.mem_powerset.mpr
        (Finset.union_subset (hp1.trans Finset.subset_union_left) (hp2.trans Finset.subset_union_right))
    · apply Prod.ext
      · ext x
        simp only [Finset.mem_union, Finset.mem_inter]
        constructor
        · rintro ⟨hx1 | hx2, hxs⟩
          · exact hx1
          · exact False.elim ((Finset.disjoint_left.mp h) hxs (hp2 hx2))
        · intro hx1
          exact ⟨Or.inl hx1, hp1 hx1⟩
      · ext x
        simp only [Finset.mem_union, Finset.mem_inter]
        constructor
        · rintro ⟨hx1 | hx2, hxt⟩
          · exact False.elim ((Finset.disjoint_left.mp h) (hp1 hx1) hxt)
          · exact hx2
        · intro hx2
          exact ⟨Or.inr hx2, hp2 hx2⟩
  · intro B hB
    congr 1
    ext x
    have hBs : B ⊆ s ∪ t := Finset.mem_powerset.mp hB
    grind

end Matroid
