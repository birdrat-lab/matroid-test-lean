import Matroid.TwoSumCycles

/-! A two-element circuit child for the recursive R10 minor argument (N152). -/

namespace Matroid

/-- A matroid whose entire ground is a two-element circuit has exactly two
cycles: the empty cycle and the whole ground. -/
theorem isCircuitUnion_iff_empty_or_pair {α : Type*} {N : Matroid α}
    {p u : α} (hE : N.E = ({p, u} : Set α))
    (hC : N.IsCircuit ({p, u} : Set α)) (D : Set α) :
    N.IsCircuitUnion D ↔ D = ∅ ∨ D = {p, u} := by
  constructor
  · intro hD
    by_cases hDE : D = ∅
    · exact Or.inl hDE
    · right
      have hDsub : D ⊆ N.E := hD.subset_ground
      obtain ⟨Cs, hCs, _, hUnion⟩ := hD
      have hCsne : Cs.Nonempty := by
        by_contra hn
        have hempty : Cs = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
        exact hDE (by simpa [hempty] using hUnion)
      obtain ⟨C, hCmem⟩ := hCsne
      have hC' : N.IsCircuit C := hCs C hCmem
      have hCsub : C ⊆ ({p, u} : Set α) := by
        rw [← hE]
        exact hC'.subset_ground
      have hEq : C = ({p, u} : Set α) :=
        hC'.eq_of_subset_isCircuit hC hCsub
      have hpairD : ({p, u} : Set α) ⊆ D := by
        rw [← hEq, hUnion]
        intro x hx
        exact Set.mem_sUnion.mpr ⟨C, by simpa using hCmem, hx⟩
      exact Set.Subset.antisymm (by rw [← hE]; exact hDsub) hpairD
  · rintro (rfl | rfl)
    · refine ⟨∅, ?_, ?_, ?_⟩ <;> simp
    · exact hC.isCircuitUnion

/-- The binary two-sum cycle construction remains defined for a
two-element circuit child, outside the proper-size convention. -/
noncomputable def twoSumWithPair {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p : α) (hinter : M.E ∩ N.E = {p}) : Matroid α :=
  Classical.choose (exists_twoSum_of_regular hM hN p hinter)

theorem twoSumWithPair_ground {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p : α) (hinter : M.E ∩ N.E = {p}) :
    (twoSumWithPair M N hM hN p hinter).E =
      _root_.symmDiff M.E N.E :=
  (Classical.choose_spec (exists_twoSum_of_regular hM hN p hinter)).1

/-- For a two-element-circuit child, the complete N065 cycle formula
reduces to replacing the parent port by the child leaf in every cycle. -/
theorem twoSumWithPair_cycle_iff_relabelPort {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p leaf : α) (hinter : M.E ∩ N.E = {p})
    (hNE : N.E = ({p, leaf} : Set α))
    (hpair : N.IsCircuit ({p, leaf} : Set α))
    (X : Set α) :
    (twoSumWithPair M N hM hN p hinter).IsCircuitUnion X ↔
      ∃ C : Set α, M.IsCircuitUnion C ∧
        ((p ∉ C ∧ X = C) ∨
          (p ∈ C ∧ X = _root_.symmDiff C {p, leaf})) := by
  have hiff :
      (twoSumWithPair M N hM hN p hinter).IsCircuitUnion X ↔
        TwoSumCycle M N p X :=
    (Classical.choose_spec (exists_twoSum_of_regular hM hN p hinter)).2 X
  rw [hiff]
  constructor
  · rintro ⟨C, D, hC, hD, hp, hEq⟩
    rcases (isCircuitUnion_iff_empty_or_pair hNE hpair D).mp hD with rfl | rfl
    · have hpC : p ∉ C := by simpa using hp
      exact ⟨C, hC, Or.inl ⟨hpC, by simpa [symmDiff] using hEq⟩⟩
    · have hpC : p ∈ C := hp.mpr (by simp)
      exact ⟨C, hC, Or.inr ⟨hpC, hEq⟩⟩
  · rintro ⟨C, hC, ⟨hpC, hEq⟩ | ⟨hpC, hEq⟩⟩
    · refine ⟨C, ∅, hC, ?_, ?_, ?_⟩
      · refine ⟨∅, ?_, ?_, ?_⟩ <;> simp
      · simpa using hpC
      · simpa [symmDiff] using hEq
    · refine ⟨C, {p, leaf}, hC, hpair.isCircuitUnion, ?_, ?_⟩
      · simp [hpC]
      · exact hEq

/-- Compatibility with the previously recorded proper-size interface.
Its hypotheses are contradictory for a two-element child; use
`twoSumWithPair_cycle_iff_relabelPort` for the actual minor step. -/
theorem regularTwoSum_cycle_iff_relabelPort {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p leaf : α) (hinter : M.E ∩ N.E = {p})
    (hNE : N.E = ({p, leaf} : Set α))
    (hpair : N.IsCircuit ({p, leaf} : Set α))
    (hlM : ¬ M.IsLoop p) (hlN : ¬ N.IsLoop p)
    (hcM : ¬ M.IsColoop p) (hcN : ¬ N.IsColoop p)
    (hnM : 3 ≤ M.E.ncard) (hnN : 3 ≤ N.E.ncard)
    (X : Set α) :
    (regularTwoSum M N hM hN p hinter hlM hlN hcM hcN hnM hnN).IsCircuitUnion X ↔
      ∃ C : Set α, M.IsCircuitUnion C ∧
        ((p ∉ C ∧ X = C) ∨
          (p ∈ C ∧ X = _root_.symmDiff C {p, leaf})) := by
  simpa only [regularTwoSum, twoSumWithPair] using
    twoSumWithPair_cycle_iff_relabelPort M N hM hN p leaf hinter hNE hpair X

end Matroid
