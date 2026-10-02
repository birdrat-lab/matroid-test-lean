import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Combinatorics.Matroid.Closure

/-! # ThreeSum -/

open Set

namespace Matroid

/-- Manuscript: prose before `lem:seymour-three-sum-five` (N158).
A triangle has only the five listed possible closure intersections. The
independence, cospanning, and coindependence conditions on the side set are
unneeded for this particular conclusion. -/
theorem triangle_closure_five_classes {α : Type*} {M : Matroid α}
    {S : Set α} {a b c : α} (hT : M.IsCircuit ({a, b, c} : Set α))
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    M.closure S ∩ ({a, b, c} : Set α) = ∅ ∨
    M.closure S ∩ ({a, b, c} : Set α) = {a} ∨
    M.closure S ∩ ({a, b, c} : Set α) = {b} ∨
    M.closure S ∩ ({a, b, c} : Set α) = {c} ∨
    M.closure S ∩ ({a, b, c} : Set α) = {a, b, c} := by
  classical
  let T : Set α := {a, b, c}
  have third (x : α) (hx : x ∈ T) (hsub : T \ {x} ⊆ M.closure S) :
      x ∈ M.closure S := by
    have hxcl : x ∈ M.closure (T \ {x}) := hT.mem_closure_sdiff_singleton_of_mem hx
    exact M.closure_closure S ▸ (M.closure_subset_closure hsub hxcl)
  have habc : a ∈ M.closure S → b ∈ M.closure S → c ∈ M.closure S := by
    intro ha hb
    apply third c (by simp [T])
    intro x hx
    simp only [T, mem_sdiff, mem_insert_iff, mem_singleton_iff] at hx
    rcases hx.1 with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact (hx.2 rfl).elim
  have hacb : a ∈ M.closure S → c ∈ M.closure S → b ∈ M.closure S := by
    intro ha hc
    apply third b (by simp [T])
    intro x hx
    simp only [T, mem_sdiff, mem_insert_iff, mem_singleton_iff] at hx
    rcases hx.1 with rfl | rfl | rfl
    · exact ha
    · exact (hx.2 rfl).elim
    · exact hc
  have hbca : b ∈ M.closure S → c ∈ M.closure S → a ∈ M.closure S := by
    intro hb hc
    apply third a (by simp [T])
    intro x hx
    simp only [T, mem_sdiff, mem_insert_iff, mem_singleton_iff] at hx
    rcases hx.1 with rfl | rfl | rfl
    · exact (hx.2 rfl).elim
    · exact hb
    · exact hc
  by_cases ha : a ∈ M.closure S <;>
    by_cases hb : b ∈ M.closure S <;>
    by_cases hc : c ∈ M.closure S <;>
    simp_all [Set.inter_insert_of_mem, Set.inter_insert_of_notMem]

end Matroid
