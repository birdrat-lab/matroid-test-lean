import Matroid.TwoElementCircuit
import Matroid.MapCircuitUnion
import Matroid.CycleExtensionality

/-! The two-element child of a binary two-sum relabels the parent port. -/

namespace Matroid

attribute [local instance] Classical.propDecidable Classical.decEq

private theorem swap_image_cycle {α : Type*} (M : Matroid α)
    (p leaf : α) (hleaf : leaf ∉ M.E)
    {C : Set α} (hCM : C ⊆ M.E) :
    (Equiv.swap p leaf) '' C =
      if p ∈ C then _root_.symmDiff C {p, leaf} else C := by
  classical
  have hleafC : leaf ∉ C := fun h => hleaf (hCM h)
  by_cases hp : p ∈ C
  · rw [if_pos hp, Equiv.image_swap_of_mem_of_notMem hp hleafC]
    ext x
    by_cases hxp : x = p
    · subst x
      simp [Set.mem_symmDiff, hleafC]
      exact hp
    · by_cases hxl : x = leaf
      · subst x
        simp [Set.mem_symmDiff, hleafC, hxp]
      · simp [Set.mem_symmDiff, hxp, hxl]
  · rw [if_neg hp]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Equiv.swap_apply_of_ne_of_ne
        (fun h : y = p => hp (h ▸ hy))
        (fun h : y = leaf => hleafC (h ▸ hy))]
      exact hy
    · intro hx
      exact ⟨x, hx, Equiv.swap_apply_of_ne_of_ne
        (fun h => hp (h ▸ hx)) (fun h => hleafC (h ▸ hx))⟩

/-- N152: after a two-element circuit child is attached, the binary
two-sum cycle matroid is exactly the parent with its port relabeled by the
surviving child leaf. The weak cycle construction is used because the
manuscript's proper 2-sum size convention excludes a two-element side. -/
theorem twoSumWithPair_eq_mapEquiv_swap {α : Type u}
    (M N : Matroid α) [M.Finite] [N.Finite]
    (hM : Regular.{u, 0, w} M) (hN : Regular.{u, 0, w} N)
    (p leaf : α) (hinter : M.E ∩ N.E = {p})
    (hNE : N.E = ({p, leaf} : Set α))
    (hpair : N.IsCircuit ({p, leaf} : Set α))
    (hne : p ≠ leaf) :
    twoSumWithPair M N hM hN p hinter =
      M.mapEquiv (Equiv.swap p leaf) := by
  classical
  have hpM : p ∈ M.E := by
    have hp : p ∈ M.E ∩ N.E := by rw [hinter]; simp
    exact hp.1
  have hleafM : leaf ∉ M.E := by
    intro h
    have hboth : leaf ∈ M.E ∩ N.E := ⟨h, by rw [hNE]; simp⟩
    rw [hinter] at hboth
    exact hne (Set.mem_singleton_iff.mp hboth).symm
  let f : α ≃ α := Equiv.swap p leaf
  have hground : (twoSumWithPair M N hM hN p hinter).E =
      (M.mapEquiv f).E := by
    rw [twoSumWithPair_ground]
    rw [mapEquiv_ground_eq]
    change _root_.symmDiff M.E N.E = f '' M.E
    rw [hNE, show f '' M.E = insert leaf M.E \ {p} from
      Equiv.image_swap_of_mem_of_notMem hpM hleafM]
    ext x
    by_cases hxp : x = p
    · subst x
      simp [Set.mem_symmDiff, hpM, hne]
    · by_cases hxl : x = leaf
      · subst x
        simp [Set.mem_symmDiff, hleafM, hne, hxp]
      · simp [Set.mem_symmDiff, hxp, hxl]
  apply ext_isCircuitUnion hground
  intro X
  rw [twoSumWithPair_cycle_iff_relabelPort M N hM hN p leaf hinter hNE hpair X,
    mapEquiv_isCircuitUnion_iff]
  constructor
  · rintro ⟨C, hC, ⟨hp, rfl⟩ | ⟨hp, rfl⟩⟩
    · have hswap := swap_image_cycle M p leaf hleafM hC.subset_ground
      rw [if_neg hp] at hswap
      have hImage : f.symm '' X = X := by simpa [f] using hswap
      rw [hImage]
      exact hC
    · have hswap := swap_image_cycle M p leaf hleafM hC.subset_ground
      rw [if_pos hp] at hswap
      have hImage : f.symm '' _root_.symmDiff C {p, leaf} = C := by
        rw [← hswap]
        simp [f, Set.image_image, Equiv.swap_apply_self]
      rw [hImage]
      exact hC
  · intro hX
    let C := f.symm '' X
    have hC : M.IsCircuitUnion C := hX
    have hXeq : X = f '' C := by simp [C]
    refine ⟨C, hC, ?_⟩
    have hswap := swap_image_cycle M p leaf hleafM hC.subset_ground
    by_cases hp : p ∈ C
    · rw [if_pos hp] at hswap
      exact Or.inr ⟨hp, hXeq.trans (by simpa [f] using hswap)⟩
    · rw [if_neg hp] at hswap
      exact Or.inl ⟨hp, hXeq.trans (by simpa [f] using hswap)⟩

end Matroid
