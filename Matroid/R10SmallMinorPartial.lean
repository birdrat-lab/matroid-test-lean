import Matroid.R10ProperMinorPartial
import Matroid.R10Minors

/-! First cardinal and factorization steps for N178's small-minor claim.
The remaining step is a planar realization of every proper minor of the
corresponding K3,3 cycle or bond matroid on the surviving edge labels. -/

namespace Matroid

/-- A minor with fewer ground elements is a strict minor. -/
theorem IsMinor.strict_of_ground_ncard_lt {α : Type*} {M N : Matroid α}
    (h : N ≤m M) (hcard : N.E.ncard < M.E.ncard) : N <m M := by
  refine ⟨h, ?_⟩
  intro hrev
  have heq : N = M := h.antisymm hrev
  rw [heq] at hcard
  exact (Nat.lt_irrefl _) hcard

/-- At most eight surviving R10 labels leave at least two original labels
absent. The statement does not assume a particular minor construction. -/
theorem r10_small_ground_two_lost {N : Matroid (Fin 10)}
    (hcard : N.E.ncard ≤ 8) :
    ∃ e f : Fin 10, e ≠ f ∧ e ∉ N.E ∧ f ∉ N.E := by
  have hlt : N.E.ncard < r10.E.ncard := by
    rw [r10_ground_card]
    omega
  obtain ⟨e, he, hne⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
  have hlt' : N.E.ncard < (r10.E \ {e}).ncard := by
    rw [Set.ncard_sdiff_singleton_of_mem he, r10_ground_card]
    omega
  obtain ⟨f, hf, hnf⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt'
  refine ⟨e, f, ?_, hne, hnf⟩
  have hfe : f ≠ e := by simpa using hf.2
  exact hfe.symm

/-- The small minor factors through a *strict* minor of one nine-element
single-step R10 minor. This is the precise point where the K3,3
minor-minimal-planarity theorem must enter the manuscript proof. -/
theorem r10_smallMinor_factors_strict_single_step {N : Matroid (Fin 10)}
    (hminor : N ≤m r10) (hcard : N.E.ncard ≤ 8) :
    ∃ e : Fin 10,
      N <m (r10 ／ {e}) ∨ N <m (r10 ＼ {e}) := by
  have hstrict : N <m r10 :=
    hminor.strict_of_ground_ncard_lt (by rw [r10_ground_card]; omega)
  obtain ⟨e, _, hfactor⟩ := hstrict.exists_single_step_factor
  refine ⟨e, ?_⟩
  rcases hfactor with hc | hd
  · left
    apply hc.strict_of_ground_ncard_lt
    rw [Matroid.contract_ground, r10_ground]
    simp
    omega
  · right
    apply hd.strict_of_ground_ncard_lt
    rw [Matroid.delete_ground, r10_ground]
    simp
    omega

end Matroid
