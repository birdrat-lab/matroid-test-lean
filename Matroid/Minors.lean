import Matroid.RankClosure
import Mathlib.Combinatorics.Matroid.Minor.Contract
import Mathlib.Combinatorics.Matroid.Minor.Delete
import Mathlib.Combinatorics.Matroid.Rank.ENat

/-! # Minor rank -/

open Set

namespace Matroid

/-- Manuscript: `def:matroid-minors` (N024). Deletion is restriction to the
complement within the ground set. -/
theorem deletion_eq_restriction {α : Type*} (M : Matroid α) (A : Set α) :
    M ＼ A = M ↾ (M.E \ A) := M.delete_eq_restrict A

/-- Manuscript ledger N027: successive deletions combine into deletion of
the union, including the disjoint case used in the manuscript. -/
theorem deletion_composition {α : Type*} (M : Matroid α)
    (A B : Set α) : M ＼ A ＼ B = M ＼ (A ∪ B) :=
  M.delete_delete A B

/-- Manuscript ledger N181; the proof of `prop:r10-no-three-sum` deletes an
element outside a circuit. -/
theorem IsCircuit.of_avoids_deleted_element {α : Type*} {M : Matroid α}
    {C : Set α} {e : α} (hC : M.IsCircuit C) (he : e ∉ C) :
    (M ＼ {e}).IsCircuit C := by
  apply (M.delete_isCircuit_iff).2
  refine ⟨hC, Set.disjoint_left.mpr ?_⟩
  intro x hxC hxe
  exact he (by simpa using hxe ▸ hxC)

/-- Manuscript: `def:matroid-minors` (N025). The natural-valued finite rank
of a contraction is the rank gain from adjoining the contracted set. -/
theorem contract_rank_toNat_eq_sub {α : Type*} {M : Matroid α} [M.Finite]
    {A X : Set α} (hA : A ⊆ M.E) (hX : X ⊆ M.E \ A) :
    ((M ／ A).eRk X).toNat =
      (M.eRk (X ∪ A)).toNat - (M.eRk A).toNat := by
  have hY : A ∪ X ⊆ M.E := union_subset hA (hX.trans sdiff_subset)
  obtain ⟨I, J, hI, hJ, hIJ⟩ :=
    M.exists_isBasis_subset_isBasis (X := A) (Y := A ∪ X) subset_union_left hY
  have hYX : (A ∪ X) \ A = X := by
    ext e
    constructor
    · intro he
      rcases he.1 with heA | heX
      · exact (he.2 heA).elim
      · exact heX
    · intro heX
      exact ⟨Or.inr heX, hX heX |>.2⟩
  have hJI : (M ／ I).IsBasis (J \ I) X := by
    simpa only [hYX] using hI.contract_sdiff_isBasis_sdiff hJ hIJ
  have hXrest : X ⊆ (M ／ I).E \ (A \ I) := by
    intro e heX
    have he := hX heX
    exact ⟨⟨he.1, fun heI => he.2 (hI.subset heI)⟩,
      fun heAI => he.2 heAI.1⟩
  have hcontract : (M ／ A).eRk X = (J \ I).encard := by
    rw [hI.contract_eq_contract_delete, (M ／ I).delete_eq_restrict]
    rw [(M ／ I).restrict_eRk_eq hXrest]
    exact hJI.eRk_eq_encard
  rw [hcontract, union_comm X A, hJ.eRk_eq_encard, hI.eRk_eq_encard]
  change (J \ I).ncard = J.ncard - I.ncard
  have hcard := Set.ncard_sdiff_add_ncard_of_subset hIJ hJ.Finite
  omega

end Matroid
