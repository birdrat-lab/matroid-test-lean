import Matroid.RankClosure
import Mathlib.Combinatorics.Matroid.Minor.Contract
import Mathlib.Combinatorics.Matroid.Minor.Delete
import Mathlib.Combinatorics.Matroid.Minor.Order
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

/-- Manuscript `def:matroid-minors` (N026): the minor relation is generated
by deletion and contraction. Mathlib normalizes every finite sequence to
one contraction followed by one deletion. -/
theorem minor_iff_contract_delete {α : Type*} (N M : Matroid α) :
    N ≤m M ↔ ∃ C D : Set α, N = M ／ C ＼ D := Iff.rfl

/-- A deletion is a minor in the manuscript sense (N026). -/
theorem deletion_isMinor {α : Type*} (M : Matroid α) (D : Set α) :
    M ＼ D ≤m M := by
  simpa using M.contract_delete_isMinor ∅ D

/-- A contraction is a minor in the manuscript sense (N026). -/
theorem contraction_isMinor {α : Type*} (M : Matroid α) (C : Set α) :
    M ／ C ≤m M := by
  simpa using M.contract_delete_isMinor C ∅

/-- Composition of the two generating operations keeps a minor a minor;
induction gives the manuscript's arbitrary finite sequence (N026). -/
theorem minor_trans {α : Type*} {L N M : Matroid α}
    (hLN : L ≤m N) (hNM : N ≤m M) : L ≤m M := hLN.trans hNM

/-- Manuscript minor algebra (N028). The identity also holds without a
disjointness hypothesis because repeated contraction removes any overlap. -/
theorem contraction_composition {α : Type*} (M : Matroid α)
    (A B : Set α) : M ／ A ／ B = M ／ (A ∪ B) := M.contract_contract A B

/-- Manuscript minor algebra (N029), with the required disjoint sets. -/
theorem deletion_contraction_commutation {α : Type*} (M : Matroid α)
    (D C : Set α) (hDC : Disjoint D C) :
    M ＼ D ／ C = M ／ C ＼ D := by
  rw [M.contract_delete_comm hDC.symm]

/-- Manuscript duality law (N134): duality exchanges deletion and
contraction on the original element labels. -/
theorem deletion_dual_eq_contraction {α : Type*} (M : Matroid α)
    (D : Set α) : (M ＼ D)✶ = M✶ ／ D := M.dual_delete D

/-- The converse duality law of N134. -/
theorem contraction_dual_eq_deletion {α : Type*} (M : Matroid α)
    (C : Set α) : (M ／ C)✶ = M✶ ＼ C := M.dual_contract C

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
