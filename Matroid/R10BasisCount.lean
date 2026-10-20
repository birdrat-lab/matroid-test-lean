import Matroid.R10Automorphism

/-! Exact kernel-checked basis counts and pointed monomial supports for
the displayed R10 on its original ten labels. -/

namespace Matroid

/-- The decidable family of every basis on the ten original labels. -/
def r10BasisFamilyCert : Finset (Finset (Fin 10)) :=
  Finset.univ.filter r10BasisCert

/-- The finite acceptance predicate contains precisely the matroid bases;
no representation-specific bases are silently substituted. -/
theorem mem_r10BasisFamilyCert_iff (B : Finset (Fin 10)) :
    B ∈ r10BasisFamilyCert ↔ r10.IsBase (B : Set (Fin 10)) := by
  simp [r10BasisFamilyCert, r10_isBase_iff_cert]

/-- Every accepted basis has the manuscript's rank-five size. -/
theorem r10BasisFamilyCert_card_five
    (B : Finset (Fin 10)) (hB : B ∈ r10BasisFamilyCert) :
    B.card = 5 := by
  exact (Finset.mem_filter.mp hB).2.1

/- N182: all 252 rank-five candidates are checked against the exact binary
basis predicate, so this finite reduction needs a larger heartbeat budget. -/
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 16384 in
theorem r10_basis_count : r10BasisFamilyCert.card = 162 := by
  decide

/- N183: the complete finite certificate checks every distinguished label,
using the same original-label basis predicate as N182. -/
set_option maxHeartbeats 30000000 in
set_option maxRecDepth 16384 in
theorem r10_pointed_basis_in_count :
    ∀ e : Fin 10, (r10BasisFamilyCert.filter (fun B => e ∈ B)).card = 81 := by
  decide

/-- Exactly 81 R10 bases omit any given displayed label. -/
theorem r10_pointed_basis_out_count (e : Fin 10) :
    (r10BasisFamilyCert.filter (fun B => e ∉ B)).card = 81 := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := r10BasisFamilyCert) (fun B => e ∈ B)
  rw [r10_pointed_basis_in_count e, r10_basis_count] at hsplit
  omega

/-- The square-free monomial supports of the two pointed R10 sums. The
target is removed from every containing basis before forming its monomial. -/
def r10PointedOutSupport (e : Fin 10) : Finset (Finset (Fin 10)) :=
  r10BasisFamilyCert.filter (fun B => e ∉ B)

def r10PointedInSupport (e : Fin 10) : Finset (Finset (Fin 10)) :=
  (r10BasisFamilyCert.filter (fun B => e ∈ B)).image (fun B => B.erase e)

theorem r10PointedOutSupport_card (e : Fin 10) :
    (r10PointedOutSupport e).card = 81 :=
  r10_pointed_basis_out_count e

theorem r10PointedInSupport_card (e : Fin 10) :
    (r10PointedInSupport e).card = 81 := by
  classical
  rw [r10PointedInSupport, Finset.card_image_of_injOn]
  · exact r10_pointed_basis_in_count e
  · intro B hB C hC hErase
    change B.erase e = C.erase e at hErase
    have heB : e ∈ B := (Finset.mem_filter.mp hB).2
    have heC : e ∈ C := (Finset.mem_filter.mp hC).2
    calc
      B = insert e (B.erase e) := (Finset.insert_erase heB).symm
      _ = insert e (C.erase e) := by rw [hErase]
      _ = C := Finset.insert_erase heC

theorem r10PointedOutSupport_degree (e : Fin 10)
    (B : Finset (Fin 10)) (hB : B ∈ r10PointedOutSupport e) :
    B.card = 5 ∧ e ∉ B := by
  exact ⟨r10BasisFamilyCert_card_five B (Finset.mem_filter.mp hB).1,
    (Finset.mem_filter.mp hB).2⟩

theorem r10PointedInSupport_degree (e : Fin 10)
    (S : Finset (Fin 10)) (hS : S ∈ r10PointedInSupport e) :
    S.card = 4 ∧ e ∉ S := by
  classical
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hS
  have heB : e ∈ B := (Finset.mem_filter.mp hB).2
  have hcard := r10BasisFamilyCert_card_five B (Finset.mem_filter.mp hB).1
  have herase := Finset.card_erase_add_one heB
  exact ⟨by omega, by simp⟩

end Matroid
