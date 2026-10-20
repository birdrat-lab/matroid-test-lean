import Matroid.R10Transitivity
import Matroid.R10CircuitParity
import Mathlib.Combinatorics.Matroid.Map

/-! Exact finite type whose cardinality is the N185 manuscript claim.
The 720-element certificate is still missing; these declarations provide
the faithful proof target and preserve the original ten labels. -/

namespace Matroid

/-- A permutation is an R10 automorphism exactly when it preserves the
entire labeled matroid, not merely a chosen collection of generators. -/
def IsR10Automorphism (σ : Equiv.Perm (Fin 10)) : Prop :=
  r10.mapEquiv σ = r10

/-- The exact finite automorphism type underlying the order-720 claim. -/
def R10Automorphism := {σ : Equiv.Perm (Fin 10) // IsR10Automorphism σ}

/-- The manuscript's order-720 assertion is `r10AutomorphismCount = 720`.
No numerical value is asserted by this definition. -/
noncomputable def r10AutomorphismCount : ℕ := Nat.card R10Automorphism

theorem isR10Automorphism_refl : IsR10Automorphism (Equiv.refl (Fin 10)) := by
  simp [IsR10Automorphism, mapEquiv_eq_map]

/-- An exact basis-level acceptance criterion for a prospective finite
automorphism certificate. It checks all bases on the original ten labels. -/
theorem isR10Automorphism_iff_preserves_bases
    (σ : Equiv.Perm (Fin 10)) :
    IsR10Automorphism σ ↔
      ∀ B : Set (Fin 10), r10.IsBase B ↔ r10.IsBase (σ.symm '' B) := by
  constructor
  · intro h B
    have hB : (r10.mapEquiv σ).IsBase B ↔ r10.IsBase B := by
      rw [h]
    simpa only [mapEquiv_isBase_iff] using hB.symm
  · intro h
    apply ext_isBase
    · simp [r10_ground]
    · intro B _
      simpa only [mapEquiv_isBase_iff] using (h B).symm

/-- The same exact criterion indexed by the finite collection of subsets of
the displayed ten-element ground. This is the finite-checker interface. -/
theorem isR10Automorphism_iff_finset_bases
    (σ : Equiv.Perm (Fin 10)) :
    IsR10Automorphism σ ↔
      ∀ B : Finset (Fin 10),
        r10.IsBase (B : Set (Fin 10)) ↔
          r10.IsBase (σ.symm '' (B : Set (Fin 10))) := by
  rw [isR10Automorphism_iff_preserves_bases]
  constructor
  · intro h B
    exact h B
  · intro h B
    have hfin : B.Finite := Set.toFinite B
    simpa only [Set.Finite.coe_toFinset] using h hfin.toFinset

/-- A computable independence test on the displayed binary matrix. Every
nonempty subset is checked, so duplicate or zero columns are handled. -/
def r10IndependentCert (B : Finset (Fin 10)) : Prop :=
  ∀ C : Finset (Fin 10), C ⊆ B → C.Nonempty →
    ∑ e ∈ C, r10BinaryMatrix.col e ≠ 0

instance (B : Finset (Fin 10)) : Decidable (r10IndependentCert B) := by
  unfold r10IndependentCert
  infer_instance

/-- The decidable finite test is exactly matroid independence, by the
binary cycle characterization rather than a sample of circuits. -/
theorem r10_indep_iff_cert (B : Finset (Fin 10)) :
    r10.Indep (B : Set (Fin 10)) ↔ r10IndependentCert B := by
  have hrep : r10.Represents (K := ZMod 2) r10BinaryMatrix.col := by
    rw [r10_eq_binary]
    exact vectorMatroid_represents _ _ _
  constructor
  · intro hI C hCB hCne hsum
    have hCE : (C : Set (Fin 10)) ⊆ r10.E := by simp
    have hcycle : r10.IsCircuitUnion (C : Set (Fin 10)) :=
      (isCircuitUnion_iff_binary_sum_eq_zero r10BinaryMatrix.col hrep hCE).2
        (by simpa [Set.Finite.toFinset] using hsum)
    have hEmpty := hcycle.eq_empty_of_subset_indep hI (by
      simpa using hCB)
    have : C = ∅ := by
      apply Finset.coe_injective
      simpa using hEmpty
    exact hCne.ne_empty this
  · intro hCert
    by_contra hI
    have hBE : (B : Set (Fin 10)) ⊆ r10.E := by simp
    obtain ⟨C, hCB, hC⟩ :=
      ((r10.not_indep_iff hBE).mp hI).exists_isCircuit_subset
    let hfin : C.Finite := r10.ground_finite.subset hC.subset_ground
    let c : Finset (Fin 10) := hfin.toFinset
    have hcB : c ⊆ B := by
      intro e he
      have heC : e ∈ C := by simpa [c] using he
      exact hCB heC
    have hcne : c.Nonempty := by
      obtain ⟨e, he⟩ := hC.nonempty
      exact ⟨e, by simpa [c] using he⟩
    have hsum : ∑ e ∈ c, r10BinaryMatrix.col e = 0 :=
      hrep.binaryCircuit_sum_zero r10BinaryMatrix.col hC
    exact (hCert c hcB hcne) hsum

/-- Computable basis test using the exact rank-five binary matrix. -/
def r10BasisCert (B : Finset (Fin 10)) : Prop :=
  B.card = 5 ∧ r10IndependentCert B

instance (B : Finset (Fin 10)) : Decidable (r10BasisCert B) := by
  unfold r10BasisCert
  infer_instance

theorem r10_isBase_iff_cert (B : Finset (Fin 10)) :
    r10.IsBase (B : Set (Fin 10)) ↔ r10BasisCert B := by
  rw [r10BasisCert]
  constructor
  · intro hB
    have hcard : (B.card : ℕ∞) = 5 := by
      simpa using hB.encard_eq_eRank.trans r10_eRank
    exact ⟨by exact_mod_cast hcard, (r10_indep_iff_cert B).1 hB.indep⟩
  · rintro ⟨hcard, hCert⟩
    have hI : r10.Indep (B : Set (Fin 10)) :=
      (r10_indep_iff_cert B).2 hCert
    apply hI.isBase_of_eRk_ge (by exact Finset.finite_toSet B)
    rw [r10_eRank, hI.eRk_eq_encard]
    simp [hcard]

/-- A completely decidable acceptance predicate for the fixed-label
automorphism count. The exhaustive cardinality certificate is still open. -/
def r10AutomorphismCert (σ : Equiv.Perm (Fin 10)) : Prop :=
  ∀ B : Finset (Fin 10),
    r10BasisCert B ↔ r10BasisCert (B.image σ.symm)

instance (σ : Equiv.Perm (Fin 10)) : Decidable (r10AutomorphismCert σ) := by
  unfold r10AutomorphismCert
  infer_instance

theorem isR10Automorphism_iff_cert (σ : Equiv.Perm (Fin 10)) :
    IsR10Automorphism σ ↔ r10AutomorphismCert σ := by
  rw [isR10Automorphism_iff_finset_bases]
  constructor <;> intro h B
  · have himage : (B.image σ.symm : Set (Fin 10)) = σ.symm '' (B : Set (Fin 10)) := by
      simp
    simpa only [← himage, r10_isBase_iff_cert] using h B
  · have himage : (B.image σ.symm : Set (Fin 10)) = σ.symm '' (B : Set (Fin 10)) := by
      simp
    simpa only [← himage, r10_isBase_iff_cert] using h B

end Matroid
