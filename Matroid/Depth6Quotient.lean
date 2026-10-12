import Matroid.Representation
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! Indexed free generators and relation contraction for the quotient normal form. -/

open Set

namespace Matroid

variable {K : Type*} [Field K] {β ρ : Type*} [Fintype β] [Fintype ρ]

/-- Coordinate vectors for the free target/response labels and adjoined
relation labels. The latter may be arbitrarily dependent. -/
noncomputable def freeRelationVector (r : ρ → β →₀ K) : β ⊕ ρ → β →₀ K
  | Sum.inl b => Finsupp.single b 1
  | Sum.inr x => r x

/-- The represented matroid before all relation elements are contracted. -/
noncomputable def freeRelationMatroid (r : ρ → β →₀ K) : Matroid (β ⊕ ρ) :=
  vectorMatroid (K := K) Set.univ Set.finite_univ (freeRelationVector r)

/-- N243: all free coordinate generators remain independent after relation
elements are adjoined, including coordinates unused by any relation. -/
theorem freeRelation_generators_indep (r : ρ → β →₀ K) :
    (freeRelationMatroid r).Indep (Set.range Sum.inl) := by
  rw [freeRelationMatroid, vectorMatroid_indep_iff]
  constructor
  · exact Set.subset_univ _
  · have hli : LinearIndependent K (fun b : β => Finsupp.single b (1 : K)) :=
      Finsupp.linearIndependent_single_one K β
    have hinj : Function.Injective (Sum.inl : β → β ⊕ ρ) := Sum.inl_injective
    exact (linearIndepOn_range_iff hinj (freeRelationVector r)).2
      (by convert hli using 1; funext b; rfl)

/-- N243: adjoining arbitrarily dependent relation vectors does not change
the fact that the free target and response coordinates form a basis. -/
theorem freeRelation_generators_isBase (r : ρ → β →₀ K) :
    (freeRelationMatroid r).IsBase (Set.range Sum.inl) := by
  apply (isBase_iff_indep_closure_eq).2
  constructor
  · exact freeRelation_generators_indep r
  · have hspan : Submodule.span K
        (freeRelationVector r '' Set.range (Sum.inl : β → β ⊕ ρ)) = ⊤ := by
      have hb := (Finsupp.basisSingleOne (R := K) (ι := β)).span_eq
      rw [← Set.range_comp]
      simpa [Function.comp_def, freeRelationVector, Finsupp.coe_basisSingleOne] using hb
    apply subset_antisymm
    · exact (freeRelationMatroid r).closure_subset_ground _
    · intro e he
      change e ∈ (vectorMatroid (K := K) Set.univ Set.finite_univ
        (freeRelationVector r)).closure (Set.range Sum.inl)
      have hrep := vectorMatroid_represents (K := K) Set.univ
        Set.finite_univ (freeRelationVector r)
      have h := (hrep.mem_closure_iff_mem_span
        (A := Set.range (Sum.inl : β → β ⊕ ρ)) (e := e)
        (by intro x hx; exact Set.mem_univ x) (by simp))
      exact h.2 (by rw [hspan]; trivial)

/-- The span of the adjoined labeled relation columns is exactly the
relation space, regardless of dependencies among the columns. -/
theorem freeRelation_relation_span (r : ρ → β →₀ K) :
    Submodule.span K (freeRelationVector r '' Set.range (Sum.inr : ρ → β ⊕ ρ)) =
      Submodule.span K (Set.range r) := by
  rw [← Set.range_comp]
  rfl

/-- The surviving labels after contracting all relation labels are exactly
the original free target and response labels. -/
theorem freeRelation_contract_ground (r : ρ → β →₀ K) :
    (freeRelationMatroid r ／ Set.range Sum.inr).E = Set.range Sum.inl := by
  rw [contract_ground]
  change Set.univ \ Set.range (Sum.inr : ρ → β ⊕ ρ) =
    Set.range (Sum.inl : β → β ⊕ ρ)
  ext e
  cases e with
  | inl b => simp
  | inr x => simp

/-- N246: contracting every relation label realizes the quotient by their
span on exactly the surviving free labels. No independence of relations is
assumed. -/
theorem freeRelation_contract_eq_quotient (r : ρ → β →₀ K) :
    freeRelationMatroid r ／ Set.range Sum.inr =
      vectorMatroid (K := K) (Set.range (Sum.inl : β → β ⊕ ρ))
        (Set.finite_range _) (fun e =>
          (Submodule.Quotient.mk (p := Submodule.span K (Set.range r)))
            (freeRelationVector r e)) := by
  have hrep := vectorMatroid_represents (K := K) Set.univ
    Set.finite_univ (freeRelationVector r)
  have hcontract := hrep.contract
    (A := Set.range (Sum.inr : ρ → β ⊕ ρ)) (by simp)
  have heq := hcontract.eq_vectorMatroid
  rw [freeRelation_relation_span] at heq
  have hground :
      (vectorMatroid (K := K) Set.univ Set.finite_univ (freeRelationVector r) ／
        Set.range (Sum.inr : ρ → β ⊕ ρ)).E =
          Set.range (Sum.inl : β → β ⊕ ρ) := freeRelation_contract_ground r
  simpa only [hground, freeRelationMatroid] using heq

/-- N247: an explicit reconstruction modulo the relation span puts the
target in the closure of the available coordinate generators. -/
theorem freeRelation_positive_closure (r : ρ → β →₀ K)
    (τ : β) (A : Set β) (hcertificate :
      ∃ v ∈ Submodule.span K
          ((fun b : β => Finsupp.single b (1 : K)) '' A),
        Finsupp.single τ (1 : K) - v ∈ Submodule.span K (Set.range r)) :
    Sum.inl τ ∈ (freeRelationMatroid r ／ Set.range Sum.inr).closure
      ((Sum.inl : β → β ⊕ ρ) '' A) := by
  rw [freeRelation_contract_eq_quotient]
  let U := Submodule.span K (Set.range r)
  let q : (β →₀ K) →ₗ[K] (β →₀ K) ⧸ U := U.mkQ
  let φ : β ⊕ ρ → (β →₀ K) ⧸ U := fun e => q (freeRelationVector r e)
  have hrep := vectorMatroid_represents (K := K)
    (Set.range (Sum.inl : β → β ⊕ ρ)) (Set.finite_range _) φ
  have hAground : (Sum.inl : β → β ⊕ ρ) '' A ⊆
      Set.range (Sum.inl : β → β ⊕ ρ) := Set.image_subset_range _ _
  apply (hrep.mem_closure_iff_mem_span hAground (by simp)).2
  rcases hcertificate with ⟨v, hv, hdiff⟩
  have hq : q (Finsupp.single τ (1 : K)) = q v := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact (Submodule.Quotient.mk_eq_zero U).2 hdiff
  have hvq : q v ∈ Submodule.span K
      (q '' ((fun b : β => Finsupp.single b (1 : K)) '' A)) :=
    Submodule.apply_mem_span_image_of_mem_span q hv
  have himage : φ '' ((Sum.inl : β → β ⊕ ρ) '' A) =
      q '' ((fun b : β => Finsupp.single b (1 : K)) '' A) := by
    ext z
    simp [φ, freeRelationVector]
  change φ (Sum.inl τ) ∈ Submodule.span K
    (φ '' ((Sum.inl : β → β ⊕ ρ) '' A))
  rw [himage]
  simpa [φ, freeRelationVector, hq] using hvq

/-- The manuscript's positive relation equation supplies the certificate in
`freeRelation_positive_closure` for each positive input label. -/
theorem freeRelation_positive_closure_of_equation (r : ρ → β →₀ K)
    (τ : β) (A : Set β) (x : ρ) (v : β →₀ K)
    (hv : v ∈ Submodule.span K
      ((fun b : β => Finsupp.single b (1 : K)) '' A))
    (hr : r x = Finsupp.single τ (1 : K) - v) :
    Sum.inl τ ∈ (freeRelationMatroid r ／ Set.range Sum.inr).closure
      ((Sum.inl : β → β ⊕ ρ) '' A) := by
  apply freeRelation_positive_closure r τ A
  exact ⟨v, hv, hr ▸ Submodule.subset_span (Set.mem_range_self x)⟩

/-- N248: a functional annihilating every relation and every available
response, but not the target, certifies target nonclosure after contraction. -/
theorem freeRelation_negative_nonclosure (r : ρ → β →₀ K)
    (τ : β) (A : Set β) (ℓ : (β →₀ K) →ₗ[K] K)
    (hrel : ∀ x : ρ, ℓ (r x) = 0)
    (hA : ∀ b ∈ A, ℓ (Finsupp.single b (1 : K)) = 0)
    (hτ : ℓ (Finsupp.single τ (1 : K)) ≠ 0) :
    Sum.inl τ ∉ (freeRelationMatroid r ／ Set.range Sum.inr).closure
      ((Sum.inl : β → β ⊕ ρ) '' A) := by
  rw [freeRelation_contract_eq_quotient]
  let U := Submodule.span K (Set.range r)
  have hU : U ≤ LinearMap.ker ℓ := by
    apply Submodule.span_le.mpr
    rintro v ⟨x, rfl⟩
    exact hrel x
  let ℓq : ((β →₀ K) ⧸ U) →ₗ[K] K := U.liftQ ℓ hU
  let φ : β ⊕ ρ → (β →₀ K) ⧸ U := fun e => U.mkQ (freeRelationVector r e)
  have hrep := vectorMatroid_represents (K := K)
    (Set.range (Sum.inl : β → β ⊕ ρ)) (Set.finite_range _) φ
  have hAground : (Sum.inl : β → β ⊕ ρ) '' A ⊆
      Set.range (Sum.inl : β → β ⊕ ρ) := Set.image_subset_range _ _
  intro hcl
  have hspan := (hrep.mem_closure_iff_mem_span hAground (by simp)).1 hcl
  have hspanKer : Submodule.span K
      (φ '' ((Sum.inl : β → β ⊕ ρ) '' A)) ≤ LinearMap.ker ℓq := by
    apply Submodule.span_le.mpr
    rintro v ⟨e, ⟨b, hb, rfl⟩, rfl⟩
    simpa [φ, freeRelationVector, ℓq] using hA b hb
  have hzero : ℓq (φ (Sum.inl τ)) = 0 := hspanKer hspan
  exact hτ (by simpa [φ, freeRelationVector, ℓq] using hzero)

end Matroid
