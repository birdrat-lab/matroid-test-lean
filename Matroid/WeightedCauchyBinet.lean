import Matroid.TotallyUnimodular

/-! Weighted Gram determinant calculations for finite rectangular matrices. -/

namespace Matrix

/-- Increasing enumeration of a finite column subset of prescribed size. -/
noncomputable def orderedColumnIndex {k n : ℕ}
    (s : {S : Finset (Fin n) // S.card = k}) : Fin k → Fin n :=
  fun i => ((s.1.orderIsoOfFin s.2) i).1

theorem orderedColumnIndex_injective {k n : ℕ}
    (s : {S : Finset (Fin n) // S.card = k}) :
    Function.Injective (orderedColumnIndex s) := by
  intro i j hij
  exact (s.1.orderIsoOfFin s.2).injective (Subtype.ext hij)

theorem orderedColumnIndex_image {k n : ℕ}
    (s : {S : Finset (Fin n) // S.card = k}) :
    Finset.univ.image (orderedColumnIndex s) = s.1 := by
  classical
  ext j
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact ((s.1.orderIsoOfFin s.2) i).2
  · intro hj
    let e := s.1.orderIsoOfFin s.2
    refine ⟨e.symm ⟨j, hj⟩, ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply ⟨j, hj⟩)

theorem exists_orderedColumnIndex_comp_perm {k n : ℕ}
    (p : Fin k → Fin n) (hp : Function.Injective p) :
    ∃ (s : {S : Finset (Fin n) // S.card = k})
      (σ : Equiv.Perm (Fin k)), p = orderedColumnIndex s ∘ σ := by
  classical
  let S : Finset (Fin n) := Finset.univ.image p
  have hcard : S.card = k := by
    simpa [S] using Finset.card_image_of_injective Finset.univ hp
  let s : {S : Finset (Fin n) // S.card = k} := ⟨S, hcard⟩
  let q : Fin k → S := fun i => ⟨p i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hq : Function.Bijective q := by
    constructor
    · intro i j hij
      exact hp (congrArg Subtype.val hij)
    · intro j
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp j.2
      exact ⟨i, Subtype.ext hi⟩
  let e : Fin k ≃ S := Equiv.ofBijective q hq
  let σ : Equiv.Perm (Fin k) := e.trans (s.1.orderIsoOfFin s.2).symm.toEquiv
  refine ⟨s, σ, ?_⟩
  funext i
  exact congrArg Subtype.val
    ((s.1.orderIsoOfFin s.2).apply_symm_apply (e i)).symm

/-- The entries of a weighted Gram matrix are weighted column-pair sums. -/
theorem weightedGram_apply {r c R : Type*} [CommRing R]
    [Fintype c] [DecidableEq c] (A : Matrix r c R) (w : c → R)
    (i j : r) :
    (A * diagonal w * Aᵀ) i j = ∑ e : c, A i e * w e * A j e := by
  change (∑ e : c, (A * diagonal w) i e * A j e) = _
  simp only [Matrix.mul_diagonal, mul_assoc]

/-- The first, permutation-indexed expansion of rectangular weighted
Cauchy–Binet. The remaining step groups injective maps by their image. -/
theorem weightedGram_det_expansion {c R : Type*} [CommRing R]
    [Fintype c] [DecidableEq c] (k : ℕ)
    (A : Matrix (Fin k) c R) (w : c → R) :
    (A * diagonal w * Aᵀ).det =
      ∑ p : Fin k → c, ∑ σ : Equiv.Perm (Fin k),
        (Equiv.Perm.sign σ : R) * ∏ i : Fin k,
          A (σ i) (p i) * w (p i) * A i (p i) := by
  classical
  simp only [Matrix.det_apply', weightedGram_apply,
    Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]

/-- A first Cauchy–Binet reduction: sum over ordered row-size choices of
columns, before quotienting those choices by permutation. -/
theorem weightedGram_det_sum_minor {c R : Type*} [CommRing R]
    [Fintype c] [DecidableEq c] (k : ℕ)
    (A : Matrix (Fin k) c R) (w : c → R) :
    (A * diagonal w * Aᵀ).det =
      ∑ p : Fin k → c,
        (A.submatrix id p).det *
          ∏ i : Fin k, w (p i) * A i (p i) := by
  classical
  rw [weightedGram_det_expansion]
  apply Finset.sum_congr rfl
  intro p _
  simp_rw [show ∀ σ : Equiv.Perm (Fin k),
      (∏ i : Fin k, A (σ i) (p i) * w (p i) * A i (p i)) =
        (∏ i : Fin k, A (σ i) (p i)) *
          (∏ i : Fin k, w (p i) * A i (p i)) from by
      intro σ
      simp_rw [mul_assoc]
      rw [← Finset.prod_mul_distrib]]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  simp only [Matrix.det_apply', Matrix.submatrix_apply, id_eq]

/-- Repeated columns make an ordered maximal minor vanish. -/
theorem det_submatrix_eq_zero_of_not_injective
    {c K : Type*} [Field K] {k : ℕ}
    (A : Matrix (Fin k) c K) (p : Fin k → c)
    (hp : ¬ Function.Injective p) :
    (A.submatrix id p).det = 0 := by
  apply Matrix.det_eq_zero_of_not_linearIndependent_cols
  intro hLI
  apply hp
  intro i j hij
  apply hLI.injective
  ext x
  simp [Matrix.col_apply, Matrix.submatrix_apply, hij]

/-- The ordered expansion may be restricted to injective column choices;
every repeated-column determinant vanishes. -/
theorem weightedGram_det_sum_injective {c K : Type*} [Field K]
    [Fintype c] [DecidableEq c] (k : ℕ)
    (A : Matrix (Fin k) c K) (w : c → K) :
    (A * diagonal w * Aᵀ).det =
      ∑ p : Fin k → c with Function.Injective p,
        (A.submatrix id p).det *
          ∏ i : Fin k, w (p i) * A i (p i) := by
  rw [weightedGram_det_sum_minor]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hnot
  have hni : ¬ Function.Injective p := by
    simpa using hnot
  rw [det_submatrix_eq_zero_of_not_injective A p hni]
  simp

/-- A single fiber of the column-choice sum, indexed by permutations of a
fixed choice, collapses to the square of its minor. -/
theorem weightedGram_permutation_fiber {c K : Type*} [Field K]
    [DecidableEq c] {k : ℕ} (A : Matrix (Fin k) c K)
    (w : c → K) (p : Fin k → c) :
    (∑ σ : Equiv.Perm (Fin k),
      (A.submatrix id (p ∘ σ)).det *
        ∏ i : Fin k, w (p (σ i)) * A i (p (σ i))) =
      (A.submatrix id p).det ^ 2 * ∏ i : Fin k, w (p i) := by
  let B := A.submatrix id p
  have hdet (σ : Equiv.Perm (Fin k)) :
      (A.submatrix id (p ∘ σ)).det =
        (Equiv.Perm.sign σ : K) * B.det := by
    simpa [B, Matrix.submatrix_submatrix] using Matrix.det_permute' σ B
  have hw (σ : Equiv.Perm (Fin k)) :
      (∏ i : Fin k, w (p (σ i))) = ∏ i : Fin k, w (p i) := by
    exact Equiv.prod_comp σ (fun i => w (p i))
  have hdet' : B.det = ∑ σ : Equiv.Perm (Fin k),
      (Equiv.Perm.sign σ : K) * ∏ i : Fin k, A i (p (σ i)) := by
    rw [← Matrix.det_transpose B, Matrix.det_apply']
    simp [B, Matrix.transpose_apply, Matrix.submatrix_apply]
  calc
    (∑ σ : Equiv.Perm (Fin k),
      (A.submatrix id (p ∘ σ)).det *
        ∏ i : Fin k, w (p (σ i)) * A i (p (σ i))) =
        ∑ σ : Equiv.Perm (Fin k),
          B.det * (∏ i : Fin k, w (p i)) *
            ((Equiv.Perm.sign σ : K) * ∏ i : Fin k, A i (p (σ i))) := by
              apply Finset.sum_congr rfl
              intro σ _
              rw [hdet]
              rw [Finset.prod_mul_distrib, hw σ]
              ring
    _ = B.det * (∏ i : Fin k, w (p i)) *
          (∑ σ : Equiv.Perm (Fin k),
            (Equiv.Perm.sign σ : K) * ∏ i : Fin k, A i (p (σ i))) := by
          rw [Finset.mul_sum]
    _ = (A.submatrix id p).det ^ 2 * ∏ i : Fin k, w (p i) := by
          rw [← hdet']
          dsimp [B]
          ring

/-- Injective ordered column choices are uniquely a subset of size `k`
together with a permutation of its increasing enumeration. -/
theorem sum_injective_eq_sum_ordered_permutations
    {k n : ℕ} {R : Type*} [AddCommMonoid R]
    (F : (Fin k → Fin n) → R) :
    (∑ p : Fin k → Fin n with Function.Injective p, F p) =
      ∑ s : {S : Finset (Fin n) // S.card = k},
        ∑ σ : Equiv.Perm (Fin k), F (orderedColumnIndex s ∘ σ) := by
  classical
  have hprod :
      (∑ s : {S : Finset (Fin n) // S.card = k},
        ∑ σ : Equiv.Perm (Fin k), F (orderedColumnIndex s ∘ σ)) =
      ∑ x : {S : Finset (Fin n) // S.card = k} × Equiv.Perm (Fin k),
        F (orderedColumnIndex x.1 ∘ x.2) :=
    (Fintype.sum_prod_type
      (fun x : {S : Finset (Fin n) // S.card = k} × Equiv.Perm (Fin k) =>
        F (orderedColumnIndex x.1 ∘ x.2))).symm
  rw [hprod]
  symm
  apply Finset.sum_bij
    (fun x _ => orderedColumnIndex x.1 ∘ x.2)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (orderedColumnIndex_injective x.1).comp x.2.injective
  · intro x hx y hy hxy
    rcases x with ⟨s, σ⟩
    rcases y with ⟨t, ρ⟩
    have himage (u : {S : Finset (Fin n) // S.card = k})
        (π : Equiv.Perm (Fin k)) :
        Finset.univ.image (orderedColumnIndex u ∘ π) = u.1 := by
      rw [Finset.image_comp,
        Finset.image_univ_of_surjective π.surjective,
        orderedColumnIndex_image]
    have hst : s = t := Subtype.ext (by
      calc
        s.1 = Finset.univ.image (orderedColumnIndex s ∘ σ) := (himage s σ).symm
        _ = Finset.univ.image (orderedColumnIndex t ∘ ρ) :=
          congrArg (fun p : Fin k → Fin n => Finset.univ.image p) hxy
        _ = t.1 := himage t ρ)
    subst t
    have hσρ : σ = ρ := Equiv.ext (fun i =>
      orderedColumnIndex_injective s (congrFun hxy i))
    exact Prod.ext rfl hσρ
  · intro p hp
    have hpinj : Function.Injective p := by simpa using hp
    obtain ⟨s, σ, h⟩ := exists_orderedColumnIndex_comp_perm p hpinj
    refine ⟨(s, σ), Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_⟩
    exact h.symm
  · intro x hx
    rfl

/-- Rectangular weighted Cauchy--Binet, with maximal minors indexed by
finite column subsets. The identity holds over every field. -/
theorem weightedCauchyBinet {k n : ℕ} {K : Type*} [Field K]
    (A : Matrix (Fin k) (Fin n) K) (w : Fin n → K) :
    (A * diagonal w * Aᵀ).det =
      ∑ s : {S : Finset (Fin n) // S.card = k},
        (A.submatrix id (orderedColumnIndex s)).det ^ 2 *
          ∏ j ∈ s.1, w j := by
  classical
  rw [weightedGram_det_sum_injective]
  rw [sum_injective_eq_sum_ordered_permutations]
  apply Finset.sum_congr rfl
  intro s _
  have h := weightedGram_permutation_fiber A w (orderedColumnIndex s)
  have hw : (∏ i : Fin k, w (orderedColumnIndex s i)) =
      ∏ j ∈ s.1, w j := by
    rw [← orderedColumnIndex_image s]
    exact (Finset.prod_image (orderedColumnIndex_injective s).injOn).symm
  simpa only [Function.comp_def, hw] using h

/-- The square instance follows from determinant multiplicativity. A
rectangular proof additionally requires grouping the maximal minors. -/
theorem weightedGram_det_square {r R : Type*} [CommRing R]
    [Fintype r] [DecidableEq r] (A : Matrix r r R) (w : r → R) :
    (A * diagonal w * Aᵀ).det = A.det ^ 2 * ∏ i, w i := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_transpose]
  ring

end Matrix
