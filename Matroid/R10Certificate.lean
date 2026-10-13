import Matroid.R10
import Matroid.Regular
import Matroid.TotallyUnimodular
import Mathlib.Data.Finset.Sort
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
/-! A kernel-checked finite TU certificate for the exact displayed R10 matrix.
The 5×5 nonbasis block has 252 canonical square minors: 1 of size zero,
25 of size one, 100 each of sizes two and three, 25 of size four, and 1
of size five. `decide` checks these fixed finite determinants; a proved
permutation bridge covers every injective minor indexing. Mathlib's
identity-column theorem then restores the full 5×10 matrix. -/

open Matrix
namespace Matroid
def r10NonbasisBlock : Matrix (Fin 5) (Fin 5) ℤ := r10IntegerMatrix.submatrix id (Fin.natAdd 5)
private def enum2 : Fin 10 → (Fin 2 → Fin 5)
  | 0 => ![0,1]
  | 1 => ![0,2]
  | 2 => ![0,3]
  | 3 => ![0,4]
  | 4 => ![1,2]
  | 5 => ![1,3]
  | 6 => ![1,4]
  | 7 => ![2,3]
  | 8 => ![2,4]
  | 9 => ![3,4]
private theorem cover2 : ∀ f : Fin 2 → Fin 5, StrictMono f → ∃ u : Fin 10, f = enum2 u := by decide
private theorem cert2 : ∀ u v : Fin 10, |(r10NonbasisBlock.submatrix (enum2 u) (enum2 v)).det| ≤ 1 := by decide
private def enum3 : Fin 10 → (Fin 3 → Fin 5)
  | 0 => ![0,1,2]
  | 1 => ![0,1,3]
  | 2 => ![0,1,4]
  | 3 => ![0,2,3]
  | 4 => ![0,2,4]
  | 5 => ![0,3,4]
  | 6 => ![1,2,3]
  | 7 => ![1,2,4]
  | 8 => ![1,3,4]
  | 9 => ![2,3,4]
private theorem cover3 : ∀ f : Fin 3 → Fin 5, StrictMono f → ∃ u : Fin 10, f = enum3 u := by decide
private theorem cert3 : ∀ u v : Fin 10, |(r10NonbasisBlock.submatrix (enum3 u) (enum3 v)).det| ≤ 1 := by decide
private def enum4 : Fin 5 → (Fin 4 → Fin 5)
  | 0 => ![0,1,2,3]
  | 1 => ![0,1,2,4]
  | 2 => ![0,1,3,4]
  | 3 => ![0,2,3,4]
  | 4 => ![1,2,3,4]
private theorem cover4 : ∀ f : Fin 4 → Fin 5, StrictMono f → ∃ u : Fin 5, f = enum4 u := by decide
private theorem cert4 : ∀ u v : Fin 5, |(r10NonbasisBlock.submatrix (enum4 u) (enum4 v)).det| ≤ 1 := by decide
private theorem cert0 : ∀ f g : Fin 0 → Fin 5, StrictMono f → StrictMono g → |(r10NonbasisBlock.submatrix f g).det| ≤ 1 := by decide
private theorem cert1 : ∀ f g : Fin 1 → Fin 5, StrictMono f → StrictMono g → |(r10NonbasisBlock.submatrix f g).det| ≤ 1 := by decide
private theorem cert5 : ∀ f g : Fin 5 → Fin 5, StrictMono f → StrictMono g → |(r10NonbasisBlock.submatrix f g).det| ≤ 1 := by
  intro f g hf hg
  have hf' := hf.eq_id
  have hg' := hg.eq_id
  subst f
  subst g
  decide
private theorem sorted_minor (k : ℕ) (hk : k ≤ 5) :
    ∀ (f g : Fin k → Fin 5), StrictMono f → StrictMono g →
      |(r10NonbasisBlock.submatrix f g).det| ≤ 1 := by
  interval_cases k
  · exact cert0
  · exact cert1
  · intro f g hf hg
    obtain ⟨u, rfl⟩ := cover2 f hf
    obtain ⟨v, rfl⟩ := cover2 g hg
    exact cert2 u v
  · intro f g hf hg
    obtain ⟨u, rfl⟩ := cover3 f hf
    obtain ⟨v, rfl⟩ := cover3 g hg
    exact cert3 u v
  · intro f g hf hg
    obtain ⟨u, rfl⟩ := cover4 f hf
    obtain ⟨v, rfl⟩ := cover4 g hg
    exact cert4 u v
  · exact cert5
private theorem abs_det_canon (A : Matrix (Fin 5) (Fin 5) ℤ)
    {k : ℕ} (f g : Fin k → Fin 5) (hf : Function.Injective f)
    (hg : Function.Injective g) :
    let s := Finset.univ.image f
    let t := Finset.univ.image g
    ∀ (hs : s.card = k) (ht : t.card = k),
      |(A.submatrix f g).det| =
        |(A.submatrix (s.orderEmbOfFin hs) (t.orderEmbOfFin ht)).det| := by
  intro s t hs ht
  let ef : Fin k ≃ s := Equiv.ofBijective
    (fun i => (⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩ : s))
    (by
      constructor
      · intro i j h
        exact hf (congrArg Subtype.val h)
      · intro x
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp x.2
        exact ⟨i, Subtype.ext hi⟩)
  let eg : Fin k ≃ t := Equiv.ofBijective
    (fun i => (⟨g i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩ : t))
    (by
      constructor
      · intro i j h
        exact hg (congrArg Subtype.val h)
      · intro x
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp x.2
        exact ⟨i, Subtype.ext hi⟩)
  let sf : Fin k ≃ Fin k := ef.trans (s.orderIsoOfFin hs).symm.toEquiv
  let sg : Fin k ≃ Fin k := eg.trans (t.orderIsoOfFin ht).symm.toEquiv
  have hfactor_f : f = (s.orderEmbOfFin hs) ∘ sf := by
    funext i
    change f i = (s.orderIsoOfFin hs (sf i)).1
    simp [sf, ef]
    rfl
  have hfactor_g : g = (t.orderEmbOfFin ht) ∘ sg := by
    funext i
    change g i = (t.orderIsoOfFin ht (sg i)).1
    simp [sg, eg]
    rfl
  rw [hfactor_f, hfactor_g]
  change |((A.submatrix (s.orderEmbOfFin hs) (t.orderEmbOfFin ht)).submatrix sf sg).det| = _
  exact Matrix.abs_det_submatrix_equiv_equiv sf sg _

theorem r10NonbasisBlock_isTotallyUnimodular : r10NonbasisBlock.IsTotallyUnimodular := by
  intro k f g hf hg
  have hk : k ≤ 5 := by simpa using Fintype.card_le_of_injective f hf
  let s : Finset (Fin 5) := Finset.univ.image f
  let t : Finset (Fin 5) := Finset.univ.image g
  have hs : s.card = k := by
    rw [Finset.card_image_of_injective _ hf]
    simp
  have ht : t.card = k := by
    rw [Finset.card_image_of_injective _ hg]
    simp
  have hcanonical := abs_det_canon r10NonbasisBlock f g hf hg hs ht
  have hbound : |(r10NonbasisBlock.submatrix f g).det| ≤ 1 := by
    rw [hcanonical]
    exact sorted_minor k hk (s.orderEmbOfFin hs) (t.orderEmbOfFin ht)
      (s.orderEmbOfFin hs).strictMono (t.orderEmbOfFin ht).strictMono
  have hbounds : -(1 : ℤ) ≤ (r10NonbasisBlock.submatrix f g).det ∧ (r10NonbasisBlock.submatrix f g).det ≤ 1 :=
    abs_le.mp hbound
  have hcases : (r10NonbasisBlock.submatrix f g).det = -1 ∨
      (r10NonbasisBlock.submatrix f g).det = 0 ∨ (r10NonbasisBlock.submatrix f g).det = 1 := by omega
  rcases hcases with h | h | h
  · exact ⟨(-1 : SignType), by simp [h]⟩
  · exact ⟨(0 : SignType), by simp [h]⟩
  · exact ⟨(1 : SignType), by simp [h]⟩

theorem r10IntegerMatrix_reindexed_eq :
    r10IntegerMatrix.reindex (Equiv.refl (Fin 5))
      (finSumFinEquiv (m := 5) (n := 5)).symm =
        Matrix.fromCols (1 : Matrix (Fin 5) (Fin 5) ℤ) r10NonbasisBlock := by
  ext i j
  cases j with
  | inl k =>
      have h := congrArg (fun X : Matrix (Fin 5) (Fin 5) ℤ => X i k)
        r10IntegerMatrix_left
      change r10IntegerMatrix i (Fin.castAdd 5 k) = (1 : Matrix (Fin 5) (Fin 5) ℤ) i k
      exact h
  | inr k =>
      change r10IntegerMatrix i (Fin.natAdd 5 k) = r10NonbasisBlock i k
      rfl

theorem r10IntegerMatrix_isTotallyUnimodular : r10IntegerMatrix.IsTotallyUnimodular := by
  have hcols : (Matrix.fromCols (1 : Matrix (Fin 5) (Fin 5) ℤ) r10NonbasisBlock).IsTotallyUnimodular :=
    (Matrix.one_fromCols_isTotallyUnimodular_iff r10NonbasisBlock).2 r10NonbasisBlock_isTotallyUnimodular
  rw [← r10IntegerMatrix_reindexed_eq] at hcols
  exact (Matrix.reindex_isTotallyUnimodular r10IntegerMatrix
    (Equiv.refl (Fin 5)) (finSumFinEquiv (m := 5) (n := 5)).symm).1 hcols

theorem r10Matrix_isTotallyUnimodular : r10Matrix.IsTotallyUnimodular := by
  intro k f g hf hg
  obtain ⟨s, hs⟩ := r10IntegerMatrix_isTotallyUnimodular k f g hf hg
  refine ⟨s, ?_⟩
  have hcast := congrArg (fun z : ℤ => (z : ℝ)) hs
  change (s : ℝ) = ((r10IntegerMatrix.submatrix f g).map (Int.castRingHom ℝ)).det
  simpa [Int.cast_det] using hcast

universe v
theorem r10_regular : r10.Regular.{0,v,v} := by
  unfold r10
  intro K _
  obtain ⟨B, hB, hBA, hEq⟩ :=
    vectorMatroid_realTU_represents_over_field (K := K)
      r10Matrix r10Matrix_isTotallyUnimodular Set.univ Set.finite_univ
  refine ⟨Fin 5 → K, inferInstance, inferInstance,
    (B.map fun z : ℤ => (z : K)).col, ?_⟩
  rw [hEq]
  exact vectorMatroid_represents Set.univ Set.finite_univ _
end Matroid
