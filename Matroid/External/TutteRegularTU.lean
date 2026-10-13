import Matroid.Regular
import Matroid.TotallyUnimodular

/-! # Cited finite regular-matroid representation theorem

James Oxley, *Briefly, What Is a Matroid?*, Definition 4.3 and Lemma 4.4,
https://www.math.lsu.edu/~oxley/matroid_intro_summ.pdf, p. 10, attributes
the regular iff real-TU-matrix characterization to Tutte (1958). The
matrix below is indexed by the finite *actual ground set* `M.E`; its column
matroid has the same independent sets on those labels. There is exactly one
external admission in this file. No manuscript-local assertion is admitted.
-/

namespace Matroid.External

universe u

/-- The regular-to-TU half of Tutte's finite theorem, stated on the exact
finite ground-label type. All later extension to ambient labels and field
transport is proved in project files. -/
theorem regular_ground_exists_realTU {α : Type u} {M : Matroid α}
    [M.Finite] (hM : M.Regular.{u,0,0}) :
    ∃ (r : Type) (_ : Fintype r) (A : Matrix r M.E ℝ),
      A.IsTotallyUnimodular ∧
      ∀ J : Set M.E,
        M.Indep (Subtype.val '' J) ↔
          LinearIndependent ℝ (fun j : J => A.col j.1) := by
  sorry

end Matroid.External
