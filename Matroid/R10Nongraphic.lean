import Matroid.External.R10Nongraphic

/-! N225: transfer the exact published binary R10 obstruction to the
manuscript's real TU realization on the original ten labels. -/

namespace Matroid

universe u

theorem r10_not_graphic_or_cographic :
    ¬ r10.IsGraphic.{u,0} ∧ ¬ r10.IsCographic.{u,0} := by
  simpa [r10_eq_binary] using
    (External.binaryR10_not_graphic_or_cographic.{u})

end Matroid
