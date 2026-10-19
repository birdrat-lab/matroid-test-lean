import Matroid.RegularTUConverse

/-! # Cited projective uniqueness of binary matroids

James Oxley, *Matroid Theory* (2nd ed., 2011), Proposition 6.6.5,
printed p. 209, attributes this theorem to Brylawski and Lucas (1976).
Oxley's §6.3, printed pp. 176–178, defines projective equivalence as
row operations and nonzero column scalings without a field automorphism;
Proposition 6.3.12 gives the matrix form. The rank-zero case is explicitly
treated as the all-zero representation on printed p. 177.

The statement below specializes the source theorem to real representations,
retains every element label (including parallel elements and loops), and
uses isomorphism of the two column spans to allow arbitrary ambient vector
spaces. `ProjectivelyEquivalent` supplies the precise span isomorphism and
nonzero scaling on nonloops. This is the single admitted N055 premise.
-/

namespace Matroid.External

universe u v w

theorem binary_real_projective_uniqueness
    {α : Type u} {V : Type v} {W : Type w}
    [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W]
    {M : Matroid α} [M.Finite]
    (hbinary : RepresentableOver.{u, 0, 0} (ZMod 2) M)
    {φ : α → V} {ψ : α → W}
    (hφ : M.Represents (K := ℝ) φ)
    (hψ : M.Represents (K := ℝ) ψ) :
    M.ProjectivelyEquivalent (K := ℝ) φ ψ := by
  sorry

end Matroid.External
