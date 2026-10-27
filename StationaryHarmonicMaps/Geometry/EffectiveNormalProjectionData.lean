module

public import StationaryHarmonicMaps.Geometry.C2ProjectionGlobalExtension
public import StationaryHarmonicMaps.Geometry.NormalProjectionProperties
public import Mathlib.Data.Rat.Cast.Order

/-!
# Rational derivative bounds for actual geometric extensions

Every compact C² embedded target admits a compactly supported C¹ ambient
extension of its normal projection and a nonnegative rational bound for
its derivative. Numerical data for a specified embedding can certify this
bound and then evaluate the rational stationary regularity constants.
-/

public section
open scoped ContDiff
namespace StationaryHarmonicMaps.CompactC2EmbeddedTarget

theorem exists_rational_normal_projection_derivative_bound {q : ℕ}
    (N : CompactC2EmbeddedTarget q) :
    ∃ (G : EuclideanSpace ℝ (Fin q) →
        (EuclideanSpace ℝ (Fin q) →L[ℝ] EuclideanSpace ℝ (Fin q))) (L : ℚ),
      ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
      (∀ p : N.Carrier,G p.val=N.normalProjection p) ∧
      0≤L ∧ ∀ y,‖fderiv ℝ G y‖≤(L:ℝ) := by
  obtain ⟨G,L,hG,hcG,hGN,_hL,hDG⟩ :=
    N.exists_global_ambient_normal_projection_extension_bounded_derivative
  obtain ⟨k,hk⟩ := exists_nat_gt L
  refine ⟨G,(k:ℚ),hG,hcG,?_,Nat.cast_nonneg k,?_⟩
  · intro p
    exact (hGN p).trans (N.normalProjection_eq_starProjection p).symm
  · intro y
    exact (hDG y).trans (by exact_mod_cast hk.le)

end StationaryHarmonicMaps.CompactC2EmbeddedTarget
end
