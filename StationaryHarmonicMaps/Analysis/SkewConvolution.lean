module

public import StationaryHarmonicMaps.Analysis.ConvolutionLinearConstraint
public import StationaryHarmonicMaps.Analysis.OperatorCoefficientCoordinates
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Actual skewness of decoded compact convolutions

The actual symmetric-part map is continuous linear. Its original
almost-everywhere zero constraint passes to every output point of the
genuine convolution. The true inverse coordinate law recovers skewness
of the original decoded operator, with no chosen representative or
derivative certificate.
-/

public section

open HarmonicMaps MeasureTheory Filter

namespace StationaryHarmonicMaps.Analysis

/-- A genuine compact convolution of an almost-everywhere skew encoded field decodes to a skew operator at every point. -/
theorem decoded_kernelConvolution_skew {n q : ℕ}
    (E : (Ambient q →L[ℝ] Ambient q) →L[ℝ] Ambient (q*q))
    (R : Ambient (q*q) →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (hRE : ∀ T, R (E T) = T)
    (f : Domain n → Ambient (q*q)) (hf : Integrable f volume)
    (hSkew : ∀ᵐ y ∂volume, star (R (f y)) = -R (f y))
    (χ : Domain n → ℝ) (hχ : Continuous χ) (hcχ : HasCompactSupport χ) :
    ∀ x : Domain n, star (R (∫ z, χ z • f (x-z))) = -R (∫ z, χ z • f (x-z)) := by
  let J : Ambient (q*q) →L[ℝ] Ambient (q*q) := E.comp
    (R + (starL' ℝ : (Ambient q →L[ℝ] Ambient q) ≃L[ℝ]
      (Ambient q →L[ℝ] Ambient q)).toContinuousLinearMap.comp R)
  have hJ (z : Ambient (q*q)) : J z = E (R z + star (R z)) := rfl
  have hZero : ∀ᵐ y ∂volume, J (f y) = 0 := by
    filter_upwards [hSkew] with y hy
    rw [hJ,hy,add_neg_cancel,map_zero]
  have H := kernelConvolution_preserves_linear_kernel f hf J hZero χ hχ hcχ
  intro x
  have Hx := H x
  rw [hJ] at Hx
  have hSym : R (∫ z, χ z • f (x-z)) + star (R (∫ z, χ z • f (x-z))) = 0 := by
    have Hr := congrArg R Hx
    simpa only [hRE,map_zero] using Hr
  exact eq_neg_of_add_eq_zero_right hSym

end StationaryHarmonicMaps.Analysis

end
