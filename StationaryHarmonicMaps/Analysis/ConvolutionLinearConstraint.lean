module

public import HarmonicMaps.Analysis.MollificationConvolution
public import Mathlib.MeasureTheory.Group.IntegralConvolution

/-!
# Actual convolution preserves linear almost-everywhere constraints

The genuine compact-kernel integrand is integrable. Translation and
reflection preserve null sets, so the original almost-everywhere linear
constraint holds at all sampled points almost everywhere in the integration
variable. Commuting the actual continuous linear map with the Bochner
integral gives the constraint at every output point.
-/

public section

open HarmonicMaps MeasureTheory Filter

namespace StationaryHarmonicMaps.Analysis

/-- A genuine compact continuous convolution satisfies every original linear zero constraint at every point. -/
theorem kernelConvolution_preserves_linear_kernel {n m k : ℕ}
    (f : Domain n → Ambient m) (hf : Integrable f volume)
    (L : Ambient m →L[ℝ] Ambient k)
    (hZero : ∀ᵐ y ∂volume, L (f y) = 0)
    (χ : Domain n → ℝ) (hχ : Continuous χ) (hcχ : HasCompactSupport χ) :
    ∀ x : Domain n, L (∫ z, χ z • f (x-z)) = 0 := by
  intro x
  have hI : Integrable (fun z => χ z • f (x-z)) volume :=
    (hcχ.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hχ hf.locallyIntegrable x).integrable
  have hSample := (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae hZero
  calc
    _ = ∫ z, L (χ z • f (x-z)) := (L.integral_comp_comm hI).symm
    _ = ∫ _z : Domain n, (0 : Ambient k) := by
      apply integral_congr_ae
      filter_upwards [hSample] with z hz
      rw [map_smul,hz,smul_zero]
    _ = 0 := by simp only [integral_zero]

end StationaryHarmonicMaps.Analysis

end
