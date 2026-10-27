module

public import HarmonicMaps.Energy
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# Positive-radius scaling of normalized sphere area

The normalized Euclidean Hausdorff measure has its exact dimensional scaling
on sphere restrictions. Consequently the canonical polar identification at
unit radius implies the same identification at every positive radius. The
unit-radius identification is an explicit input of this conditional helper.
-/

public section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace HarmonicMaps

/-- Dilating the unit-sphere restriction with its dimensional weight gives
exactly the normalized Euclidean Hausdorff measure on the new sphere. -/
theorem sphereSurface_map_scaled_restrict {n : ℕ} (d : ℕ) (R : PositiveRadius) :
    Measure.map (fun x : Domain n => R.val • x)
      (ENNReal.ofReal (R.val ^ d) •
        (Measure.euclideanHausdorffMeasure d : Measure (Domain n)).restrict
          (Metric.sphere (0 : Domain n) 1)) =
      (Measure.euclideanHausdorffMeasure d : Measure (Domain n)).restrict
        (Metric.sphere (0 : Domain n) R.val) := by
  have hscale (s : Set (Domain n)) :
      (Measure.euclideanHausdorffMeasure d : Measure (Domain n)) (R.val • s) =
        ENNReal.ofReal (R.val ^ d) *
          (Measure.euclideanHausdorffMeasure d : Measure (Domain n)) s := by
    rw [Measure.euclideanHausdorffMeasure_smul₀ d R.property.ne', ENNReal.smul_def,
      smul_eq_mul, ENNReal.coe_pow, ENNReal.ofReal_pow R.property.le]
    congr 1
    exact congrArg (fun t : ℝ≥0∞ => t ^ d) (Real.enorm_of_nonneg R.property.le)
  have himage (s : Set (Domain n)) :
      R.val • ((fun x : Domain n => R.val • x) ⁻¹' s ∩ Metric.sphere (0 : Domain n) 1) =
        s ∩ Metric.sphere (0 : Domain n) R.val := by
    ext x
    constructor
    · rintro ⟨y, ⟨hy, hys⟩, rfl⟩
      refine ⟨hy, ?_⟩
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_of_nonneg R.property.le]
      have hyunit : ‖y‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hys
      rw [hyunit, mul_one]
    · rintro ⟨hx, hxs⟩
      have hnorm : ‖x‖ = R.val := by simpa only [Metric.mem_sphere, dist_zero_right] using hxs
      have hrecover : R.val • (R.val⁻¹ • x) = x := by
        rw [smul_smul, mul_inv_cancel₀ R.property.ne', one_smul]
      refine ⟨R.val⁻¹ • x, ⟨?_, ?_⟩, hrecover⟩
      · simpa only [mem_preimage, hrecover] using hx
      · rw [Metric.mem_sphere, dist_zero_right, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.mpr R.property.le), hnorm,
          inv_mul_cancel₀ R.property.ne']
  have hm : Measurable (fun x : Domain n => R.val • x) :=
    (continuous_id.const_smul R.val).measurable
  rw [Measure.map_smul]
  ext s hs
  rw [Measure.smul_apply, Measure.map_apply hm hs, Measure.restrict_apply (hm hs),
    Measure.restrict_apply hs, ← himage s, hscale]
  rfl

/-- The genuine unit-sphere measure identity transports to every positive
radius with the canonical radius-to-the-dimension-minus-one weight. -/
theorem sphereSurface_scaledPolar_eq_of_unit {n : ℕ} (R : PositiveRadius)
    (hunit : Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => θ.val)
        (volume : Measure (Domain n)).toSphere =
      (Measure.euclideanHausdorffMeasure (n - 1) : Measure (Domain n)).restrict
        (Metric.sphere (0 : Domain n) 1)) :
    Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
      (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere) =
      (Measure.euclideanHausdorffMeasure (n - 1) : Measure (Domain n)).restrict
        (Metric.sphere (0 : Domain n) R.val) := by
  have hm : Measurable (fun x : Domain n => R.val • x) :=
    (continuous_id.const_smul R.val).measurable
  rw [Measure.map_smul]
  change ENNReal.ofReal (R.val ^ (n - 1)) •
    Measure.map ((fun x : Domain n => R.val • x) ∘
      (fun θ : Metric.sphere (0 : Domain n) 1 => θ.val))
      (volume : Measure (Domain n)).toSphere = _
  rw [← Measure.map_map hm measurable_subtype_coe, hunit, ← Measure.map_smul]
  exact sphereSurface_map_scaled_restrict (n - 1) R

end HarmonicMaps
end
