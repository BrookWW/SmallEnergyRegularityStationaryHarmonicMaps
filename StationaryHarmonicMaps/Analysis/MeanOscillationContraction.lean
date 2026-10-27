module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Mean oscillation under an actual Lipschitz composition

On each genuine finite nonzero measure, subtracting the actual mean
costs at most twice subtraction of any fixed constant. An actual
Lipschitz composition is integrable and therefore preserves mean
oscillation up to twice its Lipschitz constant.
-/

public section

open MeasureTheory Filter Set
open scoped NNReal

namespace StationaryHarmonicMaps.Analysis

/-- The actual mean minimizes absolute oscillation up to the factor two. -/
theorem mean_oscillation_le_twice_centered_average {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [NeZero μ]
    (f : X → ℝ) (hf : Integrable f μ) (c : ℝ) :
    (⨍ x,|f x-(⨍ y,f y ∂μ)| ∂μ)≤2*(⨍ x,|f x-c| ∂μ) := by
  let m := ⨍ y,f y ∂μ
  have hError : Integrable (fun x=>f x-c) μ := hf.sub (integrable_const c)
  have hMean : |m-c|≤⨍ x,|f x-c| ∂μ := by
    have hEq : m-c=⨍ x,f x-c ∂μ := by
      change (⨍ y,f y ∂μ)-c=⨍ x,f x-c ∂μ
      calc
        _ = (⨍ y,f y ∂μ)-(⨍ _x,c ∂μ) := by rw [average_const]
        _ = _ := (integral_sub hf.to_average (integrable_const c)).symm
    rw [hEq]
    exact abs_integral_le_integral_abs
  have hPoint (x : X) : |f x-m|≤|f x-c|+|m-c| := by
    calc
      _ = |(f x-c)-(m-c)| := by congr 1;ring
      _ ≤ _ := abs_sub _ _
  calc
    _ ≤ ⨍ x,|f x-c|+|m-c| ∂μ := integral_mono
      (hf.sub (integrable_const m)).abs.to_average
      (hError.abs.add (integrable_const _)).to_average hPoint
    _ = (⨍ x,|f x-c| ∂μ)+|m-c| := by
      calc
        _ = (⨍ x,|f x-c| ∂μ)+(⨍ _x,|m-c| ∂μ) :=
          integral_add hError.abs.to_average (integrable_const _)
        _ = _ := by rw [average_const]
    _ ≤ 2*(⨍ x,|f x-c| ∂μ) := by linarith only [hMean]

/-- Original local integrability and an actual Lipschitz map produce the genuine composed integrability. -/
theorem integrable_lipschitz_comp_finite {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) (hf : Integrable f μ)
    (φ : ℝ → ℝ) (K : ℝ≥0) (hφ : LipschitzWith K φ) :
    Integrable (fun x=>φ (f x)) μ := by
  have hBound (x : X) : ‖φ (f x)‖≤(K : ℝ)*|f x|+|φ 0| := by
    calc
      _ ≤ ‖φ (f x)-φ 0‖+‖φ 0‖ := norm_le_norm_sub_add _ _
      _ ≤ (K : ℝ)*|f x|+|φ 0| := by
        apply add_le_add _ le_rfl
        simpa only [sub_zero,Real.norm_eq_abs] using hφ.norm_sub_le (f x) 0
  exact ((hf.abs.const_mul (K : ℝ)).add (integrable_const |φ 0|)).mono'
    (hφ.continuous.comp_aestronglyMeasurable hf.aestronglyMeasurable)
    (Eventually.of_forall hBound)

/-- The actual composed mean oscillation is controlled by the original mean oscillation, without a composed-integrability premise. -/
theorem mean_oscillation_lipschitz_comp_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [NeZero μ]
    (f : X → ℝ) (hf : Integrable f μ)
    (φ : ℝ → ℝ) (K : ℝ≥0) (hφ : LipschitzWith K φ) :
    (⨍ x,|φ (f x)-(⨍ y,φ (f y) ∂μ)| ∂μ)≤
      2*(K : ℝ)*(⨍ x,|f x-(⨍ y,f y ∂μ)| ∂μ) := by
  have hI := integrable_lipschitz_comp_finite μ f hf φ K hφ
  apply (mean_oscillation_le_twice_centered_average μ (fun x=>φ (f x)) hI
    (φ (⨍ y,f y ∂μ))).trans
  have hBound : (⨍ x,|φ (f x)-φ (⨍ y,f y ∂μ)| ∂μ)≤
      (K : ℝ)*(⨍ x,|f x-(⨍ y,f y ∂μ)| ∂μ) := by
    calc
      _ ≤ ⨍ x,(K : ℝ)*|f x-(⨍ y,f y ∂μ)| ∂μ := integral_mono
        (hI.sub (integrable_const _)).abs.to_average
        ((hf.sub (integrable_const _)).abs.const_mul (K : ℝ)).to_average
        (fun x=>by
          change |φ (f x)-φ (⨍ y,f y ∂μ)|≤(K : ℝ)*|f x-(⨍ y,f y ∂μ)|
          simpa only [Real.norm_eq_abs] using hφ.norm_sub_le (f x) (⨍ y,f y ∂μ))
      _ = _ := integral_const_mul _ _
  nlinarith only [hBound]

end StationaryHarmonicMaps.Analysis

end
