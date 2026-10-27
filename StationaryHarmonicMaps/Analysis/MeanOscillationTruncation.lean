module

public import StationaryHarmonicMaps.Analysis.MeanOscillationContraction

/-!
# Actual bounded truncations with controlled mean oscillation

The literal symmetric truncation is a contraction. Its pointwise bounds
and eventual equality to each fixed value give bounded approximants
with uniform mean oscillation and genuine pointwise convergence.
-/

public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace StationaryHarmonicMaps.Analysis

/-- The literal symmetric truncation is a contraction and obeys both actual absolute-value bounds. -/
theorem symmetric_truncation_lipschitz_bounds (R : ℝ) (hR : 0≤R) :
    LipschitzWith 1 (fun t : ℝ=>min R (max (-R) t)) ∧
      ∀ t : ℝ,|min R (max (-R) t)|≤R ∧ |min R (max (-R) t)|≤|t| := by
  refine ⟨(LipschitzWith.id.const_max (-R)).const_min R,?_⟩
  intro t
  by_cases ht : t< -R
  · rw [max_eq_left ht.le,min_eq_right (by linarith only [hR])]
    rw [abs_neg,abs_of_nonneg hR]
    exact ⟨le_rfl,by have H := neg_le_abs t;linarith only [ht,H]⟩
  · rw [max_eq_right (le_of_not_gt ht)]
    by_cases htR : t≤R
    · rw [min_eq_right htR]
      exact ⟨abs_le.mpr ⟨le_of_not_gt ht,htR⟩,le_rfl⟩
    · rw [min_eq_left (le_of_not_ge htR),abs_of_nonneg hR]
      exact ⟨le_rfl,(le_of_not_ge htR).trans (le_abs_self t)⟩

/-- Original integrability produces bounded truncations with uniformly controlled original mean oscillation. -/
theorem integrable_symmetric_truncation_mean_oscillation_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [NeZero μ]
    (f : X → ℝ) (hf : Integrable f μ) (R : ℝ) (hR : 0≤R) :
    Integrable (fun x=>min R (max (-R) (f x))) μ ∧
      (⨍ x,|min R (max (-R) (f x))-(⨍ y,min R (max (-R) (f y)) ∂μ)| ∂μ)≤
        2*(⨍ x,|f x-(⨍ y,f y ∂μ)| ∂μ) := by
  have hLip := (symmetric_truncation_lipschitz_bounds R hR).1
  exact ⟨integrable_lipschitz_comp_finite μ f hf _ 1 hLip,by
    simpa only [NNReal.coe_one,mul_one] using mean_oscillation_lipschitz_comp_le μ f hf _ 1 hLip⟩

/-- For every original value the same literal truncation eventually equals that value as the truncation levels tend to infinity. -/
theorem eventually_symmetric_truncation_eq {I : Type*} (l : Filter I)
    (R : I → ℝ) (hR : Tendsto R l atTop) (t : ℝ) :
    ∀ᶠ i in l,min (R i) (max (-(R i)) t)=t := by
  filter_upwards [hR.eventually_ge_atTop |t|] with i hi
  have hLower : -(R i)≤t := by have H := neg_abs_le t;linarith only [hi,H]
  have hUpper : t≤R i := (le_abs_self t).trans hi
  rw [max_eq_right hLower,min_eq_right hUpper]

end StationaryHarmonicMaps.Analysis

end
