module

public import StationaryHarmonicMaps.Analysis.DyadicBallMaximal
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Actual finite ball averages from an original finite moment

The original p-moment with p at least one controls every fixed ball
integral by its finite volume plus the original moment. Only the genuine
finite dyadic windows are therefore finite at every center. Finiteness
of a full supremum is a separate almost-everywhere conclusion.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- The original finite p-moment produces a genuinely finite average on every fixed positive-radius ball. -/
theorem centeredBallAverageENN_ne_top_of_moment {n : ℕ}
    (f : Domain n → ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p)
    (hfin : (∫⁻ y, (f y)^p) < ∞) (x : Domain n) (r : PositiveRadius) :
    centeredBallAverageENN f x r ≠ ∞ := by
  have hpoint (y : Domain n) : f y ≤ 1+(f y)^p := by
    by_cases hy : f y ≤ 1
    · exact hy.trans (le_add_of_nonneg_right zero_le)
    · exact (ENNReal.le_rpow_self_of_one_le (le_of_lt (lt_of_not_ge hy)) hp).trans
        (le_add_of_nonneg_left zero_le)
  have hbound : (∫⁻ y in Metric.ball x r.val, f y) ≤
      volume (Metric.ball x r.val) + ∫⁻ y, (f y)^p := by
    calc
      _ ≤ ∫⁻ y in Metric.ball x r.val, 1+(f y)^p := lintegral_mono hpoint
      _ = volume (Metric.ball x r.val) + ∫⁻ y in Metric.ball x r.val, (f y)^p := by
        rw [lintegral_add_left measurable_const _,lintegral_const]
        simp only [Measure.restrict_apply MeasurableSet.univ,univ_inter,one_mul]
      _ ≤ _ := by
        have H : (∫⁻ y in Metric.ball x r.val, (f y)^p) ≤ ∫⁻ y, (f y)^p := by
          simpa only [Measure.restrict_univ] using lintegral_mono_set
            (f := fun y => (f y)^p) (μ := volume) (subset_univ (Metric.ball x r.val))
        exact add_le_add le_rfl H
  have hI : (∫⁻ y in Metric.ball x r.val, f y) < ∞ := hbound.trans_lt
    (ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr measure_ball_ne_top,hfin⟩)
  exact (ENNReal.mul_lt_top
    (ENNReal.inv_lt_top.mpr (Metric.measure_ball_pos volume x r.property)) hI).ne

/-- Every actual finite dyadic window is finite at every center before any real conversion. -/
theorem dyadicBallMaximalWindow_ne_top_of_moment {n : ℕ}
    (f : Domain n → ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p)
    (hfin : (∫⁻ y, (f y)^p) < ∞) (N : ℕ) (x : Domain n) :
    dyadicBallMaximalWindow f N x ≠ ∞ := by
  apply ne_of_lt
  apply (Finset.sup_lt_iff (by simp : (⊥ : ℝ≥0∞)<∞)).mpr
  intro j _hj
  exact lt_top_iff_ne_top.mpr (centeredBallAverageENN_ne_top_of_moment f hp hfin x
    ⟨(2 : ℝ)^j,zpow_pos (by norm_num) j⟩)

/-- A genuine measurable finite positive moment gives almost-everywhere finite original values. -/
theorem ae_ne_top_of_finite_positive_moment {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ≥0∞) (hf : AEMeasurable f μ)
    {p : ℝ} (hp : 0 < p) (hfin : (∫⁻ y, (f y)^p ∂μ) < ∞) :
    ∀ᵐ y ∂μ, f y ≠ ∞ := by
  have hmp : AEMeasurable (fun y => (f y)^p) μ :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hf
  have hAE := ae_lt_top' hmp hfin.ne
  filter_upwards [hAE] with y hy
  intro htop
  rw [htop,ENNReal.top_rpow_of_pos hp] at hy
  exact lt_irrefl _ hy

end StationaryHarmonicMaps.Analysis

end
