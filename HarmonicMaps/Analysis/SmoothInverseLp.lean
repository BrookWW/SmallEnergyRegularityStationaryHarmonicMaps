module

public import HarmonicMaps.Analysis.InnerVariationMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Finite Lp pullbacks by smooth inverse maps on balls

The forward Jacobian is bounded on the compact closed ball. The change of
variables estimate therefore bounds the inverse pushforward measure by a
finite multiple of the original restricted Lebesgue measure.
-/

public section

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace HarmonicMaps

/-- The inverse pushforward on a preserved ball is dominated by a finite
multiple of restricted volume, derived from the actual smooth Jacobian. -/
theorem smooth_inverse_map_restrict_le {n : ℕ} {a : Domain n} {R : ℝ}
    {f g : Domain n → Domain n} (hf : ContDiff ℝ ∞ f) (hg : Continuous g)
    (hfg : Function.RightInverse g f) (hgf : Function.LeftInverse g f)
    (hfball : MapsTo f (Metric.ball a R) (Metric.ball a R))
    (hgball : MapsTo g (Metric.ball a R) (Metric.ball a R)) :
    ∃ C : ℝ≥0∞, C ≠ (⊤ : ℝ≥0∞) ∧ Measure.map g (volume.restrict (Metric.ball a R)) ≤
      C • volume.restrict (Metric.ball a R) := by
  have hdet : Continuous (fun x => (fderiv ℝ f x).det) :=
    ContinuousLinearMap.continuous_det.comp (hf.continuous_fderiv (by simp))
  obtain ⟨C, hC⟩ := (isCompact_closedBall a R).exists_bound_of_continuousOn hdet.continuousOn
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, Measure.le_iff.mpr ?_⟩
  intro s hs
  rw [Measure.map_apply hg.measurable hs, Measure.restrict_apply (hg.measurable hs)]
  have heq : g ⁻¹' s ∩ Metric.ball a R = f '' (s ∩ Metric.ball a R) := by
    ext x
    constructor
    · rintro ⟨hx, hxB⟩
      exact ⟨g x, ⟨hx, hgball hxB⟩, hfg x⟩
    · rintro ⟨y, ⟨hy, hyB⟩, rfl⟩
      exact ⟨by change g (f y) ∈ s; rw [hgf y]; exact hy, hfball hyB⟩
  rw [heq]
  calc
    volume (f '' (s ∩ Metric.ball a R)) ≤
        ∫⁻ x in s ∩ Metric.ball a R, ENNReal.ofReal |(fderiv ℝ f x).det| :=
      addHaar_image_le_lintegral_abs_det_fderiv volume (hs.inter measurableSet_ball)
        (fun x _ => (hf.differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt)
    _ ≤ ∫⁻ _ in s ∩ Metric.ball a R, ENNReal.ofReal C := by
      apply setLIntegral_mono' (hs.inter measurableSet_ball)
      intro x hx
      apply ENNReal.ofReal_le_ofReal
      exact (Real.norm_eq_abs _ ▸ hC x (Metric.ball_subset_closedBall hx.2))
    _ = (ENNReal.ofReal C • volume.restrict (Metric.ball a R)) s := by
      rw [lintegral_const, Measure.restrict_apply_univ, Measure.smul_apply,
        Measure.restrict_apply hs, smul_eq_mul]

/-- Actual finite Lp membership survives smooth inverse composition on a
preserved ball; its measure bound is proved internally. -/
theorem memLp_comp_smooth_inverse_ball {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {a : Domain n} {R : ℝ} {p : ℝ≥0∞} {u : Domain n → E}
    (hu : MemLp u p (volume.restrict (Metric.ball a R)))
    {f g : Domain n → Domain n} (hf : ContDiff ℝ ∞ f) (hg : Continuous g)
    (hfg : Function.RightInverse g f) (hgf : Function.LeftInverse g f)
    (hfball : MapsTo f (Metric.ball a R) (Metric.ball a R))
    (hgball : MapsTo g (Metric.ball a R) (Metric.ball a R)) :
    MemLp (u ∘ g) p (volume.restrict (Metric.ball a R)) := by
  obtain ⟨C, hC, hbound⟩ := smooth_inverse_map_restrict_le hf hg hfg hgf hfball hgball
  exact ((hu.smul_measure hC).mono_measure hbound).comp_of_map hg.measurable.aemeasurable

end HarmonicMaps
