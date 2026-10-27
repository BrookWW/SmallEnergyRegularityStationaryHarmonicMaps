module

public import HarmonicMaps.Sobolev
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Variance identity on Euclidean balls

For an L2 map, the integral of the squared distance from its average is
half the normalized double integral of pairwise squared distances.
-/

public section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace HarmonicMaps

section FiniteMeasure

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] (μ : Measure α) [IsFiniteMeasure μ]

omit [InnerProductSpace ℝ E] in
/-- Pairwise squared distances of an L2 map are integrable on the product measure. -/
theorem integrable_sq_norm_sub_prod {f : α → E} (hf : MemLp f 2 μ) :
    Integrable (fun p : α × α => ‖f p.1 - f p.2‖ ^ 2) (μ.prod μ) := by
  have hd : MemLp (fun p : α × α => f p.1 - f p.2) 2 (μ.prod μ) :=
    (hf.comp_fst μ).sub (hf.comp_snd μ)
  exact (memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).mp hd

omit [InnerProductSpace ℝ E] in
/-- The inner integral of pairwise squared distances is integrable. -/
theorem integrable_integral_sq_norm_sub {f : α → E} (hf : MemLp f 2 μ) :
    Integrable (fun x => ∫ y, ‖f x - f y‖ ^ 2 ∂μ) μ :=
  (integrable_sq_norm_sub_prod μ hf).integral_prod_left

variable [CompleteSpace E]

private theorem integral_sq_norm_sub_of_integral_eq_zero {g : α → E}
    (hg : MemLp g 2 μ) (hzero : (∫ y, g y ∂μ) = 0) (a : E) :
    (∫ y, ‖a - g y‖ ^ 2 ∂μ) =
      μ.real univ * ‖a‖ ^ 2 + ∫ y, ‖g y‖ ^ 2 ∂μ := by
  have hgi : Integrable g μ := hg.integrable (by norm_num)
  have hgsq : Integrable (fun y => ‖g y‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hi : Integrable (fun y => 2 * inner ℝ a (g y)) μ :=
    (hgi.const_inner a).const_mul 2
  have hsub : Integrable (fun y => ‖a‖ ^ 2 - 2 * inner ℝ a (g y)) μ :=
    (integrable_const (‖a‖ ^ 2)).sub hi
  simp_rw [norm_sub_sq_real]
  rw [integral_add hsub hgsq,
    integral_sub (integrable_const (‖a‖ ^ 2)) hi, integral_const_mul, integral_inner hgi,
    hzero, inner_zero_right, mul_zero, sub_zero, integral_const, smul_eq_mul]

/-- Variance of an L2 map with respect to a finite nonzero measure. -/
theorem integral_sq_norm_sub_average_eq_doubleIntegral {f : α → E}
    (hμ : μ ≠ 0) (hf : MemLp f 2 μ) :
    (∫ x, ‖f x - ⨍ y, f y ∂μ‖ ^ 2 ∂μ) =
      (1 / (2 * μ.real univ)) * ∫ x, ∫ y, ‖f x - f y‖ ^ 2 ∂μ ∂μ := by
  let g : α → E := fun x => f x - ⨍ y, f y ∂μ
  have hg : MemLp g 2 μ := hf.sub (memLp_const _)
  have hzero : (∫ y, g y ∂μ) = 0 := integral_sub_average μ f
  have hgsq : Integrable (fun x => ‖g x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hdiff (x y : α) : f x - f y = g x - g y := by
    dsimp [g]
    abel
  have hdouble : (∫ x, ∫ y, ‖f x - f y‖ ^ 2 ∂μ ∂μ) =
      2 * μ.real univ * ∫ x, ‖g x‖ ^ 2 ∂μ := by
    simp_rw [hdiff, integral_sq_norm_sub_of_integral_eq_zero μ hg hzero]
    rw [integral_add (hgsq.const_mul _) (integrable_const _),
      integral_const_mul, integral_const, smul_eq_mul]
    ring
  have hmass : μ.real univ ≠ 0 :=
    (ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hμ) (measure_ne_top μ univ)).ne'
  rw [hdouble]
  change (∫ x, ‖g x‖ ^ 2 ∂μ) = _
  field_simp

end FiniteMeasure

/-- Pairwise squared distances of an L2 map on a ball are integrable. -/
theorem integrable_sq_norm_sub_prod_ball {n q : ℕ} (a : Domain n) {r : ℝ}
    {f : Domain n → Ambient q}
    (hf : MemLp f 2 (volume.restrict (Metric.ball a r))) :
    Integrable (fun p : Domain n × Domain n => ‖f p.1 - f p.2‖ ^ 2)
      ((volume.restrict (Metric.ball a r)).prod (volume.restrict (Metric.ball a r))) := by
  letI : IsFiniteMeasure (volume.restrict (Metric.ball a r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  exact integrable_sq_norm_sub_prod (volume.restrict (Metric.ball a r)) hf

/-- The pairwise-distance integral is integrable over the outer ball. -/
theorem integrable_integral_sq_norm_sub_ball {n q : ℕ} (a : Domain n) {r : ℝ}
    {f : Domain n → Ambient q}
    (hf : MemLp f 2 (volume.restrict (Metric.ball a r))) :
    IntegrableOn (fun x => ∫ y in Metric.ball a r, ‖f x - f y‖ ^ 2)
      (Metric.ball a r) volume := by
  exact (integrable_sq_norm_sub_prod_ball a hf).integral_prod_left

/-- The vector-valued variance identity on a ball of positive radius. -/
theorem integral_sq_norm_sub_average_ball_eq_doubleIntegral {n q : ℕ}
    (a : Domain n) {r : ℝ} (hr : 0 < r) {f : Domain n → Ambient q}
    (hf : MemLp f 2 (volume.restrict (Metric.ball a r))) :
    (∫ x in Metric.ball a r, ‖f x - ⨍ y in Metric.ball a r, f y‖ ^ 2) =
      (1 / (2 * volume.real (Metric.ball a r))) *
        ∫ x in Metric.ball a r, ∫ y in Metric.ball a r, ‖f x - f y‖ ^ 2 := by
  letI : IsFiniteMeasure (volume.restrict (Metric.ball a r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hμ : volume.restrict (Metric.ball a r) ≠ 0 := by
    intro h
    have hpos := Metric.measure_ball_pos volume a hr
    have hz : volume (Metric.ball a r) = 0 := by
      simpa only [Measure.restrict_apply_univ, Measure.coe_zero, Pi.zero_apply] using
        congrArg (fun ν => ν univ) h
    exact hpos.ne' hz
  simpa only [measureReal_restrict_apply_univ] using
    integral_sq_norm_sub_average_eq_doubleIntegral
      (volume.restrict (Metric.ball a r)) hμ hf

end HarmonicMaps

end
