module

public import HarmonicMaps.Analysis.VariableMollificationPullbackEstimates
public import HarmonicMaps.Analysis.VariableMollificationTensor
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Jensen and Fubini for the literal variable averages

Restricted pushforward domination gives joint integrability. Actual weighted
joint integrals then give square-integrable kernel averages by Jensen.
-/

public section

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal ContDiff

namespace HarmonicMaps

/-- The fixed source kernel has unit mass on its actual averaging ball. -/
theorem fixedMollifierKernel_setIntegral (n : ℕ) :
    (∫ y in Metric.ball (0 : Domain n) 1, fixedMollifierKernel n y) = 1 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun y hy => fixedMollifierKernel_zero_of_not_mem_unitBall hy),
    fixedMollifierKernel_integral]

/-- The actual joint sampling map preserves target null sets from the
restricted fixed-direction pushforward bounds. -/
theorem variableMollification_joint_quasiMeasurePreserving {n : ℕ}
    {s : Domain n → ℝ} (hs : ContDiff ℝ ∞ s)
    {μ ν : Measure (Domain n)} [SFinite μ] {K : ℝ}
    (hbound : ∀ y ∈ Metric.ball (0 : Domain n) 1,
      Measure.map (variableShift s y) μ ≤ ENNReal.ofReal K • ν) :
    QuasiMeasurePreserving (fun p : Domain n × Domain n => variableShift s p.2 p.1)
      (μ.prod (volume.restrict (Metric.ball (0 : Domain n) 1))) ν := by
  apply QuasiMeasurePreserving.prod_of_left
  · change Measurable (fun p : Domain n × Domain n => p.1 - s p.1 • p.2)
    exact measurable_fst.sub ((hs.continuous.measurable.comp measurable_fst).smul measurable_snd)
  · filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    exact ⟨(contDiff_variableShift hs y).continuous.measurable,
      Measure.absolutelyContinuous_of_le_smul (hbound y hy)⟩

/-- An actual finite-measure majorant supplies joint weighted integrability
from local target integrability. -/
theorem variableMollification_weighted_joint_integrable {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Domain n → ℝ} (hs : ContDiff ℝ ∞ s)
    {μ ν : Measure (Domain n)} [SFinite μ] {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ y ∈ Metric.ball (0 : Domain n) 1,
      Measure.map (variableShift s y) μ ≤ ENNReal.ofReal K • ν)
    {f : Domain n → E} (hf : Integrable f ν) :
    Integrable (fun p : Domain n × Domain n =>
      fixedMollifierKernel n p.2 • f (variableShift s p.2 p.1))
      (μ.prod (volume.restrict (Metric.ball (0 : Domain n) 1))) := by
  have hqm := variableMollification_joint_quasiMeasurePreserving hs hbound
  have hm : AEStronglyMeasurable (fun p : Domain n × Domain n =>
      fixedMollifierKernel n p.2 • f (variableShift s p.2 p.1))
      (μ.prod (volume.restrict (Metric.ball (0 : Domain n) 1))) :=
    ((fixedMollifierKernel_contDiff n).continuous.comp continuous_snd).aestronglyMeasurable.smul
      (hf.aestronglyMeasurable.comp_quasiMeasurePreserving hqm)
  apply (integrable_prod_iff' hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    exact (integrable_comp_of_map_le (contDiff_variableShift hs y).continuous.measurable
      (hbound y hy) ENNReal.ofReal_ne_top hf).smul (fixedMollifierKernel n y)
  · have hc : Integrable (fun y : Domain n =>
        fixedMollifierKernel n y * (K * ∫ z, ‖f z‖ ∂ν))
        (volume.restrict (Metric.ball (0 : Domain n) 1)) :=
      (fixedMollifierKernel_integrable n).integrableOn.mul_const _
    apply hc.mono' hm.norm.prod_swap.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    change ‖∫ x, ‖fixedMollifierKernel n y • f (variableShift s y x)‖ ∂μ‖ ≤
      fixedMollifierKernel n y * (K * ∫ z, ‖f z‖ ∂ν)
    have hnonneg : 0 ≤ ∫ x, ‖fixedMollifierKernel n y • f (variableShift s y x)‖ ∂μ :=
      integral_nonneg (fun _ => norm_nonneg _)
    rw [Real.norm_of_nonneg hnonneg]
    simp only [norm_smul, Real.norm_of_nonneg (fixedMollifierKernel_nonneg n y),
      integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (integral_comp_le_of_map_le (contDiff_variableShift hs y).continuous.measurable
        (hbound y hy) hK hf.norm (Eventually.of_forall fun _ => norm_nonneg _))
      (fixedMollifierKernel_nonneg n y)

/-- The nonnegative joint integral has exactly the restricted pushforward
constant; the source kernel contributes its unit mass. -/
theorem variableMollification_weighted_joint_integral_le {n : ℕ}
    {s : Domain n → ℝ} (hs : ContDiff ℝ ∞ s)
    {μ ν : Measure (Domain n)} [SFinite μ] {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ y ∈ Metric.ball (0 : Domain n) 1,
      Measure.map (variableShift s y) μ ≤ ENNReal.ofReal K • ν)
    {g : Domain n → ℝ} (hg : Integrable g ν) (hpos : 0 ≤ᵐ[ν] g) :
    (∫ x, (∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y * g (variableShift s y x)) ∂μ) ≤ K * ∫ z, g z ∂ν := by
  have hi := variableMollification_weighted_joint_integrable hs hK hbound hg
  rw [integral_integral_swap hi]
  calc
    (∫ y in Metric.ball (0 : Domain n) 1,
        ∫ x, fixedMollifierKernel n y * g (variableShift s y x) ∂μ) ≤
        ∫ y in Metric.ball (0 : Domain n) 1,
          fixedMollifierKernel n y * (K * ∫ z, g z ∂ν) := by
      apply integral_mono_ae hi.integral_prod_right
        ((fixedMollifierKernel_integrable n).integrableOn.mul_const _)
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      simp only [smul_eq_mul]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left
        (integral_comp_le_of_map_le (contDiff_variableShift hs y).continuous.measurable
          (hbound y hy) hK hg hpos) (fixedMollifierKernel_nonneg n y)
    _ = K * ∫ z, g z ∂ν := by
      rw [integral_mul_const, fixedMollifierKernel_setIntegral, one_mul]

/-- Actual weighted joint integrability gives an L2 kernel average and
Jensen's integrated bound. This helper applies equally to the tensor columns. -/
theorem fixedMollifier_average_memLp_two {n q : ℕ} {μ : Measure (Domain n)} [SFinite μ]
    {H : Domain n → Domain n → Ambient q}
    (hH : Integrable (fun p : Domain n × Domain n => fixedMollifierKernel n p.2 • H p.1 p.2)
      (μ.prod (volume.restrict (Metric.ball (0 : Domain n) 1))))
    (hHsq : Integrable (fun p : Domain n × Domain n =>
      fixedMollifierKernel n p.2 * ‖H p.1 p.2‖ ^ 2)
      (μ.prod (volume.restrict (Metric.ball (0 : Domain n) 1)))) :
    MemLp (fun x => ∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • H x y) 2 μ ∧
    (∫ x, ‖∫ y in Metric.ball (0 : Domain n) 1, fixedMollifierKernel n y • H x y‖ ^ 2 ∂μ) ≤
      ∫ x, (∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y * ‖H x y‖ ^ 2) ∂μ := by
  have hm := hH.aestronglyMeasurable.integral_prod_right'
  have hJ : ∀ᵐ x ∂μ,
      ‖∫ y in Metric.ball (0 : Domain n) 1, fixedMollifierKernel n y • H x y‖ ^ 2 ≤
        ∫ y in Metric.ball (0 : Domain n) 1,
          fixedMollifierKernel n y * ‖H x y‖ ^ 2 := by
    filter_upwards [hH.prod_right_ae, hHsq.prod_right_ae] with x hx hxsq
    have hv : Integrable (H x) (fixedMollifierProbability n) :=
      fixedMollifierProbability_integrable_of_integrableOn hx
    have hvsq : Integrable (fun y => ‖H x y‖ ^ 2) (fixedMollifierProbability n) :=
      fixedMollifierProbability_integrable_of_integrableOn hxsq
    have hc : ConvexOn ℝ univ (fun v : Ambient q => ‖v‖ ^ 2) :=
      (convexOn_univ_norm (E := Ambient q)).pow (fun _ _ => norm_nonneg _) 2
    have h := hc.map_integral_le (continuous_norm.pow 2).continuousOn isClosed_univ
      (Eventually.of_forall fun _ => mem_univ _) hv hvsq
    simpa only [fixedMollifierProbability_integral_eq_setIntegral, smul_eq_mul] using h
  have hi : Integrable (fun x =>
      ‖∫ y in Metric.ball (0 : Domain n) 1, fixedMollifierKernel n y • H x y‖ ^ 2) μ := by
    apply hHsq.integral_prod_left.mono' (hm.norm.pow 2)
    exact hJ.mono fun x hx => (Real.norm_of_nonneg (sq_nonneg _)).trans_le hx
  exact ⟨(memLp_two_iff_integrable_sq_norm hm).mpr hi,
    integral_mono_ae hi hHsq.integral_prod_left hJ⟩

end HarmonicMaps
