module

public import HarmonicMaps.Analysis.MollificationChangeVariables
public import HarmonicMaps.EnergyLemmas
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Jensen and Fubini estimates for mollified gradient columns

The estimates concern the actual kernel averages of arbitrary gradient fields.
Columnwise L2 data on the unit ball supply all integrability premises.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal BigOperators

namespace HarmonicMaps

noncomputable section

private theorem fixedMollifierKernel_norm_bound (n : ℕ) (y : Domain n) :
    ‖fixedMollifierKernel n y‖ ≤ (∫ z, rawMollifierKernel n z)⁻¹ := by
  rw [Real.norm_of_nonneg (fixedMollifierKernel_nonneg n y)]
  change rawMollifierKernel n y / (∫ z, rawMollifierKernel n z) ≤ _
  simpa only [one_div, rawMollifierKernel] using div_le_div_of_nonneg_right
    (Real.smoothTransition.le_one _) (rawMollifierKernel_integral_pos n).le

/-- The probability measure with density equal to the fixed normalized kernel. -/
def fixedMollifierProbability (n : ℕ) : Measure (Domain n) :=
  volume.withDensity (fun y => ENNReal.ofReal (fixedMollifierKernel n y))

instance fixedMollifierProbability_isProbability (n : ℕ) :
    IsProbabilityMeasure (fixedMollifierProbability n) := by
  constructor
  rw [fixedMollifierProbability, withDensity_apply _ MeasurableSet.univ, restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (fixedMollifierKernel_integrable n)
      (Filter.Eventually.of_forall (fixedMollifierKernel_nonneg n)),
    fixedMollifierKernel_integral]
  simp

/-- Integration against the kernel probability is the literal weighted integral. -/
theorem fixedMollifierProbability_integral {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Domain n → E) :
    (∫ y, f y ∂fixedMollifierProbability n) = ∫ y, fixedMollifierKernel n y • f y := by
  rw [fixedMollifierProbability, integral_withDensity_eq_integral_toReal_smul
    ((fixedMollifierKernel_contDiff n).continuous.measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (fixedMollifierKernel_nonneg n _)]

/-- Weighted Bochner integrability gives integrability for the kernel probability. -/
theorem fixedMollifierProbability_integrable {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Domain n → E}
    (hf : Integrable (fun y => fixedMollifierKernel n y • f y) volume) :
    Integrable f (fixedMollifierProbability n) := by
  apply (integrable_withDensity_iff_integrable_smul'
    ((fixedMollifierKernel_contDiff n).continuous.measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
  simpa only [ENNReal.toReal_ofReal (fixedMollifierKernel_nonneg n _)] using hf

/-- An integrable field has integrable kernel-weighted translates at positive scales. -/
theorem weighted_shift_integrable {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Domain n → E}
    (hf : Integrable f volume) (h : PositiveRadius) (x : Domain n) :
    Integrable (fun y => fixedMollifierKernel n y • f (x - h.val • y)) volume := by
  exact ((hf.comp_sub_left x).comp_smul h.property.ne').bdd_smul
    (∫ z, rawMollifierKernel n z)⁻¹
    (fixedMollifierKernel_contDiff n).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (fixedMollifierKernel_norm_bound n))

/-- Weighted Jensen requires integrability only for the actual averaging variable. -/
theorem fixedMollifierProbability_norm_sq_integral_le {n q : ℕ}
    {f : Domain n → Ambient q}
    (hf : Integrable (fun y => fixedMollifierKernel n y • f y) volume)
    (hf2 : Integrable (fun y => fixedMollifierKernel n y * ‖f y‖ ^ 2) volume) :
    ‖∫ y, fixedMollifierKernel n y • f y‖ ^ 2 ≤
      ∫ y, fixedMollifierKernel n y * ‖f y‖ ^ 2 := by
  have hv := fixedMollifierProbability_integrable hf
  have hs := fixedMollifierProbability_integrable hf2
  have hc : ConvexOn ℝ Set.univ (fun v : Ambient q => ‖v‖ ^ 2) :=
    (convexOn_univ_norm (E := Ambient q)).pow (fun _ _ => norm_nonneg _) 2
  have hj := hc.map_integral_le (continuous_norm.pow 2).continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hv hs
  simpa only [fixedMollifierProbability_integral, smul_eq_mul] using hj

/-- Jensen's inequality for the actual weighted average of a square-integrable column. -/
theorem mollification_column_jensen {n q : ℕ} {f : Domain n → Ambient q}
    (hf : Integrable f volume) (hf2 : Integrable (fun z => ‖f z‖ ^ 2) volume)
    (h : PositiveRadius) (x : Domain n) :
    ‖∫ y, fixedMollifierKernel n y • f (x - h.val • y)‖ ^ 2 ≤
      ∫ y, fixedMollifierKernel n y * ‖f (x - h.val • y)‖ ^ 2 := by
  exact fixedMollifierProbability_norm_sq_integral_le (weighted_shift_integrable hf h x)
    (weighted_shift_integrable hf2 h x)

/-- Translation invariance and the Tonelli finiteness criterion give joint integrability. -/
theorem weighted_shift_joint_integrable {n : ℕ} {g : Domain n → ℝ}
    (hg : Integrable g volume) (h : PositiveRadius) :
    Integrable (fun p : Domain n × Domain n =>
      fixedMollifierKernel n p.2 * g (p.1 - h.val • p.2)) (volume.prod volume) := by
  have hshift : QuasiMeasurePreserving
      (fun p : Domain n × Domain n => p.1 - h.val • p.2)
      (volume.prod volume) volume := by
    apply QuasiMeasurePreserving.prod_of_left (by fun_prop)
    exact Filter.Eventually.of_forall fun y =>
      (measurePreserving_sub_right volume (h.val • y)).quasiMeasurePreserving
  have hm : AEStronglyMeasurable (fun p : Domain n × Domain n =>
      fixedMollifierKernel n p.2 * g (p.1 - h.val • p.2)) (volume.prod volume) :=
    ((fixedMollifierKernel_contDiff n).continuous.aestronglyMeasurable.comp_snd).mul
      (hg.aestronglyMeasurable.comp_quasiMeasurePreserving hshift)
  apply (integrable_prod_iff' hm).mpr
  constructor
  · exact Filter.Eventually.of_forall fun y =>
      (hg.comp_sub_right (h.val • y)).const_mul (fixedMollifierKernel n y)
  · have heq : (fun y : Domain n => ∫ x,
        ‖fixedMollifierKernel n y * g (x - h.val • y)‖) =
        fun y => fixedMollifierKernel n y * ∫ x, ‖g x‖ := by
      funext y
      simp only [norm_mul, Real.norm_of_nonneg (fixedMollifierKernel_nonneg n y),
        integral_const_mul]
      rw [integral_sub_right_eq_self (fun x => ‖g x‖) (h.val • y)]
    rw [heq]
    exact (fixedMollifierKernel_integrable n).mul_const _

/-- The nonnegative joint energy integrand is integrable, so Fubini applies. -/
theorem mollification_column_joint_integrable {n q : ℕ} {f : Domain n → Ambient q}
    (hf2 : Integrable (fun z => ‖f z‖ ^ 2) volume) (h : PositiveRadius) :
    Integrable (fun p : Domain n × Domain n =>
      fixedMollifierKernel n p.2 * ‖f (p.1 - h.val • p.2)‖ ^ 2)
      (volume.prod volume) :=
  weighted_shift_joint_integrable hf2 h

private theorem column_integrableOn_of_memLp {n q : ℕ} {f : Domain n → Ambient q}
    (hf : MemLp f 2 (volume.restrict (Metric.ball (0 : Domain n) 1))) :
    IntegrableOn f (Metric.ball (0 : Domain n) 1) volume := by
  letI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Domain n) 1)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  exact hf.integrable (by norm_num)

private theorem norm_sq_zeroExtension {n q : ℕ} (f : Domain n → Ambient q) :
    (fun z => ‖unitBallZeroExtension f z‖ ^ 2) =
      (Metric.ball (0 : Domain n) 1).indicator (fun z => ‖f z‖ ^ 2) := by
  funext z
  by_cases hz : z ∈ Metric.ball (0 : Domain n) 1
  · simp only [unitBallZeroExtension, Set.indicator_of_mem hz]
  · simp only [unitBallZeroExtension, Set.indicator_of_notMem hz, norm_zero,
      zero_pow (by decide : 2 ≠ 0)]

private theorem norm_sq_zeroExtension_integrable {n q : ℕ} {f : Domain n → Ambient q}
    (hf : MemLp f 2 (volume.restrict (Metric.ball (0 : Domain n) 1))) :
    Integrable (fun z => ‖unitBallZeroExtension f z‖ ^ 2) volume := by
  rw [norm_sq_zeroExtension]
  have h2 : IntegrableOn (fun z => ‖f z‖ ^ 2) (Metric.ball (0 : Domain n) 1) volume :=
    hf.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  exact h2.integrable_indicator measurableSet_ball

/-- Each literal source weighted square integrand is integrable at every interior point. -/
theorem sourceMollification_column_integrable_energyIntegrand {n q : ℕ}
    {f : Domain n → Ambient q}
    (hf : MemLp f 2 (volume.restrict (Metric.ball (0 : Domain n) 1)))
    (h : PositiveRadius) (hh : h.val ≤ 1 / 4) {x : Domain n}
    (hx : x ∈ Metric.ball (0 : Domain n) (3 / 4)) :
    IntegrableOn (fun y => fixedMollifierKernel n y * ‖f (x - h.val • y)‖ ^ 2)
      (Metric.ball (0 : Domain n) 1) volume := by
  apply (weighted_shift_integrable (norm_sq_zeroExtension_integrable hf) h x).integrableOn.congr_fun
    _ measurableSet_ball
  intro y hy
  dsimp only
  rw [smul_eq_mul, unitBallZeroExtension, Set.indicator_of_mem
    (mollification_sampling_mem_unitBall h hh hx hy)]

/-- The source column average obeys Jensen on the whole proved interior neighborhood. -/
theorem sourceMollification_column_jensen {n q : ℕ} {f : Domain n → Ambient q}
    (hf : MemLp f 2 (volume.restrict (Metric.ball (0 : Domain n) 1)))
    (h : PositiveRadius) (hh : h.val ≤ 1 / 4) {x : Domain n}
    (hx : x ∈ Metric.ball (0 : Domain n) (3 / 4)) :
    ‖∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • f (x - h.val • y)‖ ^ 2 ≤
      ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y * ‖f (x - h.val • y)‖ ^ 2 := by
  have hL1 := column_integrableOn_of_memLp hf
  calc
    ‖∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • f (x - h.val • y)‖ ^ 2 =
        ‖∫ y, fixedMollifierKernel n y •
          unitBallZeroExtension f (x - h.val • y)‖ ^ 2 := by
      rw [sourceMollification_eq_zeroExtended f hL1 h hh x hx,
        fixedMollifierKernel_integral_zeroExtension_eq f hL1 h]
    _ ≤ ∫ y, fixedMollifierKernel n y *
        ‖unitBallZeroExtension f (x - h.val • y)‖ ^ 2 :=
      mollification_column_jensen (unitBallZeroExtension_integrable f hL1)
        (norm_sq_zeroExtension_integrable hf) h x
    _ = ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y * ‖f (x - h.val • y)‖ ^ 2 := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := Metric.ball (0 : Domain n) 1) (fun y hy => by
          rw [fixedMollifierKernel_zero_of_not_mem_unitBall hy, zero_mul])]
      apply setIntegral_congr_fun measurableSet_ball
      intro y hy
      dsimp only
      rw [unitBallZeroExtension, Set.indicator_of_mem
        (mollification_sampling_mem_unitBall h hh hx hy)]

/-- Square integrability of the actual global average follows from column L2 on B1. -/
theorem mollification_column_integrable_norm_sq {n q : ℕ} {f : Domain n → Ambient q}
    (hf : MemLp f 2 (volume.restrict (Metric.ball (0 : Domain n) 1)))
    (h : PositiveRadius) :
    Integrable (fun x => ‖∫ y, fixedMollifierKernel n y •
      unitBallZeroExtension f (x - h.val • y)‖ ^ 2) volume := by
  have hL1 := column_integrableOn_of_memLp hf
  have hzero := unitBallZeroExtension_integrable f hL1
  have hsq := norm_sq_zeroExtension_integrable hf
  have hJoint := mollification_column_joint_integrable hsq h
  have hm : AEStronglyMeasurable (fun x => ‖∫ y, fixedMollifierKernel n y •
      unitBallZeroExtension f (x - h.val • y)‖ ^ 2) volume := by
    simp_rw [fixedMollifierKernel_integral_zeroExtension_eq f hL1 h]
    exact ((zeroExtendedMollification_contDiff f hL1 h).continuous.norm.pow 2).aestronglyMeasurable
  apply hJoint.integral_prod_left.mono' hm
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact mollification_column_jensen hzero hsq h x

/-- Fubini and translation invariance give the exact factor one for column energy. -/
theorem mollification_column_integral_norm_sq_le {n q : ℕ} {f : Domain n → Ambient q}
    (hf : MemLp f 2 (volume.restrict (Metric.ball (0 : Domain n) 1)))
    (h : PositiveRadius) :
    (∫ x, ‖∫ y, fixedMollifierKernel n y •
      unitBallZeroExtension f (x - h.val • y)‖ ^ 2) ≤
      ∫ z in Metric.ball (0 : Domain n) 1, ‖f z‖ ^ 2 := by
  have hL1 := column_integrableOn_of_memLp hf
  have hzero := unitBallZeroExtension_integrable f hL1
  have hsq := norm_sq_zeroExtension_integrable hf
  have hJoint := mollification_column_joint_integrable hsq h
  calc
    (∫ x, ‖∫ y, fixedMollifierKernel n y •
        unitBallZeroExtension f (x - h.val • y)‖ ^ 2) ≤
        ∫ x, ∫ y, fixedMollifierKernel n y *
          ‖unitBallZeroExtension f (x - h.val • y)‖ ^ 2 :=
      integral_mono (mollification_column_integrable_norm_sq hf h)
        hJoint.integral_prod_left (fun x => mollification_column_jensen hzero hsq h x)
    _ = ∫ y, ∫ x, fixedMollifierKernel n y *
          ‖unitBallZeroExtension f (x - h.val • y)‖ ^ 2 :=
      integral_integral_swap hJoint
    _ = ∫ y, fixedMollifierKernel n y * ∫ z, ‖unitBallZeroExtension f z‖ ^ 2 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        dsimp only
        rw [integral_const_mul,
          integral_sub_right_eq_self (fun z => ‖unitBallZeroExtension f z‖ ^ 2) (h.val • y)]
    _ = ∫ z, ‖unitBallZeroExtension f z‖ ^ 2 := by
      rw [integral_mul_const, fixedMollifierKernel_integral, one_mul]
    _ = ∫ z in Metric.ball (0 : Domain n) 1, ‖f z‖ ^ 2 := by
      rw [norm_sq_zeroExtension, integral_indicator measurableSet_ball]

/-- The literal source average has finite column energy on the half-unit ball. -/
theorem sourceMollification_column_integrable_norm_sq {n q : ℕ}
    {f : Domain n → Ambient q}
    (hf : MemLp f 2 (volume.restrict (Metric.ball (0 : Domain n) 1)))
    (h : PositiveRadius) (hh : h.val ≤ 1 / 4) :
    IntegrableOn (fun x => ‖∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • f (x - h.val • y)‖ ^ 2)
      (Metric.ball (0 : Domain n) (1 / 2)) volume := by
  have hL1 := column_integrableOn_of_memLp hf
  apply (mollification_column_integrable_norm_sq hf h).integrableOn.congr_fun _
    measurableSet_ball
  intro x hx
  dsimp only
  have hx' : x ∈ Metric.ball (0 : Domain n) (3 / 4) :=
    Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4) hx
  rw [sourceMollification_eq_zeroExtended f hL1 h hh x hx',
    fixedMollifierKernel_integral_zeroExtension_eq f hL1 h]

/-- Restricting the global Jensen--Fubini estimate gives source half-ball column energy. -/
theorem sourceMollification_column_energy_le {n q : ℕ} {f : Domain n → Ambient q}
    (hf : MemLp f 2 (volume.restrict (Metric.ball (0 : Domain n) 1)))
    (h : PositiveRadius) (hh : h.val ≤ 1 / 4) :
    (∫ x in Metric.ball (0 : Domain n) (1 / 2),
      ‖∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • f (x - h.val • y)‖ ^ 2) ≤
      ∫ z in Metric.ball (0 : Domain n) 1, ‖f z‖ ^ 2 := by
  have hL1 := column_integrableOn_of_memLp hf
  calc
    (∫ x in Metric.ball (0 : Domain n) (1 / 2),
        ‖∫ y in Metric.ball (0 : Domain n) 1,
          fixedMollifierKernel n y • f (x - h.val • y)‖ ^ 2) =
        ∫ x in Metric.ball (0 : Domain n) (1 / 2),
          ‖∫ y, fixedMollifierKernel n y • unitBallZeroExtension f (x - h.val • y)‖ ^ 2 := by
      apply setIntegral_congr_fun measurableSet_ball
      intro x hx
      dsimp only
      have hx' : x ∈ Metric.ball (0 : Domain n) (3 / 4) :=
        Metric.ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4) hx
      rw [sourceMollification_eq_zeroExtended f hL1 h hh x hx',
        fixedMollifierKernel_integral_zeroExtension_eq f hL1 h]
    _ ≤ ∫ x, ‖∫ y, fixedMollifierKernel n y •
          unitBallZeroExtension f (x - h.val • y)‖ ^ 2 :=
      setIntegral_le_integral (mollification_column_integrable_norm_sq hf h)
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    _ ≤ ∫ z in Metric.ball (0 : Domain n) 1, ‖f z‖ ^ 2 :=
      mollification_column_integral_norm_sq_le hf h

end
end HarmonicMaps

end
