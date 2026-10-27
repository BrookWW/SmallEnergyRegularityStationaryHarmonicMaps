module

public import HarmonicMaps.Analysis.MollificationDistanceBasic
public import HarmonicMaps.Analysis.MollificationLocalKernel
public import HarmonicMaps.Analysis.CenteredEnergy
public import HarmonicMaps.Analysis.SobolevPoincare

/-!
# Distance of fixed-radius smoothing to the original target

Actual local Sobolev data give square integrability under the fixed kernel
probability. AE target membership and weighted variance reduce the distance
estimate to the accepted Poincare and centered-energy bounds.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace HarmonicMaps

/-- L2 on the sampled ball gives L2 under the actual fixed kernel probability. -/
theorem mollification_sampling_memLp_probability {n q : ℕ}
    {u : Domain n → Ambient q} (h : PositiveRadius) (x : Domain n)
    (hu : MemLp u 2 (volume.restrict (Metric.ball x h.val))) :
    MemLp (fun y => u (x - h.val • y)) 2 (fixedMollifierProbability n) := by
  letI : IsFiniteMeasure (volume.restrict (Metric.ball x h.val)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hi := mollification_shift_integrableOn h x (hu.integrable (by norm_num))
  have hw : IntegrableOn (fun y => fixedMollifierKernel n y • u (x - h.val • y))
      (Metric.ball (0 : Domain n) 1) volume :=
    hi.bdd_smul (fixedMollifierKernelBound n)
      (fixedMollifierKernel_contDiff n).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (fixedMollifierKernel_nonneg n y)]
        exact fixedMollifierKernel_le_bound n y)
  have hp := fixedMollifierProbability_integrable_of_integrableOn hw
  have hsq := mollification_local_kernel_estimate h x
    (hu.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
    (Filter.Eventually.of_forall fun z => sq_nonneg ‖u z‖)
    (fixedMollifierKernel_le_bound n)
  have hpsq : Integrable (fun y => ‖u (x - h.val • y)‖ ^ 2)
      (fixedMollifierProbability n) := by
    apply fixedMollifierProbability_integrable_of_integrableOn
    simpa only [smul_eq_mul] using hsq.1
  exact (memLp_two_iff_integrable_sq_norm hp.aestronglyMeasurable).mpr hpsq

/-- The source smoothing has a target-distance bound with a fixed dimension-only coefficient. -/
theorem IsLocallyEnergyMinimizing.sourceMollification_distance_bound {n q : ℕ}
    (hn : 2 ≤ n) (N : CompactSmoothEmbeddedTarget q)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hu : MemW12Loc (ballDomain (0 : Domain n) 1) u Du)
    (hN : TakesValuesIn N (ballDomain (0 : Domain n) 1) u)
    (hmin : IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) 1) u Du)
    (hE : dirichletEnergy Du (Metric.ball (0 : Domain n) 1) ≠ ⊤)
    (h : PositiveRadius) (hh : h.val ≤ 1 / 4) (x : Domain n)
    (hx : x ∈ Metric.ball (0 : Domain n) (1 / 2)) :
    Metric.infDist (∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • u (x - h.val • y)) N.carrierSet ^ 2 ≤
      fixedMollifierKernelBound n * (2 : ℝ) ^ (n + 1) * 2 ^ (n - 2) *
        (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal := by
  have hclosed : Metric.closedBall x h.val ⊆ (ballDomain (0 : Domain n) 1).val := by
    apply Metric.closedBall_subset_ball'
    have hxd : dist x (0 : Domain n) < 1 / 2 := hx
    linarith only [hxd, hh]
  have hball : Metric.ball x h.val ⊆ Metric.ball (0 : Domain n) 1 :=
    Metric.ball_subset_closedBall.trans hclosed
  letI : IsFiniteMeasure (volume.restrict (Metric.ball x h.val)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hKpos := fixedMollifierKernelBound_pos n
  have huSmall := hu.memW12_ball hclosed
  have huL2 : MemLp u 2 (volume.restrict (Metric.ball x h.val)) := huSmall.2.1
  let b := ⨍ z in Metric.ball x h.val, u z
  let f : Domain n → Ambient q := fun y => u (x - h.val • y)
  have hfp : MemLp f 2 (fixedMollifierProbability n) :=
    mollification_sampling_memLp_probability h x huL2
  have hNsmall : ∀ᵐ z ∂volume.restrict (Metric.ball x h.val), u z ∈ N.carrierSet :=
    hN.filter_mono (ae_mono (Measure.restrict_mono_set volume hball))
  have hNp : ∀ᵐ y ∂fixedMollifierProbability n, f y ∈ N.carrierSet :=
    ae_fixedMollifierProbability_of_ae_unitBall (ae_mollification_sampling_ball h x hNsmall)
  have hvarint : IntegrableOn (fun z => ‖u z - b‖ ^ 2) (Metric.ball x h.val) volume := by
    exact (huL2.sub (memLp_const b)).integrable_norm_pow
      (by decide : (2 : ℕ) ≠ 0)
  have hkernel := mollification_local_kernel_estimate h x hvarint
    (Filter.Eventually.of_forall fun z => sq_nonneg ‖u z - b‖)
    (fixedMollifierKernel_le_bound n)
  have hpoincare := huSmall.poincare_ball h.property
  have hcenter := (hmin.centered_energy_bound hn N u Du hu hN hE x hx h hh).2
  have hscale : h.val ^ 2 * h.val ^ (n - 2) = h.val ^ n := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ = Metric.infDist (∫ y, f y ∂fixedMollifierProbability n) N.carrierSet ^ 2 := by
      rw [fixedMollifierProbability_integral_eq_setIntegral]
    _ ≤ ∫ y, ‖f y - ∫ z, f z ∂fixedMollifierProbability n‖ ^ 2
        ∂fixedMollifierProbability n :=
      probability_infDist_sq_le_variance _ hfp _ hNp
    _ ≤ ∫ y, ‖f y - b‖ ^ 2 ∂fixedMollifierProbability n :=
      probability_variance_le _ hfp b
    _ = ∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y * ‖u (x - h.val • y) - b‖ ^ 2 := by
      rw [fixedMollifierProbability_integral_eq_setIntegral]
      simp only [f, smul_eq_mul]
    _ ≤ fixedMollifierKernelBound n * (h.val ^ n)⁻¹ *
        ∫ z in Metric.ball x h.val, ‖u z - b‖ ^ 2 := hkernel.2
    _ ≤ fixedMollifierKernelBound n * (h.val ^ n)⁻¹ *
        ((2 : ℝ) ^ (n + 1) * h.val ^ 2 *
          ∫ z in Metric.ball x h.val, hsNormSq (Du z)) :=
      mul_le_mul_of_nonneg_left hpoincare (mul_nonneg hKpos.le (inv_nonneg.mpr (pow_nonneg h.property.le n)))
    _ ≤ fixedMollifierKernelBound n * (h.val ^ n)⁻¹ *
        ((2 : ℝ) ^ (n + 1) * h.val ^ 2 *
          (2 ^ (n - 2) * h.val ^ (n - 2) *
            (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hcenter (by positivity))
        (mul_nonneg hKpos.le (inv_nonneg.mpr (pow_nonneg h.property.le n)))
    _ = _ := by
      calc
        _ = fixedMollifierKernelBound n * (2 : ℝ) ^ (n + 1) * 2 ^ (n - 2) *
            ((h.val ^ n)⁻¹ * (h.val ^ 2 * h.val ^ (n - 2))) *
              (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal := by ring
        _ = _ := by rw [hscale, inv_mul_cancel₀ (pow_ne_zero n h.property.ne'), mul_one]

end HarmonicMaps
