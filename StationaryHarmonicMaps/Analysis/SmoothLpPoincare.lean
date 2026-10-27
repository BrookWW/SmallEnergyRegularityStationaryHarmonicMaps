module

public import StationaryHarmonicMaps.Analysis.SmoothL1Poincare
public import StationaryHarmonicMaps.Analysis.SobolevLpOscillation
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Ball Poincare for lower real exponents

The actual fundamental theorem along segments is followed by Jensen's
inequality on the unit parameter interval. The two ball-affine changes of
variables then bound the literal double integral. The exponent remains p
on the derivative throughout; no Lp-to-L2 implication is used.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology ENNReal

namespace StationaryHarmonicMaps.Analysis

/-- Jensen's norm-power inequality for an actual finite nonzero average. -/
theorem norm_average_rpow_le_average_norm_rpow {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure X} [IsFiniteMeasure μ] [NeZero μ] (f : X → E)
    (hf : Integrable f μ) {p : ℝ} (hp : 1 ≤ p)
    (hfp : Integrable (fun x => ‖f x‖ ^ p) μ) :
    ‖⨍ x, f x ∂μ‖ ^ p ≤ ⨍ x, ‖f x‖ ^ p ∂μ := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have hnorm : ‖⨍ x, f x ∂μ‖ ≤ ⨍ x, ‖f x‖ ∂μ := by
    simp only [average_eq, norm_smul, Real.norm_of_nonneg
      (inv_nonneg.mpr (show 0 ≤ μ.real univ from ENNReal.toReal_nonneg)), smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
      (inv_nonneg.mpr ENNReal.toReal_nonneg)
  have H := (convexOn_rpow hp).map_average_le
    (Real.continuous_rpow_const hp0).continuousOn isClosed_Ici
    (Eventually.of_forall fun x => show ‖f x‖ ∈ Ici (0 : ℝ) from norm_nonneg _) hf.norm hfp
  exact (Real.rpow_le_rpow (norm_nonneg _) hnorm hp0).trans H

/-- The actual HS derivative controls segment differences at every exponent p at least one. -/
theorem ball_segment_norm_rpow_le_integral_hs_rpow {n q : ℕ}
    {f : Domain n → Ambient q} {a x y : Domain n} {r p : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Metric.ball a r))
    (hx : x ∈ Metric.ball a r) (hy : y ∈ Metric.ball a r)
    (hr : 0 < r) (hp : 1 ≤ p) :
    ‖f x-f y‖ ^ p ≤ (2*r*Real.sqrt (n : ℝ)) ^ p *
      ∫ t in Icc (0 : ℝ) 1,
        (Real.sqrt (hsNormSq (fun i => fderiv ℝ f ((1-t) • x+t • y)
          (EuclideanSpace.single i 1)))) ^ p := by
  let γ : ℝ → Domain n := fun t => (1-t) • x+t • y
  let G : Domain n → ℝ := fun z => Real.sqrt (hsNormSq
    (fun i => fderiv ℝ f z (EuclideanSpace.single i 1)))
  have hγ : Continuous γ := by dsimp [γ]; fun_prop
  have hγmem : MapsTo γ (Icc (0 : ℝ) 1) (Metric.ball a r) :=
    fun t ht => segmentPoint_mem_ball hx hy ht
  have hGc : ContinuousOn G (Metric.ball a r) :=
    Real.continuous_sqrt.comp_continuousOn (continuousOn_hsNormSq_fderiv hf)
  have hGγ : ContinuousOn (fun t => G (γ t)) (Icc (0 : ℝ) 1) :=
    hGc.comp hγ.continuousOn hγmem
  have hsumc : ContinuousOn (fun t => ∑ i : Fin n,
      ‖fderiv ℝ f (γ t) (EuclideanSpace.single i 1)‖) (Icc (0 : ℝ) 1) := by
    apply continuousOn_finsetSum
    intro i _
    exact (((hf.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply
      continuousOn_const).norm).comp hγ.continuousOn hγmem
  have hGI : IntegrableOn (fun t => G (γ t)) (Icc (0 : ℝ) 1) volume :=
    hGγ.integrableOn_Icc
  have hsumI : IntegrableOn (fun t => ∑ i : Fin n,
      ‖fderiv ℝ f (γ t) (EuclideanSpace.single i 1)‖) (Icc (0 : ℝ) 1) volume :=
    hsumc.integrableOn_Icc
  have hcompare : (∫ t in Icc (0 : ℝ) 1, ∑ i : Fin n,
      ‖fderiv ℝ f (γ t) (EuclideanSpace.single i 1)‖) ≤
      Real.sqrt (n : ℝ) * ∫ t in Icc (0 : ℝ) 1, G (γ t) := by
    rw [← integral_const_mul]
    apply integral_mono hsumI (hGI.const_mul _)
    intro t
    exact sum_column_norm_le_sqrt_dimension_mul_hs _
  have hseg := (ball_segment_norm_le_integral_column_norm (hf.of_le (by simp)) hx hy hr).trans
    (mul_le_mul_of_nonneg_left hcompare (by positivity : 0 ≤ 2*r))
  have hseg' : ‖f x-f y‖ ≤ (2*r*Real.sqrt (n : ℝ)) *
      ∫ t in Icc (0 : ℝ) 1, G (γ t) := by
    simpa only [γ, mul_assoc] using hseg
  haveI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := by
    constructor
    simp only [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]
  have hG0 (t : ℝ) : 0 ≤ G (γ t) := Real.sqrt_nonneg _
  have hGpI : IntegrableOn (fun t => ‖G (γ t)‖ ^ p) (Icc (0 : ℝ) 1) volume :=
    (hGγ.norm.rpow_const (fun _ _ => Or.inr (le_trans zero_le_one hp))).integrableOn_Icc
  have hJ := norm_average_rpow_le_average_norm_rpow (μ := volume.restrict (Icc (0 : ℝ) 1))
    (fun t => G (γ t)) hGI hp
    hGpI
  have hJ' : (∫ t in Icc (0 : ℝ) 1, G (γ t)) ^ p ≤
      ∫ t in Icc (0 : ℝ) 1, (G (γ t)) ^ p := by
    simpa only [average_eq_integral, Real.norm_of_nonneg (integral_nonneg hG0),
      Real.norm_of_nonneg (hG0 _)] using hJ
  calc
    _ ≤ ((2*r*Real.sqrt (n : ℝ)) * ∫ t in Icc (0 : ℝ) 1, G (γ t)) ^ p :=
      Real.rpow_le_rpow (norm_nonneg _) hseg' (le_trans zero_le_one hp)
    _ = (2*r*Real.sqrt (n : ℝ)) ^ p * (∫ t in Icc (0 : ℝ) 1, G (γ t)) ^ p :=
      Real.mul_rpow (by positivity) (integral_nonneg fun t => Real.sqrt_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hJ' (Real.rpow_nonneg (by positivity) _)

/-- Smooth ball data satisfy Poincare with the same lower real exponent on the HS derivative. -/
theorem smooth_poincare_lp_ball {n q : ℕ} (a : Domain n) {r p : ℝ}
    (hr : 0 < r) (hp : 1 ≤ p) (hp₂ : p ≤ 2)
    {f : Domain n → Ambient q} (hsmooth : ContDiffOn ℝ ∞ f (Metric.ball a r))
    (hf : MemLp f 2 (volume.restrict (Metric.ball a r)))
    (hDf : ∀ i, MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2
      (volume.restrict (Metric.ball a r))) :
    (∫ x in Metric.ball a r, ‖f x-(⨍ y in Metric.ball a r, f y)‖ ^ p) ≤
      (2*r*Real.sqrt (n : ℝ)) ^ p * (2 : ℝ) ^ n *
        ∫ x in Metric.ball a r,
          (Real.sqrt (hsNormSq (fun i => fderiv ℝ f x (EuclideanSpace.single i 1)))) ^ p := by
  classical
  let B : Set (Domain n) := Metric.ball a r
  let μ : Measure (Domain n) := volume.restrict B
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hμ : μ ≠ 0 := by
    intro hz
    have H := congrArg (fun ν : Measure (Domain n) => ν univ) hz
    exact (Metric.measure_ball_pos volume a hr).ne' (by simpa only [μ,B,
      Measure.restrict_apply_univ, Measure.coe_zero, Pi.zero_apply] using H)
  letI : NeZero μ := ⟨hμ⟩
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  let G : Domain n → ℝ := fun x => Real.sqrt (hsNormSq
    (fun i => fderiv ℝ f x (EuclideanSpace.single i 1)))
  let g : Domain n → ℝ := B.indicator (fun x => (G x)^p)
  have hGc : ContinuousOn G B :=
    Real.continuous_sqrt.comp_continuousOn (continuousOn_hsNormSq_fderiv hsmooth)
  have hGpc : ContinuousOn (fun x => (G x)^p) B :=
    hGc.rpow_const (fun _ _ => Or.inr hp0)
  have hgm : Measurable g :=
    hGpc.measurable_piecewise continuousOn_const measurableSet_ball
  have hG2 : MemLp G 2 μ := memLp_sqrt_sum_norm_sq _ hDf
  have hGi : Integrable (fun x => (G x)^p) μ := by
    apply (integrable_norm_rpow_of_memL2 G hp0 hp₂ hG2).congr
    exact Eventually.of_forall fun x => by
      change ‖G x‖ ^ p = (G x)^p
      rw [Real.norm_of_nonneg (show 0 ≤ G x from Real.sqrt_nonneg _)]
  have hgi : Integrable g μ := hGi.congr (by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact (indicator_of_mem hx (fun x => (G x)^p)).symm)
  have hgn : ∀ x ∈ B, 0 ≤ g x := by
    intro x hx
    rw [show g x = (G x)^p from indicator_of_mem hx _]
    exact Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hAffine := ball_affine_integrable_and_integral_le hgm hgn hgi
  have hSegmentInt := ball_affine_segmentIntegral_integrable hgm hgn hgi
  have hPair2 : MemLp (fun z : Domain n × Domain n => f z.1-f z.2) 2 (μ.prod μ) :=
    (hf.comp_fst μ).sub (hf.comp_snd μ)
  have hPair : Integrable (fun z : Domain n × Domain n => ‖f z.1-f z.2‖^p) (μ.prod μ) :=
    integrable_norm_rpow_of_memL2 _ hp0 hp₂ hPair2
  have hCenter : Integrable (fun x => ‖f x-(⨍ y, f y ∂μ)‖^p) μ :=
    integrable_norm_rpow_of_memL2 _ hp0 hp₂ (hf.sub (memLp_const _))
  have hpointMean (x : Domain n) :
      ‖f x-(⨍ y, f y ∂μ)‖^p ≤ (μ.real univ)⁻¹ * ∫ y, ‖f x-f y‖^p ∂μ := by
    have hDiff : MemLp (fun y => f x-f y) 2 μ := (memLp_const _).sub hf
    have H := norm_average_rpow_le_average_norm_rpow (fun y => f x-f y)
      (hDiff.integrable (by norm_num)) hp
      (integrable_norm_rpow_of_memL2 _ hp0 hp₂ hDiff)
    have hAvg : (⨍ y, f x-f y ∂μ) = f x-(⨍ y, f y ∂μ) := by
      have hconst : (μ.real univ)⁻¹ • (∫ _y, f x ∂μ) = f x := by
        rw [← average_eq, average_const]
      simp only [average_eq]
      rw [integral_sub (integrable_const _) (hf.integrable (by norm_num)), smul_sub, hconst]
    rw [hAvg] at H
    simpa only [average_eq, smul_eq_mul] using H
  have hMean : (∫ x, ‖f x-(⨍ y, f y ∂μ)‖^p ∂μ) ≤
      (μ.real univ)⁻¹ * ∫ x, ∫ y, ‖f x-f y‖^p ∂μ ∂μ := by
    rw [← integral_const_mul]
    exact integral_mono hCenter (hPair.integral_prod_left.const_mul _) hpointMean
  have hPairBound : (∫ z : Domain n × Domain n, ‖f z.1-f z.2‖^p ∂μ.prod μ) ≤
      (2*r*Real.sqrt (n : ℝ))^p * ∫ z : Domain n × Domain n,
        (∫ t in Icc (0 : ℝ) 1, g ((1-t) • z.1+t • z.2)) ∂μ.prod μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae hPair (hSegmentInt.const_mul _)
    change ∀ᵐ z ∂(volume.restrict B).prod (volume.restrict B), _
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_ball.prod measurableSet_ball)] with z hz
    rw [show g = B.indicator (fun x => (G x)^p) from rfl,
      ball_affine_segmentIntegral_indicator hz.1 hz.2]
    exact ball_segment_norm_rpow_le_integral_hs_rpow hsmooth hz.1 hz.2 hr hp
  have hDouble : (∫ x, ∫ y, ‖f x-f y‖^p ∂μ ∂μ) ≤
      (2*r*Real.sqrt (n : ℝ))^p *
        ((2 : ℝ)^n * volume.real B * ∫ x in B, (G x)^p) := by
    rw [integral_prod _ hPair, integral_prod _ hSegmentInt] at hPairBound
    have HH := mul_le_mul_of_nonneg_left hAffine.2
      (Real.rpow_nonneg (by positivity : 0 ≤ 2*r*Real.sqrt (n : ℝ)) p)
    rw [ball_setIntegral_indicator a r (fun x => (G x)^p)] at HH
    exact hPairBound.trans HH
  have hmass : 0 < volume.real B :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume a hr).ne' measure_ball_ne_top
  have hMean' : (∫ x in B, ‖f x-(⨍ y in B, f y)‖^p) ≤
      (volume.real B)⁻¹ * ∫ x, ∫ y, ‖f x-f y‖^p ∂μ ∂μ := by
    simpa only [μ, Measure.restrict_apply_univ, measureReal_def] using hMean
  calc
    _ ≤ (volume.real B)⁻¹ * ((2*r*Real.sqrt (n : ℝ))^p *
        ((2 : ℝ)^n * volume.real B * ∫ x in B, (G x)^p)) :=
      hMean'.trans (mul_le_mul_of_nonneg_left hDouble (inv_nonneg.mpr hmass.le))
    _ = _ := by
      change _ = (2*r*Real.sqrt (n : ℝ))^p * (2 : ℝ)^n * ∫ x in B, (G x)^p
      field_simp

end StationaryHarmonicMaps.Analysis

end
