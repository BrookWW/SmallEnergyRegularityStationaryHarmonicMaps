module

public import HarmonicMaps.Analysis.HarmonicBallMeanValue
public import HolderToCK.Foundation.BallVolume
public import StationaryHarmonicMaps.Analysis.HilbertSchmidtEncoding
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Lᵖ decay for actual smooth harmonic fields

Jensen's inequality applies to the convex function v ↦ ‖v‖^p for p≥1.
The genuine harmonic ball mean and interior half-radius balls give the
pointwise bound. Integration and exact Euclidean ball volumes give the
factor 2^n θ^n, without an L²-to-Lᵖ reversal.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

private theorem convexOn_univ_norm_rpow {k : ℕ} {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (fun v : Ambient k => ‖v‖ ^ p) := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  refine ⟨convex_univ, ?_⟩
  intro x _hx y _hy a b ha hb hab
  have hnorm : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ := by
    calc
      _ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = _ := by rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  have hpow := (convexOn_rpow hp).2 (norm_nonneg x) (norm_nonneg y) ha hb hab
  exact (Real.rpow_le_rpow (norm_nonneg _) hnorm hp0).trans hpow

/-- The actual pth norm power of a smooth harmonic map is bounded by its ball average. -/
theorem harmonic_norm_rpow_le_ballAverage {n k : ℕ} (hn : 2 ≤ n)
    {p : ℝ} (hp : 1 ≤ p) (a : Domain n) (R : PositiveRadius)
    (U : Set (Domain n)) (hU : IsOpen U) (hclosed : Metric.closedBall a R.val ⊆ U)
    (f : Domain n → Ambient k) (hf : ContDiffOn ℝ ∞ f U)
    (hharm : ∀ x ∈ Metric.ball a R.val, Laplacian.laplacian f x = 0) :
    ‖f a‖ ^ p ≤ (volume.real (Metric.ball a R.val))⁻¹ *
      ∫ x in Metric.ball a R.val, ‖f x‖ ^ p := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hpow : Continuous (fun v : Ambient k => ‖v‖ ^ p) :=
    (Real.continuous_rpow_const hp0).comp continuous_norm
  have hfi : IntegrableOn f (Metric.ball a R.val) volume :=
    ((hf.continuousOn.mono hclosed).integrableOn_compact
      (isCompact_closedBall a R.val)).mono_set Metric.ball_subset_closedBall
  have hfp : IntegrableOn (fun x => ‖f x‖ ^ p) (Metric.ball a R.val) volume :=
    ((hpow.comp_continuousOn (hf.continuousOn.mono hclosed)).integrableOn_compact
      (isCompact_closedBall a R.val)).mono_set Metric.ball_subset_closedBall
  have H := (convexOn_univ_norm_rpow (k := k) hp).map_set_average_le hpow.continuousOn
    isClosed_univ (Metric.measure_ball_pos volume a R.property).ne'
    measure_ball_ne_top (Eventually.of_forall fun _ => mem_univ _) hfi hfp
  rw [harmonic_ball_meanValue hn a R U hU hclosed f hf hharm]
  simpa only [setAverage_eq, smul_eq_mul] using H

/-- A half-radius interior point is controlled by the true Lᵖ integral on the larger ball. -/
theorem harmonic_norm_rpow_le_half_ball_integral {n k : ℕ} (hn : 2 ≤ n)
    {p : ℝ} (hp : 1 ≤ p) (a : Domain n) (R : PositiveRadius)
    (f : Domain n → Ambient k) (hf : ContDiffOn ℝ ∞ f (Metric.ball a R.val))
    (hharm : ∀ x ∈ Metric.ball a R.val, Laplacian.laplacian f x = 0)
    (hfp : IntegrableOn (fun x => ‖f x‖ ^ p) (Metric.ball a R.val) volume)
    {x : Domain n} (hx : x ∈ Metric.ball a (R.val / 2)) :
    ‖f x‖ ^ p ≤ (volume.real (Metric.ball (0 : Domain n) (R.val / 2)))⁻¹ *
      ∫ y in Metric.ball a R.val, ‖f y‖ ^ p := by
  have hclosed : Metric.closedBall x (R.val / 2) ⊆ Metric.ball a R.val := by
    intro y hy
    have hyx : dist y x ≤ R.val / 2 := hy
    have hxa : dist x a < R.val / 2 := hx
    change dist y a < R.val
    exact lt_of_le_of_lt (dist_triangle y x a) (by linarith only [hyx, hxa])
  have hmean := harmonic_norm_rpow_le_ballAverage hn hp x ⟨R.val / 2, half_pos R.property⟩
    (Metric.ball a R.val) Metric.isOpen_ball hclosed f hf
    (fun y hy => hharm y (hclosed (Metric.ball_subset_closedBall hy)))
  have hsub : Metric.ball x (R.val / 2) ⊆ Metric.ball a R.val :=
    Metric.ball_subset_closedBall.trans hclosed
  have hIntegral : (∫ y in Metric.ball x (R.val / 2), ‖f y‖ ^ p) ≤
      ∫ y in Metric.ball a R.val, ‖f y‖ ^ p :=
    setIntegral_mono_set hfp (Eventually.of_forall fun y => Real.rpow_nonneg (norm_nonneg _) _)
      (Eventually.of_forall fun y hy => hsub hy)
  have hmass : volume.real (Metric.ball x (R.val / 2)) =
      volume.real (Metric.ball (0 : Domain n) (R.val / 2)) := by
    rw [measureReal_def, measureReal_def, Measure.addHaar_ball_center volume]
  exact hmean.trans (by
    rw [hmass]
    exact mul_le_mul_of_nonneg_left hIntegral (inv_nonneg.mpr ENNReal.toReal_nonneg))

/-- Every real p≥1 has the exact dimension-only harmonic Lᵖ decay factor. -/
theorem harmonic_lp_decay {n k : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 1 ≤ p)
    (a : Domain n) (R : PositiveRadius) (f : Domain n → Ambient k)
    (hf : ContDiffOn ℝ ∞ f (Metric.ball a R.val))
    (hharm : ∀ x ∈ Metric.ball a R.val, Laplacian.laplacian f x = 0)
    (hfp : IntegrableOn (fun x => ‖f x‖ ^ p) (Metric.ball a R.val) volume)
    {θ : ℝ} (hθ : 0 < θ) (hθhalf : θ ≤ 1 / 2) :
    (∫ x in Metric.ball a (θ * R.val), ‖f x‖ ^ p) ≤
      (2 : ℝ) ^ n * θ ^ n * ∫ x in Metric.ball a R.val, ‖f x‖ ^ p := by
  have hsub : Metric.ball a (θ * R.val) ⊆ Metric.ball a (R.val / 2) := by
    apply Metric.ball_subset_ball
    nlinarith only [hθhalf, R.property]
  have hsubR : Metric.ball a (θ * R.val) ⊆ Metric.ball a R.val :=
    hsub.trans (Metric.ball_subset_ball (by linarith only [R.property]))
  have hpoint : ∀ x ∈ Metric.ball a (θ * R.val), ‖f x‖ ^ p ≤
      (volume.real (Metric.ball (0 : Domain n) (R.val / 2)))⁻¹ *
        ∫ y in Metric.ball a R.val, ‖f y‖ ^ p := by
    intro x hx
    exact harmonic_norm_rpow_le_half_ball_integral hn hp a R f hf hharm hfp (hsub hx)
  letI : IsFiniteMeasure (volume.restrict (Metric.ball a (θ * R.val))) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have H := setIntegral_mono_on (hfp.mono_set hsubR) (integrable_const _)
    measurableSet_ball hpoint
  rw [setIntegral_const, smul_eq_mul, ← mul_assoc,
    HolderToCK.ball_volume_ratio_half a R.property hθ] at H
  exact H

/-- An actually smooth harmonic encoded one-form has the genuine HS Lᵖ decay bound. -/
theorem harmonic_oneForm_lp_decay {n q : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 1 ≤ p)
    (a : Domain n) (R : PositiveRadius) (h : Domain n → Gradient n q)
    (hsmooth : ContDiffOn ℝ ∞ (fun x => WithLp.toLp 2 (fun j : Fin (n * q) =>
      h x (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)) (Metric.ball a R.val))
    (hharm : ∀ x ∈ Metric.ball a R.val,
      Laplacian.laplacian (fun y => WithLp.toLp 2 (fun j : Fin (n * q) =>
        h y (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)) x = 0)
    (hfp : IntegrableOn (fun x => (Real.sqrt (hsNormSq (h x))) ^ p) (Metric.ball a R.val) volume)
    {θ : ℝ} (hθ : 0 < θ) (hθhalf : θ ≤ 1 / 2) :
    (∫ x in Metric.ball a (θ * R.val), (Real.sqrt (hsNormSq (h x))) ^ p) ≤
      (2 : ℝ) ^ n * θ ^ n * ∫ x in Metric.ball a R.val, (Real.sqrt (hsNormSq (h x))) ^ p := by
  let E : Gradient n q → Ambient (n * q) := fun A => WithLp.toLp 2
    (fun j => A (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)
  have hnorm (x : Domain n) : ‖E (h x)‖ = Real.sqrt (hsNormSq (h x)) := by
    calc
      _ = Real.sqrt (‖E (h x)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = _ := congrArg Real.sqrt (hs_flatten_norm_sq (h x))
  have hEnc : IntegrableOn (fun x => ‖E (h x)‖ ^ p) (Metric.ball a R.val) volume :=
    hfp.congr (Eventually.of_forall fun x => by
      change (Real.sqrt (hsNormSq (h x))) ^ p = ‖E (h x)‖ ^ p
      rw [hnorm])
  have H := harmonic_lp_decay hn hp a R (fun x => E (h x)) hsmooth hharm hEnc hθ hθhalf
  simpa only [hnorm] using H

end StationaryHarmonicMaps.Analysis

end
