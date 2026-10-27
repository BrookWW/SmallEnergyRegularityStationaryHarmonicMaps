module

public import HolderToCK.Analysis.Harmonic.KernelBounds
public import HolderToCK.Analysis.Harmonic.RadialMollifier
public import HolderToCK.Foundation.BallVolume
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Interior quantitative estimates for every harmonic derivative

Radial mollification agrees with a smooth harmonic map in every interior
sampling ball. Differentiation of its compact kernel gives a dimension and
order constant and the exact radius power in the derivative estimate.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology

namespace HolderToCK

noncomputable section

theorem harmonic_iteratedFDeriv_L1_bound (n k : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (a : Domain n) (R : PositiveRadius)
      (f : Domain n → Ambient q),
      ContDiffOn ℝ ∞ f (Metric.ball a R.val) →
      (∀ z ∈ Metric.ball a R.val, Laplacian.laplacian f z = 0) →
      IntegrableOn f (Metric.ball a R.val) →
      ∀ x ∈ Metric.ball a (R.val / 2),
        ‖iteratedFDeriv ℝ k f x‖ ≤
          C * (R.val ^ (n + k))⁻¹ * ∫ z in Metric.ball a R.val, ‖f z‖ := by
  obtain ⟨K, hK, hbound⟩ := scaledMollifierKernel_derivative_bound n k
  refine ⟨K * (2 : ℝ) ^ (n + k), mul_pos hK (pow_pos (by norm_num) _), ?_⟩
  intro q a R f hf hh hfi x hx
  let Ω := ballDomain a R.val
  let h : PositiveRadius := ⟨R.val / 2, half_pos R.property⟩
  have hclosed (y : Domain n) (hy : y ∈ Metric.ball a (R.val / 2)) :
      Metric.closedBall y h.val ⊆ Metric.ball a R.val := by
    intro z hz
    have hzy : dist z y ≤ R.val / 2 := hz
    have hya : dist y a < R.val / 2 := hy
    change dist z a < R.val
    exact lt_of_le_of_lt (dist_triangle z y a) (by linarith only [hzy, hya])
  have heq : euclideanMollification Ω f hfi h =ᶠ[𝓝 x] f := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    rw [euclideanMollification_eq_integral_of_ball_subset Ω f hfi h y
      (Metric.ball_subset_closedBall.trans (hclosed y hy))]
    exact harmonic_scaledMollifier_integral_eq hn y h (Metric.ball a R.val)
      Metric.isOpen_ball (hclosed y hy) f hf hh
  have hderiv : iteratedFDeriv ℝ k f x =
      iteratedFDeriv ℝ k (euclideanMollification Ω f hfi h) x :=
    ((heq.iteratedFDeriv ℝ k).eq_of_nhds).symm
  rw [hderiv]
  have hestimate := kernelConvolution_iteratedFDeriv_norm_le Ω f hfi
    (scaledMollifierKernel_contDiff n h) (scaledMollifierKernel_hasCompactSupport n h) k
    (mul_nonneg hK.le (inv_nonneg.mpr (pow_nonneg h.property.le _)))
    (hbound h) x
  have hcoeff : K * (h.val ^ (n + k))⁻¹ =
      (K * (2 : ℝ) ^ (n + k)) * (R.val ^ (n + k))⁻¹ := by
    change K * ((R.val / 2) ^ (n + k))⁻¹ = _
    rw [div_pow, inv_div]
    ring
  change ‖iteratedFDeriv ℝ k (euclideanMollification Ω f hfi h) x‖ ≤ _ at hestimate
  rw [hcoeff] at hestimate
  exact hestimate


theorem integral_norm_sq_le_ball_volume_mul_sqIntegral {n q : ℕ}
    (a : Domain n) (R : PositiveRadius) (f : Domain n → Ambient q)
    (hf : ContinuousOn f (Metric.ball a R.val))
    (hE : IntegrableOn (fun z => ‖f z‖ ^ 2) (Metric.ball a R.val)) :
    (∫ z in Metric.ball a R.val, ‖f z‖) ^ 2 ≤
      volume.real (Metric.ball a R.val) * ∫ z in Metric.ball a R.val, ‖f z‖ ^ 2 := by
  let μ := volume.restrict (Metric.ball a R.val)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hfLp : MemLp f 2 μ :=
    (memLp_two_iff_integrable_sq_norm (hf.aestronglyMeasurable measurableSet_ball)).mpr hE
  have hnormLp : MemLp (fun z => ‖f z‖) (ENNReal.ofReal (2 : ℝ)) μ := by
    norm_num only [ENNReal.ofReal_ofNat]
    exact hfLp.norm
  have hconstLp : MemLp (fun _ : Domain n => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μ :=
    memLp_const 1
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall (fun z => norm_nonneg (f z)))
    (Filter.Eventually.of_forall (fun _ : Domain n => zero_le_one)) hnormLp hconstLp
  have hCSeq : (∫ z in Metric.ball a R.val, ‖f z‖) ≤
      Real.sqrt (∫ z in Metric.ball a R.val, ‖f z‖ ^ 2) *
        Real.sqrt (volume.real (Metric.ball a R.val)) := by
    dsimp only [μ] at hCS
    simpa only [mul_one, Real.rpow_two, Real.one_rpow, one_pow, integral_const,
      smul_eq_mul, measureReal_def, Measure.restrict_apply_univ,
      ← Real.sqrt_eq_rpow] using hCS
  have hEpos : 0 ≤ ∫ z in Metric.ball a R.val, ‖f z‖ ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hVpos : 0 ≤ volume.real (Metric.ball a R.val) := ENNReal.toReal_nonneg
  have hsquared := (sq_le_sq₀ (integral_nonneg (fun _ => norm_nonneg _))
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hCSeq
  rw [mul_pow, Real.sq_sqrt hEpos, Real.sq_sqrt hVpos, mul_comm] at hsquared
  exact hsquared


theorem harmonic_iteratedFDeriv_sq_L2_bound (n k : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (a : Domain n) (R : PositiveRadius)
      (f : Domain n → Ambient q),
      ContDiffOn ℝ ∞ f (Metric.ball a R.val) →
      (∀ z ∈ Metric.ball a R.val, Laplacian.laplacian f z = 0) →
      IntegrableOn (fun z => ‖f z‖ ^ 2) (Metric.ball a R.val) →
      ∀ x ∈ Metric.ball a (R.val / 2),
        ‖iteratedFDeriv ℝ k f x‖ ^ 2 ≤
          C * (R.val ^ (2 * k + n))⁻¹ * ∫ z in Metric.ball a R.val, ‖f z‖ ^ 2 := by
  obtain ⟨K, hK, hbound⟩ := harmonic_iteratedFDeriv_L1_bound n k hn
  let V := volume.real (Metric.ball (0 : Domain n) 1)
  have hV : 0 < V := ball_volume_real_pos 0 (by norm_num)
  refine ⟨K ^ 2 * V, mul_pos (sq_pos_of_pos hK) hV, ?_⟩
  intro q a R f hf hh hE x hx
  letI : IsFiniteMeasure (volume.restrict (Metric.ball a R.val)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hfLp : MemLp f 2 (volume.restrict (Metric.ball a R.val)) :=
    (memLp_two_iff_integrable_sq_norm
      (hf.continuousOn.aestronglyMeasurable measurableSet_ball)).mpr hE
  have hfi : IntegrableOn f (Metric.ball a R.val) := hfLp.integrable (by norm_num)
  have hL1 := hbound q a R f hf hh hfi x hx
  have hCS := integral_norm_sq_le_ball_volume_mul_sqIntegral a R f hf.continuousOn hE
  have hcoeffpos : 0 ≤ K * (R.val ^ (n + k))⁻¹ :=
    mul_nonneg hK.le (inv_nonneg.mpr (pow_nonneg R.property.le _))
  have hL1pos : 0 ≤ ∫ z in Metric.ball a R.val, ‖f z‖ :=
    integral_nonneg (fun _ => norm_nonneg _)
  have hsquared := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg hcoeffpos hL1pos)).mpr hL1
  rw [mul_pow] at hsquared
  have hcoeff : (K * (R.val ^ (n + k))⁻¹) ^ 2 *
      volume.real (Metric.ball a R.val) =
      (K ^ 2 * V) * (R.val ^ (2 * k + n))⁻¹ := by
    rw [ball_volume_real a R.property]
    change (K * (R.val ^ (n + k))⁻¹) ^ 2 * (R.val ^ n * V) = _
    have hpow : (R.val ^ (n + k)) ^ 2 = R.val ^ n * R.val ^ (2 * k + n) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    rw [mul_pow, inv_pow, hpow]
    field_simp [R.property.ne']
  calc
    _ ≤ (K * (R.val ^ (n + k))⁻¹) ^ 2 *
        (volume.real (Metric.ball a R.val) * ∫ z in Metric.ball a R.val, ‖f z‖ ^ 2) :=
      hsquared.trans (mul_le_mul_of_nonneg_left hCS (sq_nonneg _))
    _ = _ := by rw [← mul_assoc, hcoeff]


theorem harmonic_iteratedFDeriv_L2_bound (n k : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (a : Domain n) (R : PositiveRadius)
      (f : Domain n → Ambient q),
      ContDiffOn ℝ ∞ f (Metric.ball a R.val) →
      (∀ z ∈ Metric.ball a R.val, Laplacian.laplacian f z = 0) →
      IntegrableOn (fun z => ‖f z‖ ^ 2) (Metric.ball a R.val) →
      ∀ x ∈ Metric.ball a (R.val / 2),
        ‖iteratedFDeriv ℝ k f x‖ ≤
          C * Real.rpow R.val (-(k : ℝ) - (n : ℝ) / 2) *
            Real.sqrt (∫ z in Metric.ball a R.val, ‖f z‖ ^ 2) := by
  obtain ⟨K, hK, hbound⟩ := harmonic_iteratedFDeriv_sq_L2_bound n k hn
  refine ⟨Real.sqrt K, Real.sqrt_pos.mpr hK, ?_⟩
  intro q a R f hf hh hE x hx
  have h := Real.le_sqrt_of_sq_le (hbound q a R f hf hh hE x hx)
  have hcoeffpos : 0 ≤ K * (R.val ^ (2 * k + n))⁻¹ :=
    mul_nonneg hK.le (inv_nonneg.mpr (pow_nonneg R.property.le _))
  rw [Real.sqrt_mul hcoeffpos, Real.sqrt_mul hK.le] at h
  have hpower : Real.sqrt ((R.val ^ (2 * k + n))⁻¹) =
      Real.rpow R.val (-(k : ℝ) - (n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_neg R.property.le, ← Real.rpow_mul R.property.le]
    apply congrArg (Real.rpow R.val)
    push_cast
    ring
  rw [hpower] at h
  exact h


theorem harmonic_iteratedFDeriv_sup_bound (n k : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (a : Domain n) (R : PositiveRadius)
      (f : Domain n → Ambient q) (M : ℝ),
      ContDiffOn ℝ ∞ f (Metric.ball a R.val) →
      (∀ z ∈ Metric.ball a R.val, Laplacian.laplacian f z = 0) →
      (∀ z ∈ Metric.ball a R.val, ‖f z‖ ≤ M) →
      ∀ x ∈ Metric.ball a (R.val / 2),
        ‖iteratedFDeriv ℝ k f x‖ ≤ C * (R.val ^ k)⁻¹ * M := by
  obtain ⟨K, hK, hbound⟩ := harmonic_iteratedFDeriv_L1_bound n k hn
  let V := volume.real (Metric.ball (0 : Domain n) 1)
  have hV : 0 < V := ball_volume_real_pos 0 (by norm_num)
  refine ⟨K * V, mul_pos hK hV, ?_⟩
  intro q a R f M hf hh hM x hx
  letI : IsFiniteMeasure (volume.restrict (Metric.ball a R.val)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hfi : IntegrableOn f (Metric.ball a R.val) :=
    (integrable_const M).mono' (hf.continuousOn.aestronglyMeasurable measurableSet_ball)
      ((ae_restrict_iff' measurableSet_ball).mpr (Filter.Eventually.of_forall hM))
  have hL1 := hbound q a R f hf hh hfi x hx
  have hmass := setIntegral_mono_on hfi.norm (integrable_const M) measurableSet_ball hM
  rw [setIntegral_const, smul_eq_mul] at hmass
  have hcoeff : K * (R.val ^ (n + k))⁻¹ *
      (volume.real (Metric.ball a R.val) * M) = (K * V) * (R.val ^ k)⁻¹ * M := by
    rw [ball_volume_real a R.property, pow_add]
    dsimp only [V]
    field_simp [R.property.ne']
  calc
    _ ≤ K * (R.val ^ (n + k))⁻¹ * (volume.real (Metric.ball a R.val) * M) :=
      hL1.trans (mul_le_mul_of_nonneg_left hmass
        (mul_nonneg hK.le (inv_nonneg.mpr (pow_nonneg R.property.le _))))
    _ = _ := hcoeff

end
end HolderToCK
end
