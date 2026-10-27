module

public import HolderToCK.Analysis.Poisson.FundamentalFlux
public import HolderToCK.Analysis.Poisson.FundamentalWeakGradient
public import HolderToCK.Analysis.Poisson.HessianTestIntegrability
public import HolderToCK.Analysis.Poisson.HessianRadialCutoff
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Distributional pairings of the fundamental solution

Smooth compactly supported tests give the Laplacian point mass and the
Hessian principal value. The mixed Hessian retains the point-evaluation term
with coefficient `δᵢⱼ / n`.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology BigOperators

namespace HolderToCK

private theorem sphereTestIntegral_hasDerivAt {n : ℕ}
    {φ : Domain n → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) (r : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ θ : Metric.sphere (0 : Domain n) 1,
      φ (s • θ.val) ∂(volume : Measure (Domain n)).toSphere)
      (∫ θ : Metric.sphere (0 : Domain n) 1,
        fderiv ℝ φ (r • θ.val) θ.val ∂(volume : Measure (Domain n)).toSphere) r := by
  have hD : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  obtain ⟨M, hM⟩ := ((hcφ.fderiv ℝ).isCompact_range hD).exists_bound_of_continuousOn
    continuous_id.continuousOn
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure (Domain n)).toSphere)
    (F := fun s θ => φ (s • θ.val))
    (F' := fun s θ => fderiv ℝ φ (s • θ.val) θ.val)
    (bound := fun _ => M) (s := univ) (by simp) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards with s
    have hc : Continuous (fun θ : Metric.sphere (0 : Domain n) 1 => φ (s • θ.val)) :=
      hφ.continuous.comp (continuous_subtype_val.const_smul s)
    exact hc.aestronglyMeasurable
  · exact (hφ.continuous.comp
      (continuous_subtype_val.const_smul r)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact ((hD.comp (continuous_subtype_val.const_smul r)).clm_apply
      continuous_subtype_val).aestronglyMeasurable
  · filter_upwards with θ s _
    have hθ : ‖θ.val‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
    calc
      _ ≤ ‖fderiv ℝ φ (s • θ.val)‖ * ‖θ.val‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ M := by rw [hθ, mul_one]; exact hM _ (mem_range_self _)
  · exact integrable_const M
  · filter_upwards with θ s _
    simpa only [id_eq, one_smul, Function.comp_def] using
      (hφ.differentiable one_ne_zero (s • θ.val)).hasFDerivAt.comp_hasDerivAt s
        ((hasDerivAt_id s).smul_const θ.val)

private theorem sphereTestIntegral_hasCompactSupport {n : ℕ}
    {φ : Domain n → ℝ} (hcφ : HasCompactSupport φ) :
    HasCompactSupport (fun s : ℝ => ∫ θ : Metric.sphere (0 : Domain n) 1,
      φ (s • θ.val) ∂(volume : Measure (Domain n)).toSphere) := by
  obtain ⟨R, hR, hbound⟩ := hcφ.isBounded.exists_pos_norm_lt
  apply HasCompactSupport.intro' (isCompact_closedBall (0 : ℝ) R)
    Metric.isClosed_closedBall
  intro r hr
  have hrR : R < ‖r‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hr
  apply integral_eq_zero_of_ae
  filter_upwards with θ
  apply image_eq_zero_of_notMem_tsupport
  intro hx
  have hθ : ‖θ.val‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
  have hnorm : ‖r • θ.val‖ = ‖r‖ := by rw [norm_smul, hθ, mul_one]
  exact (hrR.trans (by simpa only [hnorm] using hbound _ hx)).false

private theorem sphereTestIntegral_radialDerivative_integral {n : ℕ}
    {φ : Domain n → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) :
    (∫ r in Ioi (0 : ℝ), ∫ θ : Metric.sphere (0 : Domain n) 1,
      fderiv ℝ φ (r • θ.val) θ.val ∂(volume : Measure (Domain n)).toSphere) =
      -(euclideanSphereArea n * φ 0) := by
  let A : ℝ → ℝ := fun r => ∫ θ : Metric.sphere (0 : Domain n) 1,
    φ (r • θ.val) ∂(volume : Measure (Domain n)).toSphere
  let D : ℝ → ℝ := fun r => ∫ θ : Metric.sphere (0 : Domain n) 1,
    fderiv ℝ φ (r • θ.val) θ.val ∂(volume : Measure (Domain n)).toSphere
  have hAcs : HasCompactSupport A := sphereTestIntegral_hasCompactSupport hcφ
  have hD : Continuous D := by
    have hc : Continuous (fun p : ℝ × Metric.sphere (0 : Domain n) 1 =>
        fderiv ℝ φ (p.1 • p.2.val) p.2.val) :=
      ((hφ.continuous_fderiv one_ne_zero).comp
        (continuous_fst.smul (continuous_subtype_val.comp continuous_snd))).clm_apply
        (continuous_subtype_val.comp continuous_snd)
    simpa only [D, Measure.restrict_univ] using
      continuous_parametric_integral_of_continuous
        (μ := (volume : Measure (Domain n)).toSphere)
        (f := fun r θ => fderiv ℝ φ (r • θ.val) θ.val) hc isCompact_univ
  have hAD (r : ℝ) : HasDerivAt A (D r) r := sphereTestIntegral_hasDerivAt hφ hcφ r
  have hDcs : HasCompactSupport D := by
    have heq : D = deriv A := funext fun r => (hAD r).deriv.symm
    rw [heq]
    exact hAcs.deriv
  have hAt : Tendsto A atTop (𝓝 0) := by
    rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at hAcs
    exact (hAcs.filter_mono _root_.atTop_le_cocompact).tendsto
  have hid := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := (0 : ℝ)) (fun r _ => hAD r)
    (hD.integrable_of_hasCompactSupport hDcs).integrableOn hAt
  change (∫ r in Ioi (0 : ℝ), D r) = _
  rw [hid, zero_sub]
  simp only [A, zero_smul, integral_const, smul_eq_mul]
  rfl

private theorem linearMap_apply_coordinates {n : ℕ} (L : Domain n →L[ℝ] ℝ)
    (x : Domain n) :
    L x = ∑ i : Fin n, x i * L (EuclideanSpace.single i 1) := by
  have hx := (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x
  conv_lhs => rw [← hx, map_sum]
  simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply,
    map_smul, smul_eq_mul]

theorem fundamentalGradient_testIntegrable {n : ℕ} (hn : 0 < n)
    {φ : Domain n → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) :
    Integrable (fun x : Domain n => (euclideanSphereArea n)⁻¹ *
      ‖x‖ ^ (-(n : ℝ)) * fderiv ℝ φ x x) volume := by
  have hi (i : Fin n) : Integrable (fun x : Domain n =>
      ((euclideanSphereArea n)⁻¹ * ‖x‖ ^ (-(n : ℝ)) * x i) *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) volume :=
    normalizedRadialColumn_testIntegrable hn i
      ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      (hcφ.fderiv_apply ℝ _)
  apply (integrable_finsetSum Finset.univ (fun i _ => hi i)).congr
  filter_upwards with x
  rw [linearMap_apply_coordinates, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem fundamentalGradient_distributionPairing {n : ℕ} (hn : 0 < n)
    {φ : Domain n → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) :
    (∫ x : Domain n, (euclideanSphereArea n)⁻¹ *
      ‖x‖ ^ (-(n : ℝ)) * fderiv ℝ φ x x) = -φ 0 := by
  rw [integral_eq_polar hn (fundamentalGradient_testIntegrable hn hφ hcφ) 0]
  have hpolar : (fun r : ℝ => r ^ (n - 1) *
      ∫ θ : Metric.sphere (0 : Domain n) 1,
        (euclideanSphereArea n)⁻¹ * ‖0 + r • θ.val‖ ^ (-(n : ℝ)) *
          fderiv ℝ φ (0 + r • θ.val) (0 + r • θ.val)
        ∂(volume : Measure (Domain n)).toSphere) =ᵐ[volume.restrict (Ioi 0)]
      (fun r => (euclideanSphereArea n)⁻¹ *
        ∫ θ : Metric.sphere (0 : Domain n) 1,
          fderiv ℝ φ (r • θ.val) θ.val ∂(volume : Measure (Domain n)).toSphere) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hrp : 0 < r := hr
    have heq : (fun θ : Metric.sphere (0 : Domain n) 1 =>
        (euclideanSphereArea n)⁻¹ * ‖0 + r • θ.val‖ ^ (-(n : ℝ)) *
          fderiv ℝ φ (0 + r • θ.val) (0 + r • θ.val)) =
        (fun θ => ((euclideanSphereArea n)⁻¹ * r ^ (-(n : ℝ)) * r) *
          fderiv ℝ φ (r • θ.val) θ.val) := by
      funext θ
      have hθ : ‖θ.val‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
      rw [zero_add, norm_smul, Real.norm_of_nonneg hrp.le, hθ, mul_one,
        map_smul, smul_eq_mul]
      ring
    rw [heq, integral_const_mul, Real.rpow_neg hrp.le, Real.rpow_natCast]
    have hpow : r ^ n = r ^ (n - 1) * r := by
      conv_lhs => rw [← Nat.sub_add_cancel hn, pow_succ]
    rw [hpow]
    field_simp [pow_ne_zero _ hrp.ne', hrp.ne']
  rw [integral_congr_ae hpolar, integral_const_mul,
    sphereTestIntegral_radialDerivative_integral hφ hcφ]
  have hS : euclideanSphereArea n ≠ 0 := (euclideanSphereArea_pos hn).ne'
  rw [mul_neg, inv_mul_cancel_left₀ hS]

theorem fundamentalPower_distributionPairing {n : ℕ} (hn : 3 ≤ n)
    {φ : Domain n → ℝ} (hφ : ContDiff ℝ 2 φ) (hcφ : HasCompactSupport φ) :
    (∫ x, fundamentalPowerExpression x * Laplacian.laplacian φ x) = φ 0 := by
  rw [fundamentalPower_laplacianPairing hn hφ hcφ,
    fundamentalGradient_distributionPairing (by omega : 0 < n)
      (hφ.of_le (by norm_num)) hcφ, neg_neg]

theorem fundamentalLog_distributionPairing
    {φ : Domain 2 → ℝ} (hφ : ContDiff ℝ 2 φ) (hcφ : HasCompactSupport φ) :
    (∫ x, fundamentalLogExpression x * Laplacian.laplacian φ x) = φ 0 := by
  have hd := fundamentalGradient_distributionPairing (by omega : 0 < 2)
    (hφ.of_le (by norm_num)) hcφ
  simp only [Nat.cast_ofNat] at hd
  rw [fundamentalLog_laplacianPairing hφ hcφ, hd, neg_neg]

theorem fundamentalSolution_power_testIntegral {n : ℕ} (hn : 3 ≤ n)
    (ψ : Domain n → ℝ) :
    (∫ x : {x : Domain n // x ≠ 0}, fundamentalSolution n (by omega) x * ψ x.val
      ∂(volume : Measure (Domain n)).comap (Subtype.val : {x : Domain n // x ≠ 0} → Domain n)) =
      ∫ x, fundamentalPowerExpression x * ψ x := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega : 0 < n)
  have hs : MeasurableSet {x : Domain n | x ≠ 0} :=
    (isClosed_singleton (x := (0 : Domain n))).isOpen_compl.measurableSet
  have heq : (fun x : {x : Domain n // x ≠ 0} =>
      fundamentalSolution n (by omega) x * ψ x.val) =
      (fun x => fundamentalPowerExpression x.val * ψ x.val) := by
    funext x
    rw [fundamentalSolution_power hn]
  rw [heq]
  calc
    _ = ∫ x in {x : Domain n | x ≠ 0}, fundamentalPowerExpression x * ψ x :=
      integral_subtype_comap hs (fun x => fundamentalPowerExpression x * ψ x)
    _ = _ := by
      change (∫ x in ({(0 : Domain n)}ᶜ : Set (Domain n)),
        fundamentalPowerExpression x * ψ x) = _
      rw [restrict_compl_singleton]

theorem fundamentalSolution_log_testIntegral (ψ : Domain 2 → ℝ) :
    (∫ x : {x : Domain 2 // x ≠ 0}, fundamentalSolution 2 (by omega) x * ψ x.val
      ∂(volume : Measure (Domain 2)).comap (Subtype.val : {x : Domain 2 // x ≠ 0} → Domain 2)) =
      ∫ x, fundamentalLogExpression x * ψ x := by
  have hs : MeasurableSet {x : Domain 2 | x ≠ 0} :=
    (isClosed_singleton (x := (0 : Domain 2))).isOpen_compl.measurableSet
  have heq : (fun x : {x : Domain 2 // x ≠ 0} =>
      fundamentalSolution 2 (by omega) x * ψ x.val) =
      (fun x => fundamentalLogExpression x.val * ψ x.val) := by
    funext x
    rw [fundamentalSolution_log]
  rw [heq]
  calc
    _ = ∫ x in {x : Domain 2 | x ≠ 0}, fundamentalLogExpression x * ψ x :=
      integral_subtype_comap hs (fun x => fundamentalLogExpression x * ψ x)
    _ = _ := by
      change (∫ x in ({(0 : Domain 2)}ᶜ : Set (Domain 2)),
        fundamentalLogExpression x * ψ x) = _
      rw [restrict_compl_singleton]

theorem fundamentalSolution_distributionPairing {n : ℕ} (hn : 2 ≤ n)
    {φ : Domain n → ℝ} (hφ : ContDiff ℝ 2 φ) (hcφ : HasCompactSupport φ) :
    (∫ x : {x : Domain n // x ≠ 0},
      fundamentalSolution n hn x * Laplacian.laplacian φ x.val
      ∂(volume : Measure (Domain n)).comap (Subtype.val : {x : Domain n // x ≠ 0} → Domain n)) =
      φ 0 := by
  by_cases hn2 : n = 2
  · subst n
    rw [fundamentalSolution_log_testIntegral]
    exact fundamentalLog_distributionPairing hφ hcφ
  · rw [fundamentalSolution_power_testIntegral (by omega : 3 ≤ n)]
    exact fundamentalPower_distributionPairing (by omega) hφ hcφ

theorem normalizedRadialColumn_hessianPV {n : ℕ} (hn : 2 ≤ n)
    (i j : Fin n) {φ : Domain n → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hcφ : HasCompactSupport φ) :
    Tendsto (fun r : ℝ => ∫ x in (Metric.ball (0 : Domain n) r)ᶜ,
      hessianKernelExpression i j x * φ x) (𝓝[>] 0)
      (𝓝 (-(∫ x, ((euclideanSphereArea n)⁻¹ * ‖x‖ ^ (-(n : ℝ)) * x i) *
          fderiv ℝ φ x (EuclideanSpace.single j 1)) -
        (if i = j then 1 else 0) / (n : ℝ) * φ 0)) := by
  let ψ : Domain n → ℝ := fun x => φ x - φ 0 * fundamentalTestCutoff x
  have hχ : ContDiff ℝ 1 (fundamentalTestCutoff : Domain n → ℝ) :=
    fundamentalTestCutoff_contDiff.of_le (by norm_num)
  have hψ : ContDiff ℝ 1 ψ := hφ.sub (contDiff_const.mul hχ)
  have hcψ : HasCompactSupport ψ := hcφ.sub fundamentalTestCutoff_hasCompactSupport.mul_left
  have hψ0 : ψ 0 = 0 := by
    dsimp only [ψ]
    rw [fundamentalTestCutoff_zero, mul_one, sub_self]
  have hKψ := hessianKernelExpression_testZero_integrable (by omega : 0 < n)
    i j hψ hcψ hψ0
  have hφD := normalizedRadialColumn_testIntegrable (by omega : 0 < n) i
    (ψ := fun x => fderiv ℝ φ x (EuclideanSpace.single j 1))
    ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const) (hcφ.fderiv_apply ℝ _)
  have hχD := normalizedRadialColumn_testIntegrable (by omega : 0 < n) i
    (ψ := fun x => fderiv ℝ fundamentalTestCutoff x (EuclideanSpace.single j 1))
    ((hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    (fundamentalTestCutoff_hasCompactSupport.fderiv_apply ℝ _)
  have hDψ : (fun x : Domain n =>
      ((euclideanSphereArea n)⁻¹ * ‖x‖ ^ (-(n : ℝ)) * x i) *
        fderiv ℝ ψ x (EuclideanSpace.single j 1)) =
      (fun x => ((euclideanSphereArea n)⁻¹ * ‖x‖ ^ (-(n : ℝ)) * x i) *
        fderiv ℝ φ x (EuclideanSpace.single j 1) - φ 0 *
        (((euclideanSphereArea n)⁻¹ * ‖x‖ ^ (-(n : ℝ)) * x i) *
          fderiv ℝ fundamentalTestCutoff x (EuclideanSpace.single j 1))) := by
    funext x
    rw [show ψ = φ - (fun x => φ 0 * fundamentalTestCutoff x) by rfl,
      fderiv_sub (hφ.differentiable one_ne_zero x)
        ((hχ.differentiable one_ne_zero x).const_mul (φ 0)),
      fderiv_const_mul (hχ.differentiable one_ne_zero x)]
    simp only [sub_apply, smul_apply, smul_eq_mul]
    ring
  have hpair := normalizedRadialColumn_testZero_integrationByParts hn i j hψ hcψ hψ0
  rw [hDψ, integral_sub hφD (hχD.const_mul (φ 0)), integral_const_mul,
    normalizedRadialColumn_cutoffPairing (by omega : 0 < n) i j] at hpair
  have hvalue : (∫ x, hessianKernelExpression i j x * ψ x) =
      -(∫ x, ((euclideanSphereArea n)⁻¹ * ‖x‖ ^ (-(n : ℝ)) * x i) *
        fderiv ℝ φ x (EuclideanSpace.single j 1)) -
      (if i = j then 1 else 0) / (n : ℝ) * φ 0 := by
    linear_combination hpair
  have hext (r : ℝ) (hr : 0 < r) :
      (∫ x in (Metric.ball (0 : Domain n) r)ᶜ, hessianKernelExpression i j x * φ x) =
      ∫ x in (Metric.ball (0 : Domain n) r)ᶜ, hessianKernelExpression i j x * ψ x := by
    have hKχ := hessianKernelExpression_testIntegrableOn_exterior i j
      fundamentalTestCutoff_contDiff.continuous fundamentalTestCutoff_hasCompactSupport hr
    have heq : (fun x => hessianKernelExpression i j x * φ x) =
        (fun x => hessianKernelExpression i j x * ψ x +
          φ 0 * (hessianKernelExpression i j x * fundamentalTestCutoff x)) := by
      funext x
      dsimp only [ψ]
      ring
    rw [heq, integral_add hKψ.integrableOn (hKχ.const_mul (φ 0)), integral_const_mul,
      hessianKernelExpression_cutoffTruncation (by omega : 0 < n) i j hr, mul_zero, add_zero]
  have ht := (integrable_tendsto_exteriorBall_integral (by omega : 0 < n) hKψ).mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  rw [hvalue] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (hext r hr).symm

theorem fundamentalPower_hessianPV {n : ℕ} (hn : 3 ≤ n) (i j : Fin n)
    {φ : Domain n → ℝ} (hφ : ContDiff ℝ 2 φ) (hcφ : HasCompactSupport φ) :
    Tendsto (fun r : ℝ => ∫ x in (Metric.ball (0 : Domain n) r)ᶜ,
      hessianKernelExpression i j x * φ x) (𝓝[>] 0)
      (𝓝 ((∫ x, fundamentalPowerExpression x *
          fderiv ℝ (fun z => fderiv ℝ φ z (EuclideanSpace.single j 1)) x
            (EuclideanSpace.single i 1)) -
        (if i = j then 1 else 0) / (n : ℝ) * φ 0)) := by
  have hD : ContDiff ℝ 1 (fun x => fderiv ℝ φ x (EuclideanSpace.single j 1)) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hfirst := fundamentalPower_testDerivative hn hD (hcφ.fderiv_apply ℝ _) i
  have ht := normalizedRadialColumn_hessianPV (by omega : 2 ≤ n) i j
    (hφ.of_le (by norm_num)) hcφ
  rw [← hfirst] at ht
  exact ht

theorem fundamentalLog_hessianPV (i j : Fin 2)
    {φ : Domain 2 → ℝ} (hφ : ContDiff ℝ 2 φ) (hcφ : HasCompactSupport φ) :
    Tendsto (fun r : ℝ => ∫ x in (Metric.ball (0 : Domain 2) r)ᶜ,
      hessianKernelExpression i j x * φ x) (𝓝[>] 0)
      (𝓝 ((∫ x, fundamentalLogExpression x *
          fderiv ℝ (fun z => fderiv ℝ φ z (EuclideanSpace.single j 1)) x
            (EuclideanSpace.single i 1)) -
        (if i = j then 1 else 0) / (2 : ℝ) * φ 0)) := by
  have hD : ContDiff ℝ 1 (fun x => fderiv ℝ φ x (EuclideanSpace.single j 1)) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hfirst := fundamentalLog_testDerivative hD (hcφ.fderiv_apply ℝ _) i
  have ht := normalizedRadialColumn_hessianPV (by omega : 2 ≤ 2) i j
    (hφ.of_le (by norm_num)) hcφ
  simp only [Nat.cast_ofNat] at ht
  rw [← hfirst] at ht
  exact ht

theorem fundamentalSolution_hessianPV {n : ℕ} (hn : 2 ≤ n) (i j : Fin n)
    {φ : Domain n → ℝ} (hφ : ContDiff ℝ 2 φ) (hcφ : HasCompactSupport φ) :
    Tendsto (fun r : ℝ => ∫ x in (Metric.ball (0 : Domain n) r)ᶜ,
      hessianKernelExpression i j x * φ x) (𝓝[>] 0)
      (𝓝 ((∫ x : {x : Domain n // x ≠ 0}, fundamentalSolution n hn x *
          fderiv ℝ (fun z => fderiv ℝ φ z (EuclideanSpace.single j 1)) x.val
            (EuclideanSpace.single i 1)
          ∂(volume : Measure (Domain n)).comap
            (Subtype.val : {x : Domain n // x ≠ 0} → Domain n)) -
        (if i = j then 1 else 0) / (n : ℝ) * φ 0)) := by
  by_cases hn2 : n = 2
  · subst n
    rw [fundamentalSolution_log_testIntegral (fun x : Domain 2 =>
      fderiv ℝ (fun z => fderiv ℝ φ z (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single i 1))]
    exact fundamentalLog_hessianPV i j hφ hcφ
  · rw [fundamentalSolution_power_testIntegral (by omega : 3 ≤ n)
      (fun x : Domain n =>
        fderiv ℝ (fun z => fderiv ℝ φ z (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single i 1))]
    exact fundamentalPower_hessianPV (by omega) i j hφ hcφ

theorem fundamentalSolution_hessianDistributionPairing {n : ℕ} (hn : 2 ≤ n) (i j : Fin n)
    {φ : Domain n → ℝ} (hφ : ContDiff ℝ 2 φ) (hcφ : HasCompactSupport φ) :
    Tendsto (fun r : ℝ =>
      (∫ x in (Metric.ball (0 : Domain n) r)ᶜ, hessianKernelExpression i j x * φ x) +
        (if i = j then 1 else 0) / (n : ℝ) * φ 0) (𝓝[>] 0)
      (𝓝 (∫ x : {x : Domain n // x ≠ 0}, fundamentalSolution n hn x *
        fderiv ℝ (fun z => fderiv ℝ φ z (EuclideanSpace.single j 1)) x.val
          (EuclideanSpace.single i 1)
        ∂(volume : Measure (Domain n)).comap
          (Subtype.val : {x : Domain n // x ≠ 0} → Domain n))) := by
  simpa only [sub_add_cancel] using
    (fundamentalSolution_hessianPV hn i j hφ hcφ).add_const
      ((if i = j then 1 else 0) / (n : ℝ) * φ 0)

end HolderToCK
end
