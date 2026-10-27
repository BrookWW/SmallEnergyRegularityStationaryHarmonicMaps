module

public import HolderToCK.Analysis.Poisson.FundamentalFlux
public import HolderToCK.Analysis.Poisson.FundamentalIntegrability
public import HarmonicMaps.Analysis.RadialCutoffDerivative
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Radial cutoff pairings for the Hessian point mass -/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology

namespace HolderToCK

@[expose] noncomputable def fundamentalTestCutoffProfile : ℝ → ℝ :=
  radialCutoffProfile ⟨1, one_pos⟩ ⟨1, one_pos⟩

@[expose] noncomputable def fundamentalTestCutoff {n : ℕ} (x : Domain n) : ℝ :=
  fundamentalTestCutoffProfile ‖x‖

theorem fundamentalTestCutoffProfile_contDiff :
    ContDiff ℝ ∞ fundamentalTestCutoffProfile := radialCutoffProfile_contDiff _ _

theorem fundamentalTestCutoff_eq_one {n : ℕ} (x : Domain n) (hx : ‖x‖ ≤ 1) :
    fundamentalTestCutoff x = 1 := radialCutoffProfile_eq_one _ _ hx

theorem fundamentalTestCutoff_eq_zero {n : ℕ} (x : Domain n) (hx : 2 ≤ ‖x‖) :
    fundamentalTestCutoff x = 0 := radialCutoffProfile_eq_zero _ _ (by norm_num; exact hx)

theorem fundamentalTestCutoff_contDiff {n : ℕ} :
    ContDiff ℝ ∞ (fundamentalTestCutoff : Domain n → ℝ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : Domain n) one_pos] with y hy
    exact fundamentalTestCutoff_eq_one y ((by
      simpa only [Metric.mem_ball, dist_zero_right] using hy : ‖y‖ < 1).le)
  · exact fundamentalTestCutoffProfile_contDiff.contDiffAt.comp x
      (contDiffAt_norm (𝕜 := ℝ) hx)

theorem fundamentalTestCutoff_hasCompactSupport {n : ℕ} :
    HasCompactSupport (fundamentalTestCutoff : Domain n → ℝ) := by
  apply HasCompactSupport.intro' (isCompact_closedBall (0 : Domain n) 2)
    Metric.isClosed_closedBall
  intro x hx
  apply fundamentalTestCutoff_eq_zero
  exact (not_le.mp (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)).le

theorem fundamentalTestCutoff_zero {n : ℕ} :
    fundamentalTestCutoff (0 : Domain n) = 1 :=
  fundamentalTestCutoff_eq_one 0 (by simp only [norm_zero]; exact zero_le_one)

theorem fundamentalTestCutoffProfile_deriv_integrable :
    Integrable (deriv fundamentalTestCutoffProfile) volume := by
  exact (fundamentalTestCutoffProfile_contDiff.continuous_deriv (by norm_num)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      ((subset_tsupport _).trans (radialCutoffProfile_deriv_tsupport_subset _ _)))

theorem fundamentalTestCutoffProfile_deriv_integral :
    (∫ r in Ioi (0 : ℝ), deriv fundamentalTestCutoffProfile r) = -1 := by
  have hlim : Tendsto fundamentalTestCutoffProfile atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr
    exact (radialCutoffProfile_eq_zero ⟨1, one_pos⟩ ⟨1, one_pos⟩ (by simpa only [one_add_one_eq_two] using hr)).symm
  rw [integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun r _ => (fundamentalTestCutoffProfile_contDiff.differentiable (by norm_num) r).hasDerivAt)
    fundamentalTestCutoffProfile_deriv_integrable.integrableOn hlim]
  have h0 : fundamentalTestCutoffProfile 0 = 1 :=
    radialCutoffProfile_eq_one _ _ zero_le_one
  rw [h0]
  norm_num

theorem normalizedRadialColumn_cutoffPairing {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    (∫ x : Domain n, ((euclideanSphereArea n)⁻¹ * ‖x‖ ^ (-(n : ℝ)) * x i) *
      fderiv ℝ fundamentalTestCutoff x (EuclideanSpace.single j 1)) =
      -(if i = j then 1 else 0) / (n : ℝ) := by
  have hχ : ContDiff ℝ 1 (fundamentalTestCutoff : Domain n → ℝ) :=
    fundamentalTestCutoff_contDiff.of_le (by norm_num)
  have hi := normalizedRadialColumn_testIntegrable hn i
    (ψ := fun x => fderiv ℝ fundamentalTestCutoff x (EuclideanSpace.single j 1))
    ((hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    (fundamentalTestCutoff_hasCompactSupport.fderiv_apply ℝ _)
  rw [integral_eq_polar hn hi 0]
  have heq : (fun r : ℝ => r ^ (n - 1) *
      ∫ θ : Metric.sphere (0 : Domain n) 1,
        ((euclideanSphereArea n)⁻¹ * ‖0 + r • θ.val‖ ^ (-(n : ℝ)) *
          (0 + r • θ.val) i) *
          fderiv ℝ fundamentalTestCutoff (0 + r • θ.val) (EuclideanSpace.single j 1)
          ∂(volume : Measure (Domain n)).toSphere) =ᵐ[volume.restrict (Ioi 0)]
      (fun r => (euclideanSphereArea n)⁻¹ * deriv fundamentalTestCutoffProfile r *
        (euclideanSphereArea n * (if i = j then 1 else 0) / n)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hrp : 0 < r := hr
    have heqθ : (fun θ : Metric.sphere (0 : Domain n) 1 =>
        ((euclideanSphereArea n)⁻¹ * ‖0 + r • θ.val‖ ^ (-(n : ℝ)) *
          (0 + r • θ.val) i) *
          fderiv ℝ fundamentalTestCutoff (0 + r • θ.val) (EuclideanSpace.single j 1)) =
        (fun θ => ((euclideanSphereArea n)⁻¹ * r ^ (-(n : ℝ)) * r *
          deriv fundamentalTestCutoffProfile r) * (θ.val i * θ.val j)) := by
      funext θ
      have hθ : ‖θ.val‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
      have hθ0 : θ.val ≠ 0 := norm_pos_iff.mp (by rw [hθ]; exact one_pos)
      have hnorm : ‖r • θ.val‖ = r := by
        rw [norm_smul, Real.norm_of_nonneg hrp.le, hθ, mul_one]
      rw [zero_add]
      change ((euclideanSphereArea n)⁻¹ * ‖r • θ.val‖ ^ (-(n : ℝ)) * (r • θ.val) i) *
        fderiv ℝ (fun x : Domain n => fundamentalTestCutoffProfile ‖x‖)
          (r • θ.val) (EuclideanSpace.single j 1) = _
      rw [radialProfile_fderiv_apply
        (fundamentalTestCutoffProfile_contDiff.differentiable (by norm_num) _)
        (smul_ne_zero hrp.ne' hθ0), hnorm]
      simp only [EuclideanSpace.inner_single_right, one_mul, conj_trivial,
        PiLp.smul_apply, smul_eq_mul]
      field_simp
    rw [heqθ, integral_const_mul, sphereCoordinateProduct_moment hn i j,
      Real.rpow_neg hrp.le, Real.rpow_natCast]
    have hpow : r ^ n = r ^ (n - 1) * r := by
      conv_lhs => rw [← Nat.sub_add_cancel hn, pow_succ]
    rw [hpow]
    field_simp [pow_ne_zero _ hrp.ne', hrp.ne']
  rw [integral_congr_ae heq, integral_mul_const, integral_const_mul,
    fundamentalTestCutoffProfile_deriv_integral]
  have hS : euclideanSphereArea n ≠ 0 := (euclideanSphereArea_pos hn).ne'
  field_simp

theorem hessianKernelExpression_cutoffTruncation {n : ℕ} (hn : 0 < n)
    (i j : Fin n) {r : ℝ} (hr : 0 < r) :
    (∫ x in (Metric.ball (0 : Domain n) r)ᶜ,
      hessianKernelExpression i j x * fundamentalTestCutoff x) = 0 := by
  let b : ℝ := max 2 r
  have hrb : r ≤ b := le_max_right _ _
  have hzero : ∀ x ∈ (Metric.ball (0 : Domain n) r)ᶜ \
      (Metric.ball (0 : Domain n) b \ Metric.ball (0 : Domain n) r),
      hessianKernelExpression i j x * fundamentalTestCutoff x = 0 := by
    intro x hx
    have hxb : x ∉ Metric.ball (0 : Domain n) b := fun h => hx.2 ⟨h, hx.1⟩
    have hnorm : b ≤ ‖x‖ := by
      simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hxb
    rw [fundamentalTestCutoff_eq_zero x ((le_max_left 2 r).trans hnorm), mul_zero]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball.compl
    (fun _ hx => hx.2) hzero]
  obtain ⟨_, hpolar⟩ := integral_weighted_annulus_eq_polar hn hr hrb
    (hessianKernelExpression_integrableOn_annulus i j hr)
    fundamentalTestCutoffProfile_contDiff.continuous.continuousOn
  have heq : (fun x : Domain n => fundamentalTestCutoffProfile ‖x - 0‖ *
      hessianKernelExpression i j x) =
      (fun x => hessianKernelExpression i j x * fundamentalTestCutoff x) := by
    funext x
    rw [sub_zero, fundamentalTestCutoff, mul_comm]
  rw [heq] at hpolar
  rw [hpolar]
  calc
    _ = ∫ _ in r..b, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc r b := by simpa only [uIcc_of_le hrb] using ht
      simp only [zero_add]
      rw [hessianKernelExpression_sphere_cancellation hn i j (hr.trans_le ht'.1),
        mul_zero, mul_zero]
    _ = 0 := intervalIntegral.integral_zero

end HolderToCK
end
