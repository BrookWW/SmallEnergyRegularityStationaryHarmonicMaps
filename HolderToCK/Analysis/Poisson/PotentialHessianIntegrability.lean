module

public import HolderToCK.Analysis.Poisson.HessianTestIntegrability
public import HolderToCK.Foundation.HolderContinuity
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Absolutely convergent near Hessian integrals of Holder data -/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace HolderToCK

theorem radialPower_integral_ball {n : ℕ} (hn : 0 < n) {η R : ℝ}
    (hη : 0 < η) (hR : 0 < R) :
    (∫ z in Metric.ball (0 : Domain n) R, ‖z‖ ^ (η - (n : ℝ))) =
      euclideanSphereArea n * R ^ η / η := by
  have hi := (norm_rpow_locallyIntegrable hn
    (p := η - (n : ℝ)) (by linarith only [hη])).integrableOn_isCompact
      (isCompact_closedBall (0 : Domain n) R)
  rw [integral_ball_eq_polar hn (hi.mono_set Metric.ball_subset_closedBall)]
  have heq : (∫ r in Ioo (0 : ℝ) R, r ^ (n - 1) *
      ∫ θ : Metric.sphere (0 : Domain n) 1,
        ‖0 + r • θ.val‖ ^ (η - (n : ℝ)) ∂(volume : Measure (Domain n)).toSphere) =
      euclideanSphereArea n * ∫ r in Ioo (0 : ℝ) R, r ^ (η - 1) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    have heqθ : (fun θ : Metric.sphere (0 : Domain n) 1 =>
        ‖0 + r • θ.val‖ ^ (η - (n : ℝ))) = fun _ => r ^ (η - (n : ℝ)) := by
      funext θ
      have hθ : ‖θ.val‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
      rw [zero_add, norm_smul, Real.norm_of_nonneg hr.1.le, hθ, mul_one]
    dsimp only
    rw [heqθ, integral_const, smul_eq_mul]
    change r ^ (n - 1) * (euclideanSphereArea n * r ^ (η - (n : ℝ))) = _
    rw [mul_left_comm, ← Real.rpow_natCast, ← Real.rpow_add hr.1]
    congr 2
    have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      simpa only [Nat.cast_one] using (Nat.cast_sub (by omega : 1 ≤ n) :
        ((n - 1 : ℕ) : ℝ) = (n : ℝ) - ((1 : ℕ) : ℝ))
    rw [hn1]
    ring
  rw [heq, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR.le,
    integral_rpow (Or.inl (by linarith only [hη] : -1 < η - 1)),
    show η - 1 + 1 = η by ring, Real.zero_rpow hη.ne', sub_zero]
  ring

theorem hessianKernelExpression_measurable {n : ℕ} (i j : Fin n) :
    Measurable (hessianKernelExpression i j) := by
  exact measurable_const.mul
    ((measurable_const.mul (measurable_norm.pow_const _)).sub
      (((measurable_const.mul
        (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).measurable).mul
        (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).measurable).mul
        (measurable_norm.pow_const _)))

theorem hessianKernelExpression_holderDifference_bound {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hn : 0 < n) (i j : Fin n) {g : Domain n → E} {η H : ℝ}
    (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H)
    (x z : Domain n) (hz : z ≠ 0) :
    ‖hessianKernelExpression i j z • (g (x - z) - g x)‖ ≤
      (((n : ℝ) + 1) * (euclideanSphereArea n)⁻¹ * H) * ‖z‖ ^ (η - (n : ℝ)) := by
  have hg : ‖g (x - z) - g x‖ ≤ H * ‖z‖ ^ η := by
    simpa only [dist_eq_norm, sub_sub_cancel_left, norm_neg, Real.rpow_eq_pow] using
      hHolder (x - z) (mem_univ _) x (mem_univ _)
  rw [norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ (((n : ℝ) + 1) * (euclideanSphereArea n)⁻¹ * ‖z‖ ^ (-(n : ℝ))) *
        (H * ‖z‖ ^ η) :=
      (mul_le_mul_of_nonneg_left hg (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (hessianKernelExpression_bound hn i j z hz)
          (mul_nonneg hH (Real.rpow_nonneg (norm_nonneg _) _)))
    _ = _ := by
      rw [show (((n : ℝ) + 1) * (euclideanSphereArea n)⁻¹ * ‖z‖ ^ (-(n : ℝ))) *
          (H * ‖z‖ ^ η) =
          (((n : ℝ) + 1) * (euclideanSphereArea n)⁻¹ * H) *
            (‖z‖ ^ (-(n : ℝ)) * ‖z‖ ^ η) by ring,
        ← Real.rpow_add (norm_pos_iff.mpr hz), show -(n : ℝ) + η = η - (n : ℝ) by ring]

theorem hessianKernelExpression_holderDifference_integrableOn {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hn : 0 < n) (i j : Fin n) {g : Domain n → E} {η H R : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H)
    (x : Domain n) :
    IntegrableOn (fun z => hessianKernelExpression i j z • (g (x - z) - g x))
      (Metric.ball (0 : Domain n) R) volume := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hg : Continuous g := continuousOn_univ.mp (hHolder.continuousOn hη)
  apply integrableOn_ball_of_norm_le_rpow (α := (n : ℝ) - η)
    (C := ((n : ℝ) + 1) * (euclideanSphereArea n)⁻¹ * H)
    (by simp only [finrank_euclideanSpace, Fintype.card_fin]; omega)
  · simp only [finrank_euclideanSpace, Fintype.card_fin]
    linarith only [hη]
  · filter_upwards [ae_restrict_of_ae ((volume : Measure (Domain n)).ae_ne 0)] with z hz
    simpa only [show -((n : ℝ) - η) = η - (n : ℝ) by ring] using
      hessianKernelExpression_holderDifference_bound hn i j hH hHolder x z hz
  · exact (hessianKernelExpression_measurable i j).aestronglyMeasurable.smul
      ((hg.comp (continuous_const.sub continuous_id)).sub continuous_const).aestronglyMeasurable

theorem hessianKernelExpression_holderDifference_integral_bound {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hn : 0 < n) (i j : Fin n) {g : Domain n → E} {η H R : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hR : 0 < R)
    (hHolder : HolderBoundOn univ g η H) (x : Domain n) :
    ‖∫ z in Metric.ball (0 : Domain n) R,
      hessianKernelExpression i j z • (g (x - z) - g x)‖ ≤
      ((n : ℝ) + 1) * H * R ^ η / η := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hi := hessianKernelExpression_holderDifference_integrableOn hn i j hη hH hHolder x
    (R := R)
  have hpow := (norm_rpow_locallyIntegrable hn
    (p := η - (n : ℝ)) (by linarith only [hη])).integrableOn_isCompact
      (isCompact_closedBall (0 : Domain n) R)
  calc
    _ ≤ ∫ z in Metric.ball (0 : Domain n) R,
        ‖hessianKernelExpression i j z • (g (x - z) - g x)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z in Metric.ball (0 : Domain n) R,
        (((n : ℝ) + 1) * (euclideanSphereArea n)⁻¹ * H) *
          ‖z‖ ^ (η - (n : ℝ)) := by
      apply integral_mono_ae hi.norm ((hpow.mono_set Metric.ball_subset_closedBall).const_mul _)
      filter_upwards [ae_restrict_of_ae ((volume : Measure (Domain n)).ae_ne 0)] with z hz
      exact hessianKernelExpression_holderDifference_bound hn i j hH hHolder x z hz
    _ = _ := by
      rw [integral_const_mul, radialPower_integral_ball hn hη hR]
      have hS : euclideanSphereArea n ≠ 0 := (euclideanSphereArea_pos hn).ne'
      field_simp

theorem hessianKernelExpression_smul_testIntegrableOn_exterior {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i j : Fin n) {g : Domain n → E} (hg : Continuous g)
    (hcg : HasCompactSupport g) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun z => hessianKernelExpression i j z • g z)
      (Metric.ball (0 : Domain n) r)ᶜ volume := by
  have hcnorm : HasCompactSupport (fun z => ‖g z‖) :=
    hcg.comp_left norm_zero
  have hi := hessianKernelExpression_testIntegrableOn_exterior i j hg.norm hcnorm hr
  change Integrable _ (volume.restrict (Metric.ball (0 : Domain n) r)ᶜ) at hi ⊢
  apply hi.mono ((hessianKernelExpression_measurable i j).aestronglyMeasurable.smul
    hg.aestronglyMeasurable).restrict
  filter_upwards with z
  change ‖hessianKernelExpression i j z • g z‖ ≤ ‖hessianKernelExpression i j z * ‖g z‖‖
  simp only [norm_smul, Real.norm_eq_abs, norm_mul,
    Real.norm_of_nonneg (norm_nonneg (g z))]
  exact le_rfl

theorem hessianKernelExpression_farHolder_integrableOn {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i j : Fin n) {g : Domain n → E} {η H : ℝ} (hη : 0 < η)
    (hHolder : HolderBoundOn univ g η H) (hcg : HasCompactSupport g) (x : Domain n) :
    IntegrableOn (fun z => hessianKernelExpression i j z • g (x - z))
      (Metric.ball (0 : Domain n) 1)ᶜ volume := by
  have hg : Continuous g := continuousOn_univ.mp (hHolder.continuousOn hη)
  exact hessianKernelExpression_smul_testIntegrableOn_exterior i j
    (hg.comp (continuous_const.sub continuous_id))
    (hcg.comp_homeomorph (Homeomorph.subLeft x)) one_pos

end HolderToCK
end
