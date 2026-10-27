module

public import HolderToCK.Analysis.Poisson.PotentialGradient

/-! # Uniform local potential bounds for data with fixed support -/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped Topology

namespace HolderToCK

theorem compactUnitData_sub_eq_zero {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] {g : Domain n → E}
    (hSupp : tsupport g ⊆ Metric.closedBall (0 : Domain n) 1)
    {x z : Domain n} (hx : ‖x‖ ≤ 1) (hz : z ∉ Metric.ball (0 : Domain n) 3) :
    g (x - z) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hg : ‖x - z‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hSupp hmem
  have hz3 : 3 ≤ ‖z‖ := by
    simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hz
  have hn : ‖z‖ ≤ ‖x‖ + ‖x - z‖ := by
    calc
      _ = ‖x - (x - z)‖ := by rw [sub_sub_cancel]
      _ ≤ _ := norm_sub_le _ _
  linarith only [hn, hg, hx, hz3]

theorem locallyIntegrableKernel_unitData_norm_bound {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : Domain n → ℝ} (hk : LocallyIntegrable k volume)
    {g : Domain n → E} (hg : Continuous g) (hcg : HasCompactSupport g)
    (hSupp : tsupport g ⊆ Metric.closedBall (0 : Domain n) 1)
    {M : ℝ} (_hM : 0 ≤ M) (hbound : ∀ y, ‖g y‖ ≤ M)
    {x : Domain n} (hx : ‖x‖ ≤ 1) :
    ‖∫ z, k z • g (x - z)‖ ≤ M * ∫ z in Metric.ball (0 : Domain n) 3, ‖k z‖ := by
  have hi := hk.integrable_smul_right_of_hasCompactSupport
    (hg.comp (continuous_const.sub continuous_id)) (hcg.comp_homeomorph (Homeomorph.subLeft x))
  have heq : (∫ z, k z • g (x - z)) =
      ∫ z in Metric.ball (0 : Domain n) 3, k z • g (x - z) := by
    rw [← setIntegral_univ]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ (subset_univ _)
    intro z hz
    rw [compactUnitData_sub_eq_zero hSupp hx hz.2, smul_zero]
  rw [heq]
  have hki := (hk.integrableOn_isCompact (isCompact_closedBall (0 : Domain n) 3)).mono_set
    Metric.ball_subset_closedBall
  calc
    _ ≤ ∫ z in Metric.ball (0 : Domain n) 3, ‖k z • g (x - z)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z in Metric.ball (0 : Domain n) 3, M * ‖k z‖ := by
      apply integral_mono_ae hi.integrableOn.norm (hki.norm.const_mul M)
      filter_upwards with z
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)).trans_eq (mul_comm _ _)
    _ = _ := integral_const_mul _ _

@[expose] noncomputable def potentialValueConstant (n : ℕ) : ℝ :=
  if n = 2 then ∫ z in Metric.ball (0 : Domain n) 3,
    ‖(2 * Real.pi)⁻¹ * Real.log ‖z‖‖
  else ∫ z in Metric.ball (0 : Domain n) 3, ‖fundamentalPowerExpression z‖

theorem potentialValueConstant_nonneg (n : ℕ) : 0 ≤ potentialValueConstant n := by
  rw [potentialValueConstant]
  split_ifs <;> exact integral_nonneg (fun _ => norm_nonneg _)

theorem newtonianPotential_unitData_norm_bound {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hn : 2 ≤ n) {g : Domain n → E} (hg : Continuous g) (hcg : HasCompactSupport g)
    (hSupp : tsupport g ⊆ Metric.closedBall (0 : Domain n) 1)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ y, ‖g y‖ ≤ M)
    {x : Domain n} (hx : ‖x‖ ≤ 1) :
    ‖newtonianPotential hn g x‖ ≤ potentialValueConstant n * M := by
  by_cases hn2 : n = 2
  · subst n
    rw [newtonianPotential_eq_log, potentialValueConstant, if_pos rfl]
    simpa only [fundamentalLogExpression, mul_comm] using
      locallyIntegrableKernel_unitData_norm_bound fundamentalLog_locallyIntegrable
        hg hcg hSupp hM hbound hx
  · have hn3 : 3 ≤ n := by omega
    rw [newtonianPotential_eq_power hn3, potentialValueConstant, if_neg hn2]
    simpa only [mul_comm] using
      locallyIntegrableKernel_unitData_norm_bound (fundamentalPower_locallyIntegrable hn3)
        hg hcg hSupp hM hbound hx

theorem normalizedRadialColumn_abs_bound {n : ℕ} (hn : 0 < n) (i : Fin n)
    (z : Domain n) (hz : z ≠ 0) :
    |(euclideanSphereArea n)⁻¹ * ‖z‖ ^ (-(n : ℝ)) * z i| ≤
      (euclideanSphereArea n)⁻¹ * ‖z‖ ^ (1 - (n : ℝ)) := by
  have heq : (euclideanSphereArea n)⁻¹ * ‖z‖ ^ (-(n : ℝ)) * z i =
      fundamentalGradientExpression z (EuclideanSpace.single i 1) := by
    simp only [fundamentalGradientExpression, smul_apply, innerSL_apply_apply,
      EuclideanSpace.inner_single_right, one_mul, conj_trivial, smul_eq_mul]
  rw [heq, ← Real.norm_eq_abs]
  calc
    _ ≤ ‖fundamentalGradientExpression z‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = _ := by
      rw [fundamentalGradientExpression_norm hn z hz, PiLp.norm_single,
        norm_one, mul_one]

theorem normalizedRadialColumn_abs_integral_bound {n : ℕ} (hn : 0 < n) (i : Fin n) :
    (∫ z in Metric.ball (0 : Domain n) 3,
      ‖(euclideanSphereArea n)⁻¹ * ‖z‖ ^ (-(n : ℝ)) * z i‖) ≤ 3 := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hi := (normalizedRadialColumn_locallyIntegrable hn i).integrableOn_isCompact
    (isCompact_closedBall (0 : Domain n) 3)
  have hp := (norm_rpow_locallyIntegrable hn (p := 1 - (n : ℝ)) (by linarith only [])).integrableOn_isCompact (isCompact_closedBall (0 : Domain n) 3)
  calc
    _ ≤ ∫ z in Metric.ball (0 : Domain n) 3,
        (euclideanSphereArea n)⁻¹ * ‖z‖ ^ (1 - (n : ℝ)) := by
      apply integral_mono_ae (hi.mono_set Metric.ball_subset_closedBall).norm
        ((hp.mono_set Metric.ball_subset_closedBall).const_mul _)
      filter_upwards [ae_restrict_of_ae ((volume : Measure (Domain n)).ae_ne 0)] with z hz
      exact normalizedRadialColumn_abs_bound hn i z hz
    _ = 3 := by
      rw [integral_const_mul, radialPower_integral_ball hn (η := 1) one_pos (by norm_num)]
      have hS : euclideanSphereArea n ≠ 0 := (euclideanSphereArea_pos hn).ne'
      norm_num only [Real.rpow_one, div_one]
      rw [inv_mul_cancel_left₀ hS]

theorem potentialGradientColumn_unitData_norm_bound {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hn : 0 < n) (i : Fin n) {g : Domain n → E}
    (hg : Continuous g) (hcg : HasCompactSupport g)
    (hSupp : tsupport g ⊆ Metric.closedBall (0 : Domain n) 1)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ y, ‖g y‖ ≤ M)
    {x : Domain n} (hx : ‖x‖ ≤ 1) : ‖potentialGradientColumn i g x‖ ≤ 3 * M := by
  rw [potentialGradientColumn]
  exact (locallyIntegrableKernel_unitData_norm_bound
    (normalizedRadialColumn_locallyIntegrable hn i) hg hcg hSupp hM hbound hx).trans
      ((mul_le_mul_of_nonneg_left (normalizedRadialColumn_abs_integral_bound hn i) hM).trans_eq (mul_comm _ _))

theorem hessianKernelExpression_farIndicator_norm_bound {n : ℕ} (hn : 0 < n)
    (i j : Fin n) (z : Domain n) :
    ‖(Metric.ball (0 : Domain n) 1)ᶜ.indicator (hessianKernelExpression i j) z‖ ≤
      ((n : ℝ) + 1) * (euclideanSphereArea n)⁻¹ := by
  have hC : 0 ≤ ((n : ℝ) + 1) * (euclideanSphereArea n)⁻¹ :=
    mul_nonneg (by positivity) (inv_nonneg.mpr (euclideanSphereArea_pos hn).le)
  by_cases hz : z ∈ (Metric.ball (0 : Domain n) 1)ᶜ
  · rw [indicator_of_mem hz, Real.norm_eq_abs]
    have hnorm : 1 ≤ ‖z‖ := by
      simpa only [mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le hnorm)
    exact (hessianKernelExpression_bound hn i j z hz0).trans
      (mul_le_of_le_one_right hC (Real.rpow_le_one_of_one_le_of_nonpos hnorm
        (neg_nonpos.mpr (Nat.cast_nonneg n))))
  · rw [indicator_of_notMem hz, norm_zero]
    exact hC

theorem hessianKernelExpression_farIndicator_locallyIntegrable {n : ℕ} (hn : 0 < n)
    (i j : Fin n) :
    LocallyIntegrable ((Metric.ball (0 : Domain n) 1)ᶜ.indicator
      (hessianKernelExpression i j)) volume := by
  have hC : 0 ≤ ((n : ℝ) + 1) * (euclideanSphereArea n)⁻¹ :=
    mul_nonneg (by positivity) (inv_nonneg.mpr (euclideanSphereArea_pos hn).le)
  apply (locallyIntegrable_const (((n : ℝ) + 1) * (euclideanSphereArea n)⁻¹)).mono
    ((hessianKernelExpression_measurable i j).indicator measurableSet_ball.compl).aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_of_nonneg hC]
  exact hessianKernelExpression_farIndicator_norm_bound hn i j z

theorem potentialHessian_far_unitData_norm_bound {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hn : 0 < n) (i j : Fin n) {g : Domain n → E}
    (hg : Continuous g) (hcg : HasCompactSupport g)
    (hSupp : tsupport g ⊆ Metric.closedBall (0 : Domain n) 1)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ y, ‖g y‖ ≤ M)
    {x : Domain n} (hx : ‖x‖ ≤ 1) :
    ‖∫ z in (Metric.ball (0 : Domain n) 1)ᶜ, hessianKernelExpression i j z • g (x - z)‖ ≤
      (((n : ℝ) + 1) * (euclideanSphereArea n)⁻¹ *
        volume.real (Metric.ball (0 : Domain n) 3)) * M := by
  let k : Domain n → ℝ := (Metric.ball (0 : Domain n) 1)ᶜ.indicator (hessianKernelExpression i j)
  have hk := hessianKernelExpression_farIndicator_locallyIntegrable hn i j
  have heq : ((Metric.ball (0 : Domain n) 1)ᶜ.indicator
      (fun z => hessianKernelExpression i j z • g (x - z))) =
      (fun z => k z • g (x - z)) := by
    funext z
    by_cases hz : z ∈ (Metric.ball (0 : Domain n) 1)ᶜ
    · rw [indicator_of_mem hz]
      change _ = ((Metric.ball (0 : Domain n) 1)ᶜ.indicator (hessianKernelExpression i j) z) • _
      rw [indicator_of_mem hz]
    · rw [indicator_of_notMem hz]
      change _ = ((Metric.ball (0 : Domain n) 1)ᶜ.indicator (hessianKernelExpression i j) z) • _
      rw [indicator_of_notMem hz, zero_smul]
  rw [← integral_indicator measurableSet_ball.compl, heq]
  have hInt : (∫ z in Metric.ball (0 : Domain n) 3, ‖k z‖) ≤
      ((n : ℝ) + 1) * (euclideanSphereArea n)⁻¹ * volume.real (Metric.ball (0 : Domain n) 3) := by
    calc
      _ ≤ ∫ _z in Metric.ball (0 : Domain n) 3,
          ((n : ℝ) + 1) * (euclideanSphereArea n)⁻¹ := by
        apply integral_mono_ae
          ((hk.integrableOn_isCompact (isCompact_closedBall (0 : Domain n) 3)).mono_set
            Metric.ball_subset_closedBall).norm
          ((continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Domain n) 3)).mono_set
            Metric.ball_subset_closedBall)
        filter_upwards with z
        exact hessianKernelExpression_farIndicator_norm_bound hn i j z
      _ = _ := by
        rw [integral_const, smul_eq_mul, mul_comm]
        simp only [measureReal_def, Measure.restrict_apply_univ]
  exact (locallyIntegrableKernel_unitData_norm_bound hk hg hcg hSupp hM hbound hx).trans
    ((mul_le_mul_of_nonneg_left hInt hM).trans_eq (mul_comm _ _))

theorem potentialHessianExpression_unitData_norm_bound {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hn : 0 < n) (i j : Fin n) {g : Domain n → E} {η H M : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hHolder : HolderBoundOn univ g η H) (hcg : HasCompactSupport g)
    (hSupp : tsupport g ⊆ Metric.closedBall (0 : Domain n) 1)
    (hbound : ∀ y, ‖g y‖ ≤ M) {x : Domain n} (hx : ‖x‖ ≤ 1) :
    ‖potentialHessianExpression i j g x‖ ≤
      (1 / (n : ℝ) + ((n : ℝ) + 1) * (euclideanSphereArea n)⁻¹ *
        volume.real (Metric.ball (0 : Domain n) 3)) * M + ((n : ℝ) + 1) / η * H := by
  have hg : Continuous g := continuousOn_univ.mp (hHolder.continuousOn hη)
  have hdiag : ‖((if i = j then 1 else 0) / (n : ℝ)) • g x‖ ≤ (1 / (n : ℝ)) * M := by
    by_cases hij : i = j
    · rw [if_pos hij, norm_smul, Real.norm_of_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg n))]
      exact mul_le_mul_of_nonneg_left (hbound x) (one_div_nonneg.mpr (Nat.cast_nonneg n))
    · rw [if_neg hij, zero_div, zero_smul, norm_zero]
      exact mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg n)) hM
  have hnear := hessianKernelExpression_holderDifference_integral_bound hn i j hη hH
    (R := 1) one_pos hHolder x
  simp only [Real.one_rpow, mul_one] at hnear
  have hfar := potentialHessian_far_unitData_norm_bound hn i j hg hcg hSupp hM hbound hx
  rw [potentialHessianExpression]
  calc
    _ ≤ (‖((if i = j then 1 else 0) / (n : ℝ)) • g x‖ +
        ‖∫ z in Metric.ball (0 : Domain n) 1,
          hessianKernelExpression i j z • (g (x - z) - g x)‖) +
        ‖∫ z in (Metric.ball (0 : Domain n) 1)ᶜ,
          hessianKernelExpression i j z • g (x - z)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ((1 / (n : ℝ)) * M + ((n : ℝ) + 1) * H / η) +
        (((n : ℝ) + 1) * (euclideanSphereArea n)⁻¹ *
          volume.real (Metric.ball (0 : Domain n) 3)) * M :=
      add_le_add (add_le_add hdiag hnear) hfar
    _ = _ := by ring

end HolderToCK
end
