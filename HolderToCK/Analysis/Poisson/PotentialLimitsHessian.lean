module

public import HolderToCK.Analysis.Poisson.PotentialLimitsKernel
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Radius splitting and uniform limits of the potential Hessian formula -/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Convolution Topology

namespace HolderToCK

@[expose] noncomputable def hessianExteriorKernel {n : ℕ} (i j : Fin n)
    (r : ℝ) (z : Domain n) : ℝ :=
  (Metric.ball (0 : Domain n) r)ᶜ.indicator (hessianKernelExpression i j) z

theorem hessianExteriorKernel_norm_bound {n : ℕ} (hn : 0 < n) (i j : Fin n)
    {r : ℝ} (hr : 0 < r) (z : Domain n) :
    ‖hessianExteriorKernel i j r z‖ ≤
      ((n : ℝ) + 1) * (euclideanSphereArea n)⁻¹ * r ^ (-(n : ℝ)) := by
  have hC : 0 ≤ ((n : ℝ) + 1) * (euclideanSphereArea n)⁻¹ :=
    mul_nonneg (by positivity) (inv_nonneg.mpr (euclideanSphereArea_pos hn).le)
  by_cases hz : z ∈ (Metric.ball (0 : Domain n) r)ᶜ
  · rw [hessianExteriorKernel, indicator_of_mem hz, Real.norm_eq_abs]
    have hnorm : r ≤ ‖z‖ := by
      simpa only [mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (hr.trans_le hnorm)
    exact (hessianKernelExpression_bound hn i j z hz0).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hr hnorm
        (neg_nonpos.mpr (Nat.cast_nonneg n))) hC)
  · rw [hessianExteriorKernel, indicator_of_notMem hz, norm_zero]
    exact mul_nonneg hC (Real.rpow_nonneg hr.le _)

theorem hessianExteriorKernel_locallyIntegrable {n : ℕ} (hn : 0 < n) (i j : Fin n)
    {r : ℝ} (hr : 0 < r) : LocallyIntegrable (hessianExteriorKernel i j r) volume := by
  have hC : 0 ≤ ((n : ℝ) + 1) * (euclideanSphereArea n)⁻¹ * r ^ (-(n : ℝ)) :=
    mul_nonneg (mul_nonneg (by positivity)
      (inv_nonneg.mpr (euclideanSphereArea_pos hn).le)) (Real.rpow_nonneg hr.le _)
  apply (locallyIntegrable_const
    (((n : ℝ) + 1) * (euclideanSphereArea n)⁻¹ * r ^ (-(n : ℝ)))).mono
    ((hessianKernelExpression_measurable i j).indicator measurableSet_ball.compl).aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_of_nonneg hC]
  exact hessianExteriorKernel_norm_bound hn i j hr z

theorem hessianExteriorKernel_integral {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i j : Fin n) (g : Domain n → E) (r : ℝ) (x : Domain n) :
    (∫ z, hessianExteriorKernel i j r z • g (x - z)) =
      ∫ z in (Metric.ball (0 : Domain n) r)ᶜ,
        hessianKernelExpression i j z • g (x - z) := by
  rw [← integral_indicator measurableSet_ball.compl]
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : z ∈ (Metric.ball (0 : Domain n) r)ᶜ
  · rw [hessianExteriorKernel, indicator_of_mem hz, indicator_of_mem hz]
  · rw [hessianExteriorKernel, indicator_of_notMem hz, indicator_of_notMem hz, zero_smul]

theorem potentialHessianExpression_splitRadius {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hn : 0 < n) (i j : Fin n) {g : Domain n → E} {η H r : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H)
    (hcg : HasCompactSupport g) (hr : 0 < r) (hr1 : r ≤ 1) (x : Domain n) :
    potentialHessianExpression i j g x =
      (((if i = j then 1 else 0) / (n : ℝ)) • g x +
        ∫ z in Metric.ball (0 : Domain n) r,
          hessianKernelExpression i j z • (g (x - z) - g x)) +
      ∫ z in (Metric.ball (0 : Domain n) r)ᶜ,
        hessianKernelExpression i j z • g (x - z) := by
  have hg : Continuous g := continuousOn_univ.mp (hHolder.continuousOn hη)
  have hi := hessianCompensated_integrable hn i j hη hH hHolder hcg x
  have hsplit : (∫ z, hessianKernelExpression i j z •
      (g (x - z) - fundamentalTestCutoff z • g x)) =
      (∫ z in Metric.ball (0 : Domain n) r,
        hessianKernelExpression i j z • (g (x - z) - g x)) +
      ∫ z in (Metric.ball (0 : Domain n) r)ᶜ,
        hessianKernelExpression i j z • g (x - z) := by
    rw [← integral_add_compl measurableSet_ball hi]
    congr 1
    · apply setIntegral_congr_fun measurableSet_ball
      intro z hz
      dsimp only
      have hz1 : ‖z‖ ≤ 1 :=
        (show ‖z‖ < r by simpa only [Metric.mem_ball, dist_zero_right] using hz).le.trans hr1
      rw [fundamentalTestCutoff_eq_one z hz1, one_smul]
    · have hfar : IntegrableOn (fun z => hessianKernelExpression i j z • g (x - z))
          (Metric.ball (0 : Domain n) r)ᶜ volume :=
        hessianKernelExpression_smul_testIntegrableOn_exterior i j
        (hg.comp (continuous_const.sub continuous_id))
        (hcg.comp_homeomorph (Homeomorph.subLeft x)) hr
      have hχ := hessianKernelExpression_testIntegrableOn_exterior i j
        fundamentalTestCutoff_contDiff.continuous fundamentalTestCutoff_hasCompactSupport hr
      simp_rw [smul_sub, smul_smul]
      rw [integral_sub hfar (hχ.smul_const (g x)), integral_smul_const,
        hessianKernelExpression_cutoffTruncation hn i j hr, zero_smul, sub_zero]
  rw [potentialHessianExpression, add_assoc,
    ← hessianCompensated_integral_eq hn i j hη hH hHolder hcg x, hsplit]
  abel

theorem hessianKernelExpression_cutoffDefect_ball {n : ℕ} (hn : 0 < n)
    (i j : Fin n) {r : ℝ} (hr : 1 ≤ r) :
    IntegrableOn (fun z => hessianKernelExpression i j z * (1 - fundamentalTestCutoff z))
      (Metric.ball (0 : Domain n) r) volume ∧
    (∫ z in Metric.ball (0 : Domain n) r,
      hessianKernelExpression i j z * (1 - fundamentalTestCutoff z)) = 0 := by
  have hprofile : Continuous (fun t : ℝ => 1 - fundamentalTestCutoffProfile t) :=
    continuous_const.sub fundamentalTestCutoffProfile_contDiff.continuous
  obtain ⟨hi, hpolar⟩ := integral_weighted_annulus_eq_polar hn one_pos hr
    (hessianKernelExpression_integrableOn_annulus i j one_pos)
    hprofile.continuousOn
  have heq : (fun z : Domain n => (1 - fundamentalTestCutoffProfile ‖z - 0‖) *
      hessianKernelExpression i j z) =
      (fun z => hessianKernelExpression i j z * (1 - fundamentalTestCutoff z)) := by
    funext z
    rw [sub_zero, fundamentalTestCutoff, mul_comm]
  rw [heq] at hi hpolar
  have hzero : ∀ z ∈ Metric.ball (0 : Domain n) r \
      (Metric.ball (0 : Domain n) r \ Metric.ball (0 : Domain n) 1),
      hessianKernelExpression i j z * (1 - fundamentalTestCutoff z) = 0 := by
    intro z hz
    have hz1 : z ∈ Metric.ball (0 : Domain n) 1 := by
      by_contra hnot
      exact hz.2 ⟨hz.1, hnot⟩
    rw [fundamentalTestCutoff_eq_one z
      ((show ‖z‖ < 1 by simpa only [Metric.mem_ball, dist_zero_right] using hz1).le),
      sub_self, mul_zero]
  refine ⟨hi.of_forall_sdiff_eq_zero measurableSet_ball hzero, ?_⟩
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball
    (fun _ hz => hz.1) hzero, hpolar]
  calc
    _ = ∫ _ in (1 : ℝ)..r, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc (1 : ℝ) r := by simpa only [uIcc_of_le hr] using ht
      simp only [zero_add]
      rw [hessianKernelExpression_sphere_cancellation hn i j (one_pos.trans_le ht'.1),
        mul_zero, mul_zero]
    _ = 0 := intervalIntegral.integral_zero

theorem potentialHessianExpression_splitRadius_all {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hn : 0 < n) (i j : Fin n) {g : Domain n → E} {η H r : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H)
    (hcg : HasCompactSupport g) (hr : 0 < r) (x : Domain n) :
    potentialHessianExpression i j g x =
      (((if i = j then 1 else 0) / (n : ℝ)) • g x +
        ∫ z in Metric.ball (0 : Domain n) r,
          hessianKernelExpression i j z • (g (x - z) - g x)) +
      ∫ z in (Metric.ball (0 : Domain n) r)ᶜ,
        hessianKernelExpression i j z • g (x - z) := by
  by_cases hr1 : r ≤ 1
  · exact potentialHessianExpression_splitRadius hn i j hη hH hHolder hcg hr hr1 x
  have h1r : 1 ≤ r := (lt_of_not_ge hr1).le
  have hg : Continuous g := continuousOn_univ.mp (hHolder.continuousOn hη)
  have hi := hessianCompensated_integrable hn i j hη hH hHolder hcg x
  have hnear := hessianKernelExpression_holderDifference_integrableOn hn i j hη hH hHolder x
    (R := r)
  obtain ⟨hdefect, hdefect0⟩ := hessianKernelExpression_cutoffDefect_ball hn i j h1r
  have hsplit : (∫ z, hessianKernelExpression i j z •
      (g (x - z) - fundamentalTestCutoff z • g x)) =
      (∫ z in Metric.ball (0 : Domain n) r,
        hessianKernelExpression i j z • (g (x - z) - g x)) +
      ∫ z in (Metric.ball (0 : Domain n) r)ᶜ,
        hessianKernelExpression i j z • g (x - z) := by
    rw [← integral_add_compl measurableSet_ball hi]
    congr 1
    · have heq : (fun z => hessianKernelExpression i j z •
          (g (x - z) - fundamentalTestCutoff z • g x)) =
          (fun z => hessianKernelExpression i j z • (g (x - z) - g x) +
            (hessianKernelExpression i j z * (1 - fundamentalTestCutoff z)) • g x) := by
        funext z
        rw [smul_sub, mul_sub, mul_one, sub_smul, smul_smul, smul_sub]
        abel
      rw [heq, integral_add hnear (hdefect.smul_const (g x)), integral_smul_const,
        hdefect0, zero_smul, add_zero]
    · have hfar : IntegrableOn (fun z => hessianKernelExpression i j z • g (x - z))
          (Metric.ball (0 : Domain n) r)ᶜ volume :=
        hessianKernelExpression_smul_testIntegrableOn_exterior i j
          (hg.comp (continuous_const.sub continuous_id))
          (hcg.comp_homeomorph (Homeomorph.subLeft x)) hr
      have hχ := hessianKernelExpression_testIntegrableOn_exterior i j
        fundamentalTestCutoff_contDiff.continuous fundamentalTestCutoff_hasCompactSupport hr
      simp_rw [smul_sub, smul_smul]
      rw [integral_sub hfar (hχ.smul_const (g x)), integral_smul_const,
        hessianKernelExpression_cutoffTruncation hn i j hr, zero_smul, sub_zero]
  rw [potentialHessianExpression, add_assoc,
    ← hessianCompensated_integral_eq hn i j hη hH hHolder hcg x, hsplit]
  abel

theorem potentialHessianExpression_tendstoUniformlyOn {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hn : 0 < n) (i j : Fin n) {F : ℕ → Domain n → E} {g : Domain n → E}
    {η H R S : ℝ} (hη : 0 < η) (hH : 0 ≤ H)
    (hFHolder : ∀ m, HolderBoundOn univ (F m) η H)
    (hgHolder : HolderBoundOn univ g η H)
    (hFS : ∀ m, tsupport (F m) ⊆ Metric.closedBall (0 : Domain n) S)
    (hgS : tsupport g ⊆ Metric.closedBall (0 : Domain n) S)
    (hlim : TendstoUniformly F g atTop) :
    TendstoUniformlyOn (fun m => potentialHessianExpression i j (F m))
      (potentialHessianExpression i j g) atTop (Metric.closedBall (0 : Domain n) R) := by
  have hF (m : ℕ) : Continuous (F m) :=
    continuousOn_univ.mp ((hFHolder m).continuousOn hη)
  have hg : Continuous g := continuousOn_univ.mp (hgHolder.continuousOn hη)
  have hcF (m : ℕ) : HasCompactSupport (F m) :=
    (isCompact_closedBall (0 : Domain n) S).of_isClosed_subset (isClosed_tsupport _) (hFS m)
  have hcg : HasCompactSupport g :=
    (isCompact_closedBall (0 : Domain n) S).of_isClosed_subset (isClosed_tsupport _) hgS
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let t : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have ht : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hAt : ContinuousAt (fun s : ℝ => ((n : ℝ) + 1) * H * s ^ η / η) 0 :=
    ((continuousAt_const.mul
      (continuousAt_id.rpow_const (Or.inr hη.le))).div_const η)
  have hnearLim : Tendsto (fun k => ((n : ℝ) + 1) * H * (t k) ^ η / η)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.zero_rpow hη.ne', mul_zero, zero_div] using
      hAt.tendsto.comp ht
  obtain ⟨k, hk⟩ := (hnearLim.eventually (gt_mem_nhds (by positivity : 0 < ε / 4))).exists
  let r : ℝ := t k
  have hr : 0 < r := by dsimp only [r, t]; positivity
  have hr1 : r ≤ 1 := by
    dsimp only [r, t]
    apply (div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)).mpr
    linarith only [Nat.cast_nonneg (α := ℝ) k]
  have hFar := locallyIntegrableKernel_tendstoUniformlyOn
    (hessianExteriorKernel_locallyIntegrable hn i j hr) hF hg hFS hgS hlim
    (R := R)
  have hFar' : TendstoUniformlyOn
      (fun m x => ∫ z in (Metric.ball (0 : Domain n) r)ᶜ,
        hessianKernelExpression i j z • F m (x - z))
      (fun x => ∫ z in (Metric.ball (0 : Domain n) r)ᶜ,
        hessianKernelExpression i j z • g (x - z)) atTop
      (Metric.closedBall (0 : Domain n) R) := by
    have heq : (fun (v : Domain n → E) x => ∫ z, hessianExteriorKernel i j r z • v (x - z)) =
        (fun v x => ∫ z in (Metric.ball (0 : Domain n) r)ᶜ,
          hessianKernelExpression i j z • v (x - z)) :=
      funext fun v => funext (hessianExteriorKernel_integral i j v r)
    change TendstoUniformlyOn
      (fun m => (fun (v : Domain n → E) x => ∫ z, hessianExteriorKernel i j r z • v (x - z)) (F m))
      ((fun (v : Domain n → E) x => ∫ z, hessianExteriorKernel i j r z • v (x - z)) g)
      atTop (Metric.closedBall (0 : Domain n) R) at hFar
    rw [heq] at hFar
    exact hFar
  let c : ℝ := (if i = j then 1 else 0) / (n : ℝ)
  have hδ : 0 < ε / (4 * (‖c‖ + 1)) := div_pos hε (by positivity)
  filter_upwards [Metric.tendstoUniformly_iff.mp hlim _ hδ,
    Metric.tendstoUniformlyOn_iff.mp hFar' (ε / 4) (by positivity)] with m hm hfar x hx
  have hdiag : ‖c • (g x - F m x)‖ < ε / 4 := by
    rw [norm_smul]
    have hd : ‖g x - F m x‖ ≤ ε / (4 * (‖c‖ + 1)) := by
      simpa only [dist_eq_norm] using (hm x).le
    calc
      _ ≤ ‖c‖ * (ε / (4 * (‖c‖ + 1))) :=
        mul_le_mul_of_nonneg_left hd (norm_nonneg _)
      _ < (‖c‖ + 1) * (ε / (4 * (‖c‖ + 1))) :=
        mul_lt_mul_of_pos_right (lt_add_one _) hδ
      _ = ε / 4 := by field_simp
  have hnearG := hessianKernelExpression_holderDifference_integral_bound hn i j hη hH hr
    hgHolder x
  have hnearF := hessianKernelExpression_holderDifference_integral_bound hn i j hη hH hr
    (hFHolder m) x
  have hfarNorm : ‖(∫ z in (Metric.ball (0 : Domain n) r)ᶜ,
      hessianKernelExpression i j z • g (x - z)) -
      ∫ z in (Metric.ball (0 : Domain n) r)ᶜ,
        hessianKernelExpression i j z • F m (x - z)‖ < ε / 4 := by
    simpa only [dist_eq_norm] using hfar x hx
  rw [dist_eq_norm,
    potentialHessianExpression_splitRadius hn i j hη hH hgHolder hcg hr hr1,
    potentialHessianExpression_splitRadius hn i j hη hH (hFHolder m) (hcF m) hr hr1]
  change ‖(c • g x + _) + _ - ((c • F m x + _) + _)‖ < ε
  rw [show (c • g x +
      (∫ z in Metric.ball (0 : Domain n) r,
        hessianKernelExpression i j z • (g (x - z) - g x))) +
      (∫ z in (Metric.ball (0 : Domain n) r)ᶜ,
        hessianKernelExpression i j z • g (x - z)) -
      ((c • F m x +
        (∫ z in Metric.ball (0 : Domain n) r,
          hessianKernelExpression i j z • (F m (x - z) - F m x))) +
        (∫ z in (Metric.ball (0 : Domain n) r)ᶜ,
          hessianKernelExpression i j z • F m (x - z))) =
      c • (g x - F m x) +
      ((∫ z in Metric.ball (0 : Domain n) r,
        hessianKernelExpression i j z • (g (x - z) - g x)) -
        ∫ z in Metric.ball (0 : Domain n) r,
          hessianKernelExpression i j z • (F m (x - z) - F m x)) +
      ((∫ z in (Metric.ball (0 : Domain n) r)ᶜ,
        hessianKernelExpression i j z • g (x - z)) -
        ∫ z in (Metric.ball (0 : Domain n) r)ᶜ,
          hessianKernelExpression i j z • F m (x - z)) by rw [smul_sub]; abel]
  have hnorm := (norm_add_le
    (c • (g x - F m x) +
      ((∫ z in Metric.ball (0 : Domain n) r,
        hessianKernelExpression i j z • (g (x - z) - g x)) -
        ∫ z in Metric.ball (0 : Domain n) r,
          hessianKernelExpression i j z • (F m (x - z) - F m x)))
    ((∫ z in (Metric.ball (0 : Domain n) r)ᶜ,
      hessianKernelExpression i j z • g (x - z)) -
      ∫ z in (Metric.ball (0 : Domain n) r)ᶜ,
        hessianKernelExpression i j z • F m (x - z))).trans
      (add_le_add ((norm_add_le _ _).trans
        (add_le_add le_rfl (norm_sub_le _ _))) le_rfl)
  change ((n : ℝ) + 1) * H * r ^ η / η < ε / 4 at hk
  exact hnorm.trans_lt (by linarith only [hdiag, hnearG, hnearF, hfarNorm, hk])

end HolderToCK
end
