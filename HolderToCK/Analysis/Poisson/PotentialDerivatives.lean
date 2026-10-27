module

public import HolderToCK.Analysis.Poisson.HolderPotential
public import HolderToCK.Analysis.Poisson.PotentialHessianIntegrability

/-! # The near-far Hessian formula for Newtonian potentials -/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology

namespace HolderToCK

@[expose] noncomputable def potentialHessianExpression {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i j : Fin n) (g : Domain n → E) (x : Domain n) : E :=
  ((if i = j then 1 else 0) / (n : ℝ)) • g x +
    (∫ z in Metric.ball (0 : Domain n) 1,
      hessianKernelExpression i j z • (g (x - z) - g x)) +
    ∫ z in (Metric.ball (0 : Domain n) 1)ᶜ,
      hessianKernelExpression i j z • g (x - z)

theorem hessianCompensated_integrable {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hn : 0 < n) (i j : Fin n) {g : Domain n → E} {η H : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H)
    (hcg : HasCompactSupport g) (x : Domain n) :
    Integrable (fun z => hessianKernelExpression i j z •
      (g (x - z) - fundamentalTestCutoff z • g x)) volume := by
  have hg : Continuous g := continuousOn_univ.mp (hHolder.continuousOn hη)
  have hnear : IntegrableOn (fun z => hessianKernelExpression i j z •
      (g (x - z) - fundamentalTestCutoff z • g x)) (Metric.ball (0 : Domain n) 1) := by
    apply (hessianKernelExpression_holderDifference_integrableOn hn i j hη hH hHolder x).congr_fun
      ?_ measurableSet_ball
    intro z hz
    dsimp only
    rw [fundamentalTestCutoff_eq_one z ((by
      simpa only [Metric.mem_ball, dist_zero_right] using hz : ‖z‖ < 1).le), one_smul]
  have htest : HasCompactSupport (fun z => g (x - z) - fundamentalTestCutoff z • g x) :=
    (hcg.comp_homeomorph (Homeomorph.subLeft x)).sub
      fundamentalTestCutoff_hasCompactSupport.smul_right
  have hfar : IntegrableOn (fun z => hessianKernelExpression i j z •
      (g (x - z) - fundamentalTestCutoff z • g x)) (Metric.ball (0 : Domain n) 1)ᶜ :=
    hessianKernelExpression_smul_testIntegrableOn_exterior i j
      ((hg.comp (continuous_const.sub continuous_id)).sub
        (fundamentalTestCutoff_contDiff.continuous.smul continuous_const)) htest one_pos
  rw [← integrableOn_univ, ← union_compl_self (Metric.ball (0 : Domain n) 1)]
  exact hnear.union hfar

theorem hessianCompensated_integral_eq {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hn : 0 < n) (i j : Fin n) {g : Domain n → E} {η H : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H)
    (hcg : HasCompactSupport g) (x : Domain n) :
    (∫ z, hessianKernelExpression i j z •
      (g (x - z) - fundamentalTestCutoff z • g x)) =
      (∫ z in Metric.ball (0 : Domain n) 1,
        hessianKernelExpression i j z • (g (x - z) - g x)) +
      ∫ z in (Metric.ball (0 : Domain n) 1)ᶜ,
        hessianKernelExpression i j z • g (x - z) := by
  have hi := hessianCompensated_integrable hn i j hη hH hHolder hcg x
  rw [← integral_add_compl measurableSet_ball hi]
  congr 1
  · apply setIntegral_congr_fun measurableSet_ball
    intro z hz
    dsimp only
    rw [fundamentalTestCutoff_eq_one z ((by
      simpa only [Metric.mem_ball, dist_zero_right] using hz : ‖z‖ < 1).le), one_smul]
  · have hfar := hessianKernelExpression_farHolder_integrableOn i j hη hHolder hcg x
    have hχ := hessianKernelExpression_testIntegrableOn_exterior i j
      fundamentalTestCutoff_contDiff.continuous fundamentalTestCutoff_hasCompactSupport one_pos
    simp_rw [smul_sub, smul_smul]
    rw [integral_sub hfar (hχ.smul_const (g x)), integral_smul_const,
      hessianKernelExpression_cutoffTruncation hn i j one_pos, zero_smul, sub_zero]

theorem potentialHessianExpression_principalValue {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hn : 0 < n) (i j : Fin n) {g : Domain n → E} {η H : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H)
    (hcg : HasCompactSupport g) (x : Domain n) :
    Tendsto (fun r : ℝ =>
      (∫ z in (Metric.ball (0 : Domain n) r)ᶜ, hessianKernelExpression i j z • g (x - z)) +
        ((if i = j then 1 else 0) / (n : ℝ)) • g x) (𝓝[>] 0)
      (𝓝 (potentialHessianExpression i j g x)) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let F : Domain n → E := fun z => hessianKernelExpression i j z •
    (g (x - z) - fundamentalTestCutoff z • g x)
  have hi : Integrable F volume := hessianCompensated_integrable hn i j hη hH hHolder hcg x
  have ht := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[>] (0 : ℝ)) (f := F) (fun z => ‖F z‖)
    (Eventually.of_forall (fun r : ℝ => hi.aestronglyMeasurable.indicator measurableSet_ball.compl))
    (Eventually.of_forall (fun r : ℝ => Eventually.of_forall (fun z : Domain n =>
      norm_indicator_le_norm_self (s := (Metric.ball (0 : Domain n) r)ᶜ) F z))) hi.norm ?_
  · simp only [integral_indicator measurableSet_ball.compl] at ht
    have hext (r : ℝ) (hr : 0 < r) :
        (∫ z in (Metric.ball (0 : Domain n) r)ᶜ, hessianKernelExpression i j z • g (x - z)) =
          ∫ z in (Metric.ball (0 : Domain n) r)ᶜ, F z := by
      have hχ := hessianKernelExpression_testIntegrableOn_exterior i j
        fundamentalTestCutoff_contDiff.continuous fundamentalTestCutoff_hasCompactSupport hr
      have heq : (fun z => hessianKernelExpression i j z • g (x - z)) =
          (fun z => F z + (hessianKernelExpression i j z * fundamentalTestCutoff z) • g x) := by
        funext z
        dsimp only [F]
        rw [smul_sub, smul_smul, sub_add_cancel]
      rw [heq, integral_add hi.integrableOn (hχ.smul_const (g x)), integral_smul_const,
        hessianKernelExpression_cutoffTruncation hn i j hr, zero_smul, add_zero]
    have hlim := ht.add_const (((if i = j then 1 else 0) / (n : ℝ)) • g x)
    have heqvalue : (∫ z, F z) + ((if i = j then 1 else 0) / (n : ℝ)) • g x =
        potentialHessianExpression i j g x := by
      rw [show (∫ z, F z) = ∫ z, hessianKernelExpression i j z •
          (g (x - z) - fundamentalTestCutoff z • g x) by rfl,
        hessianCompensated_integral_eq hn i j hη hH hHolder hcg x,
        potentialHessianExpression]
      abel
    rw [heqvalue] at hlim
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [hext r hr]
  · filter_upwards [(volume : Measure (Domain n)).ae_ne 0] with z hz
    apply tendsto_const_nhds.congr'
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (norm_pos_iff.mpr hz))] with r hr
    rw [indicator_of_mem (show z ∈ (Metric.ball (0 : Domain n) r)ᶜ from
      (by simpa only [mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hr.le))]

theorem compactData_sub_hasFDerivAt {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Domain n → E} (hg : ContDiff ℝ 1 g) (x z : Domain n) :
    HasFDerivAt (fun w => g (x - w)) (-fderiv ℝ g (x - z)) z := by
  have hd := (hg.differentiable one_ne_zero (x - z)).hasFDerivAt.comp z
    ((hasFDerivAt_id z).const_sub x)
  simpa only [Function.comp_def, ContinuousLinearMap.comp_neg,
    ContinuousLinearMap.comp_id] using hd

theorem compactData_sub_mixedColumns {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Domain n → E} (hg : ContDiff ℝ 2 g) (x z : Domain n) (i j : Fin n) :
    fderiv ℝ (fun w => fderiv ℝ (fun v => g (x - v)) w (EuclideanSpace.single j 1)) z
      (EuclideanSpace.single i 1) =
      fderiv ℝ (fun w => fderiv ℝ g w (EuclideanSpace.single j 1)) (x - z)
        (EuclideanSpace.single i 1) := by
  let D : Domain n → E := fun w => fderiv ℝ g w (EuclideanSpace.single j 1)
  have hD : ContDiff ℝ 1 D :=
    (hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have heq : (fun w => fderiv ℝ (fun v => g (x - v)) w (EuclideanSpace.single j 1)) =
      (fun w => -D (x - w)) := by
    funext w
    rw [(compactData_sub_hasFDerivAt (hg.of_le (by norm_num)) x w).fderiv]
    rfl
  rw [heq]
  change fderiv ℝ (-(fun w => D (x - w))) z (EuclideanSpace.single i 1) = _
  rw [(compactData_sub_hasFDerivAt hD x z).neg.fderiv, neg_neg]

theorem newtonianPotential_mixedColumns_eq_hessian_scalar {n : ℕ}
    (hn : 2 ≤ n) (i j : Fin n) {g : Domain n → ℝ} {η H : ℝ}
    (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H) (x : Domain n) :
    fderiv ℝ (fun y => fderiv ℝ (newtonianPotential hn g) y
      (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1) =
      potentialHessianExpression i j g x := by
  let φ : Domain n → ℝ := fun z => g (x - z)
  have hφ : ContDiff ℝ 2 φ := hg.comp (contDiff_const.sub contDiff_id)
  have hcφ : HasCompactSupport φ := hcg.comp_homeomorph (Homeomorph.subLeft x)
  have ht := fundamentalSolution_hessianDistributionPairing hn i j hφ hcφ
  have hφ0 : φ 0 = g x := by dsimp only [φ]; rw [sub_zero]
  have hHess : (∫ z : {z : Domain n // z ≠ 0}, fundamentalSolution n hn z *
      fderiv ℝ (fun w => fderiv ℝ φ w (EuclideanSpace.single j 1)) z.val
        (EuclideanSpace.single i 1)
      ∂(volume : Measure (Domain n)).comap
        (Subtype.val : {z : Domain n // z ≠ 0} → Domain n)) =
      fderiv ℝ (fun y => fderiv ℝ (newtonianPotential hn g) y
        (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1) := by
    rw [newtonianPotential_mixedColumns_data hn hg hcg, newtonianPotential]
    apply integral_congr_ae
    filter_upwards with z
    rw [compactData_sub_mixedColumns hg x z.val i j]
    rfl
  rw [hφ0, hHess] at ht
  exact tendsto_nhds_unique ht (potentialHessianExpression_principalValue
    (by omega : 0 < n) i j hη hH hHolder hcg x)

theorem compactData_clm_mixedColumns {n : ℕ}
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    {g : Domain n → E} (hg : ContDiff ℝ 2 g) (x : Domain n) (i j : Fin n) :
    fderiv ℝ (fun z => fderiv ℝ (fun w => L (g w)) z (EuclideanSpace.single j 1)) x
      (EuclideanSpace.single i 1) =
      L (fderiv ℝ (fun z => fderiv ℝ g z (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single i 1)) := by
  have heq : (fun z => fderiv ℝ (fun w => L (g w)) z (EuclideanSpace.single j 1)) =
      (fun z => L (fderiv ℝ g z (EuclideanSpace.single j 1))) := by
    funext z
    have hd := L.hasFDerivAt.comp z
      (hg.differentiable (by norm_num) z).hasFDerivAt
    simp only [Function.comp_def] at hd
    rw [hd.fderiv]
    rfl
  rw [heq]
  have hD : ContDiff ℝ 1 (fun z => fderiv ℝ g z (EuclideanSpace.single j 1)) :=
    (hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hd := L.hasFDerivAt.comp x (hD.differentiable one_ne_zero x).hasFDerivAt
  simp only [Function.comp_def] at hd
  rw [hd.fderiv]
  rfl

theorem potentialHessianExpression_applyCLM {n : ℕ}
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (hn : 0 < n) (i j : Fin n) (L : E →L[ℝ] F)
    {g : Domain n → E} {η H : ℝ} (hη : 0 < η) (hH : 0 ≤ H)
    (hHolder : HolderBoundOn univ g η H) (hcg : HasCompactSupport g) (x : Domain n) :
    L (potentialHessianExpression i j g x) =
      potentialHessianExpression i j (fun z => L (g z)) x := by
  have hnear := hessianKernelExpression_holderDifference_integrableOn hn i j hη hH hHolder x
    (R := 1)
  have hfar := hessianKernelExpression_farHolder_integrableOn i j hη hHolder hcg x
  simp only [potentialHessianExpression, map_add, map_smul]
  rw [← L.integral_comp_comm hnear, ← L.integral_comp_comm hfar]
  simp only [map_smul, map_sub]

theorem newtonianPotential_mixedColumns_eq_hessian {n q : ℕ}
    (hn : 2 ≤ n) (i j : Fin n) {g : Domain n → Ambient q} {η H : ℝ}
    (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H) (x : Domain n) :
    fderiv ℝ (fun y => fderiv ℝ (newtonianPotential hn g) y
      (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1) =
      potentialHessianExpression i j g x := by
  ext a
  let L : Ambient q →L[ℝ] ℝ := PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin q => ℝ) a
  change L (fderiv ℝ (fun y => fderiv ℝ (newtonianPotential hn g) y
    (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)) =
      L (potentialHessianExpression i j g x)
  have hD : ContDiff ℝ 1 (fun z => fderiv ℝ g z (EuclideanSpace.single j 1)) :=
    (hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hDD : Continuous (fun z =>
      fderiv ℝ (fun w => fderiv ℝ g w (EuclideanSpace.single j 1)) z
        (EuclideanSpace.single i 1)) :=
    (hD.continuous_fderiv one_ne_zero).clm_apply continuous_const
  rw [newtonianPotential_mixedColumns_data hn hg hcg,
    newtonianPotential_applyCLM hn L hDD ((hcg.fderiv_apply ℝ _).fderiv_apply ℝ _) x,
    potentialHessianExpression_applyCLM (by omega : 0 < n) i j L hη hH hHolder hcg x]
  have hHolderL : HolderBoundOn univ (fun z => L (g z)) η (‖L‖ * H) := by
    intro y hy z hz
    rw [← L.map_sub]
    calc
      _ ≤ ‖L‖ * ‖g y - g z‖ := L.le_opNorm _
      _ ≤ ‖L‖ * (H * Real.rpow (dist y z) η) :=
        mul_le_mul_of_nonneg_left (hHolder y hy z hz) (norm_nonneg _)
      _ = _ := by ring
  have hgL : ContDiff ℝ 2 (fun z => L (g z)) := L.contDiff.comp hg
  have hcgL : HasCompactSupport (fun z => L (g z)) := hcg.comp_left L.map_zero
  have hs := newtonianPotential_mixedColumns_eq_hessian_scalar hn i j hgL hcgL hη
    (mul_nonneg (norm_nonneg _) hH) hHolderL x
  rw [newtonianPotential_mixedColumns_data hn hgL hcgL] at hs
  have heq : (fun z =>
      fderiv ℝ (fun w => fderiv ℝ (fun v => L (g v)) w (EuclideanSpace.single j 1)) z
        (EuclideanSpace.single i 1)) =
      (fun z => L (fderiv ℝ (fun w => fderiv ℝ g w (EuclideanSpace.single j 1)) z
        (EuclideanSpace.single i 1))) :=
    funext (fun z => compactData_clm_mixedColumns L hg z i j)
  rw [heq] at hs
  exact hs

end HolderToCK
end
