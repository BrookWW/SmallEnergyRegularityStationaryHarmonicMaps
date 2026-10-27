module

public import HolderToCK.Analysis.Poisson.PotentialRegularityMollification
public import HolderToCK.Analysis.Poisson.PotentialTrace
public import HolderToCK.Analysis.ClassicalPoisson

/-! # Classical second derivatives of the Newtonian potential of Holder data -/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff Convolution Topology

namespace HolderToCK

theorem potentialGradientColumn_continuous {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hn : 0 < n) (i : Fin n) {g : Domain n → E}
    (hg : Continuous g) (hcg : HasCompactSupport g) :
    Continuous (potentialGradientColumn i g) := by
  exact hcg.continuous_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    (normalizedRadialColumn_locallyIntegrable hn i) hg

theorem potentialGradientColumn_contDiff_smooth {n q : ℕ}
    (hn : 2 ≤ n) (j : Fin n) {g : Domain n → Ambient q}
    (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g) :
    ContDiff ℝ 1 (potentialGradientColumn j g) := by
  have hP : ContDiff ℝ 2 (newtonianPotential hn g) := newtonianPotential_contDiff hn hg hcg
  have heq : potentialGradientColumn j g =
      (fun x => fderiv ℝ (newtonianPotential hn g) x (EuclideanSpace.single j 1)) :=
    (funext fun x => newtonianPotential_column_eq_gradient hn j
      (hg.of_le (by norm_num)) hcg x).symm
  rw [heq]
  exact (hP.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem potentialHessianExpression_continuous_smooth {n q : ℕ}
    (hn : 2 ≤ n) (i j : Fin n) {g : Domain n → Ambient q} {η H : ℝ}
    (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H) :
    Continuous (potentialHessianExpression i j g) := by
  have hD := potentialGradientColumn_contDiff_smooth hn j hg hcg
  have heq : potentialHessianExpression i j g =
      (fun x => fderiv ℝ (potentialGradientColumn j g) x (EuclideanSpace.single i 1)) := by
    funext x
    rw [potentialGradientColumn_fderiv_eq_hessianLinearMap_smooth hn j hg hcg hη hH hHolder,
      potentialHessianColumnLinearMap, columnLinearMap_single]
  rw [heq]
  exact (hD.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem newtonianPotential_holder_hasFDerivAt {n q : ℕ}
    (hn : 2 ≤ n) {g : Domain n → Ambient q} {η H : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H)
    (hcg : HasCompactSupport g) (x : Domain n) :
    HasFDerivAt (newtonianPotential hn g) (potentialGradientLinearMap g x) x := by
  have hg : Continuous g := continuousOn_univ.mp (hHolder.continuousOn hη)
  let R : ℝ := ‖x‖ + 1
  have hValue := compactDataMollification_potential_tendstoUniformlyOn hn hη hH hHolder hcg R
  have hDerivative := compactDataMollification_fderivPotential_tendstoUniformlyOn hn
    hη hH hHolder hcg R
  apply hasFDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball
    (hDerivative.mono Metric.ball_subset_closedBall)
  · intro k y _
    have hm := newtonianPotential_contDiff hn
      (compactDataMollification_contDiff hg (compactDataApproximationScale k))
      (compactDataMollification_hasCompactSupport hcg _)
    exact (hm.differentiable (by simp)).differentiableAt.hasFDerivAt
  · intro y hy
    exact hValue.tendsto_at (Metric.ball_subset_closedBall hy)
  · rw [Metric.mem_ball, dist_zero_right]
    exact lt_add_one _

theorem potentialGradientColumn_holder_hasFDerivAt {n q : ℕ}
    (hn : 2 ≤ n) (j : Fin n) {g : Domain n → Ambient q} {η H : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H)
    (hcg : HasCompactSupport g) (x : Domain n) :
    HasFDerivAt (potentialGradientColumn j g) (potentialHessianColumnLinearMap j g x) x := by
  have hg : Continuous g := continuousOn_univ.mp (hHolder.continuousOn hη)
  let R : ℝ := ‖x‖ + 1
  have hValue := compactDataMollification_gradient_tendstoUniformlyOn (by omega) j
    hη hH hHolder hcg R
  have hDerivative := compactDataMollification_fderivGradient_tendstoUniformlyOn hn j
    hη hH hHolder hcg R
  apply hasFDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball
    (hDerivative.mono Metric.ball_subset_closedBall)
  · intro k y _
    have hm := potentialGradientColumn_contDiff_smooth hn j
      ((compactDataMollification_contDiff hg (compactDataApproximationScale k)).of_le
        (WithTop.coe_le_coe.mpr le_top))
      (compactDataMollification_hasCompactSupport hcg _)
    exact (hm.differentiable one_ne_zero).differentiableAt.hasFDerivAt
  · intro y hy
    exact hValue.tendsto_at (Metric.ball_subset_closedBall hy)
  · rw [Metric.mem_ball, dist_zero_right]
    exact lt_add_one _

theorem potentialHessianExpression_holder_continuous {n q : ℕ}
    (hn : 2 ≤ n) (i j : Fin n) {g : Domain n → Ambient q} {η H : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H)
    (hcg : HasCompactSupport g) : Continuous (potentialHessianExpression i j g) := by
  have hg : Continuous g := continuousOn_univ.mp (hHolder.continuousOn hη)
  apply continuous_iff_continuousAt.mpr
  intro x
  let R : ℝ := ‖x‖ + 1
  have hlim := compactDataMollification_hessian_tendstoUniformlyOn (by omega) i j
    hη hH hHolder hcg R
  have hcont : ContinuousOn (potentialHessianExpression i j g)
      (Metric.ball (0 : Domain n) R) :=
    (hlim.mono Metric.ball_subset_closedBall).continuousOn
      (Eventually.of_forall fun k =>
        (potentialHessianExpression_continuous_smooth hn i j
          ((compactDataMollification_contDiff hg _).of_le (WithTop.coe_le_coe.mpr le_top))
          (compactDataMollification_hasCompactSupport hcg _) hη hH
          (compactDataMollification_holderBound hη hH hHolder _)).continuousOn).frequently
  apply hcont.continuousAt
  apply Metric.isOpen_ball.mem_nhds
  rw [Metric.mem_ball, dist_zero_right]
  exact lt_add_one _

theorem potentialGradientColumn_holder_contDiff_one {n q : ℕ}
    (hn : 2 ≤ n) (j : Fin n) {g : Domain n → Ambient q} {η H : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H)
    (hcg : HasCompactSupport g) : ContDiff ℝ 1 (potentialGradientColumn j g) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨potentialHessianColumnLinearMap j g, ?_,
    potentialGradientColumn_holder_hasFDerivAt hn j hη hH hHolder hcg⟩
  apply continuous_finsetSum Finset.univ
  intro i _
  exact (((ContinuousLinearMap.smulRightL ℝ (Domain n) (Ambient q))
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i)).continuous.comp
      (potentialHessianExpression_holder_continuous hn i j hη hH hHolder hcg))

theorem newtonianPotential_holder_contDiff_two {n q : ℕ}
    (hn : 2 ≤ n) {g : Domain n → Ambient q} {η H : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H)
    (hcg : HasCompactSupport g) : ContDiff ℝ 2 (newtonianPotential hn g) := by
  apply (contDiff_succ_iff_hasFDerivAt (n := 1)).mpr
  refine ⟨potentialGradientLinearMap g, ?_,
    newtonianPotential_holder_hasFDerivAt hn hη hH hHolder hcg⟩
  apply ContDiff.sum
  intro i _
  exact (((ContinuousLinearMap.smulRightL ℝ (Domain n) (Ambient q))
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i)).contDiff.comp
      (potentialGradientColumn_holder_contDiff_one hn i hη hH hHolder hcg))

theorem newtonianPotential_holder_column_eq_gradient {n q : ℕ}
    (hn : 2 ≤ n) (j : Fin n) {g : Domain n → Ambient q} {η H : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H)
    (hcg : HasCompactSupport g) (x : Domain n) :
    fderiv ℝ (newtonianPotential hn g) x (EuclideanSpace.single j 1) =
      potentialGradientColumn j g x := by
  rw [(newtonianPotential_holder_hasFDerivAt hn hη hH hHolder hcg x).fderiv,
    potentialGradientLinearMap, columnLinearMap_single]

theorem newtonianPotential_holder_mixedColumns_eq_hessian {n q : ℕ}
    (hn : 2 ≤ n) (i j : Fin n) {g : Domain n → Ambient q} {η H : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H)
    (hcg : HasCompactSupport g) (x : Domain n) :
    fderiv ℝ (fun y => fderiv ℝ (newtonianPotential hn g) y
      (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1) =
      potentialHessianExpression i j g x := by
  have heq : (fun y => fderiv ℝ (newtonianPotential hn g) y (EuclideanSpace.single j 1)) =
      potentialGradientColumn j g :=
    funext (newtonianPotential_holder_column_eq_gradient hn j hη hH hHolder hcg)
  rw [heq, (potentialGradientColumn_holder_hasFDerivAt hn j hη hH hHolder hcg x).fderiv,
    potentialHessianColumnLinearMap, columnLinearMap_single]

theorem newtonianPotential_holder_laplacian {n q : ℕ}
    (hn : 2 ≤ n) {g : Domain n → Ambient q} {η H : ℝ}
    (hη : 0 < η) (hH : 0 ≤ H) (hHolder : HolderBoundOn univ g η H)
    (hcg : HasCompactSupport g) (x : Domain n) :
    Laplacian.laplacian (newtonianPotential hn g) x = g x := by
  rw [laplacian_eq_coordinateSum_of_contDiffAt_two _ x
    (newtonianPotential_holder_contDiff_two hn hη hH hHolder hcg).contDiffAt]
  calc
    _ = ∑ i : Fin n, potentialHessianExpression i i g x := by
      apply Finset.sum_congr rfl
      intro i _
      exact newtonianPotential_holder_mixedColumns_eq_hessian hn i i hη hH hHolder hcg x
    _ = _ := potentialHessianExpression_trace (by omega) hη hH hHolder hcg x

end HolderToCK
end
