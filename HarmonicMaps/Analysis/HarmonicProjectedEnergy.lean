module

public import HarmonicMaps.Analysis.HarmonicEnergyAlgebra
public import HarmonicMaps.Analysis.DirichletSmoothData
public import HarmonicMaps.Analysis.SobolevDifference

/-!
# Energy comparison after a smooth projection

The operator derivative bound two gives the factor four on HS energy.
Splitting the smoothing gradient into the harmonic gradient and its error
then gives the factor eight on each integral.
-/

public section

open MeasureTheory Set
open scoped ContDiff BigOperators

namespace HarmonicMaps

private theorem hsNormSq_le_twice_difference {n q : ℕ} (A B : Gradient n q) :
    hsNormSq A ≤ 2 * hsNormSq (A - B) + 2 * hsNormSq B := by
  have hpoint (a b : Ambient q) : ‖a‖ ^ 2 ≤ 2 * ‖a - b‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    have htriangle : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
      simpa only [sub_add_cancel] using norm_add_le (a - b) b
    nlinarith only [htriangle, norm_nonneg a, norm_nonneg (a - b), norm_nonneg b,
      sq_nonneg (‖a - b‖ - ‖b‖)]
  unfold hsNormSq
  simp only [Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => hpoint (A i) (B i))

/-- A smooth ambient projection with derivative norm at most two gives the
source energy comparison, with the literal harmonic error columns. -/
theorem harmonic_projectedEnergy_le {n q : ℕ}
    (P : Ambient q → Ambient q) (hP : ContDiff ℝ ∞ P)
    (m w : Domain n → Ambient q)
    (hm : ContDiffOn ℝ ∞ m (Metric.ball (0 : Domain n) (3 / 4 : ℝ)))
    (hw : MemW12 (ballDomain (0 : Domain n) (1 / 2 : ℝ)) w
      (fun x i => fderiv ℝ w x (EuclideanSpace.single i 1)))
    (hD : ∀ x ∈ Metric.ball (0 : Domain n) (1 / 2 : ℝ), ‖fderiv ℝ P (m x)‖ ≤ 2)
    (θ : ℝ) (_hθ : 0 < θ) (hθquarter : θ ≤ 1 / 4)
    (L : ℝ) (hgrad : ∀ x ∈ Metric.ball (0 : Domain n) (1 / 4 : ℝ),
      hsNormSq (fun i => fderiv ℝ w x (EuclideanSpace.single i 1)) ≤ L) :
    (∫ x in Metric.ball (0 : Domain n) θ, hsNormSq (fun i =>
      fderiv ℝ (P ∘ m) x (EuclideanSpace.single i 1))) ≤
      8 * (∫ x in Metric.ball (0 : Domain n) (1 / 2 : ℝ),
        hsNormSq (fun i => fderiv ℝ m x (EuclideanSpace.single i 1) -
          fderiv ℝ w x (EuclideanSpace.single i 1))) +
      8 * L * (volume : Measure (Domain n)).real (Metric.ball (0 : Domain n) θ) := by
  let B : Set (Domain n) := Metric.ball 0 (1 / 2 : ℝ)
  let T : Set (Domain n) := Metric.ball 0 θ
  let Dm : Domain n → Gradient n q := fun x i => fderiv ℝ m x (EuclideanSpace.single i 1)
  let Dw : Domain n → Gradient n q := fun x i => fderiv ℝ w x (EuclideanSpace.single i 1)
  let DP : Domain n → Gradient n q := fun x i => fderiv ℝ (P ∘ m) x (EuclideanSpace.single i 1)
  have hclosed : Metric.closedBall (0 : Domain n) (1 / 2 : ℝ) ⊆
      Metric.ball 0 (3 / 4) := Metric.closedBall_subset_ball (by norm_num)
  have hmW := dirichlet_smoothData_memW12 ⟨1 / 2, by norm_num⟩ _
    Metric.isOpen_ball hclosed m hm
  have hpm : ContDiffOn ℝ ∞ (P ∘ m) (Metric.ball (0 : Domain n) (3 / 4 : ℝ)) :=
    hP.contDiffOn.comp hm (mapsTo_univ _ _)
  have hpW := dirichlet_smoothData_memW12 ⟨1 / 2, by norm_num⟩ _
    Metric.isOpen_ball hclosed (P ∘ m) hpm
  have hsub : T ⊆ B := Metric.ball_subset_ball (by linarith only [hθquarter])
  have herror : IntegrableOn (fun x => hsNormSq (Dm x - Dw x)) B volume :=
    (hmW.sub hw).integrable_hsNormSq
  have hpoint (x : Domain n) (hx : x ∈ T) :
      hsNormSq (DP x) ≤ 8 * hsNormSq (Dm x - Dw x) + 8 * hsNormSq (Dw x) := by
    have hxB := hsub hx
    have hmdiff := (hm.contDiffAt (Metric.isOpen_ball.mem_nhds
      (hclosed (Metric.ball_subset_closedBall hxB)))).differentiableAt (by simp)
    have hpdiff : DifferentiableAt ℝ P (m x) :=
      (hP.differentiable (by simp)).differentiableAt
    have hchain := fderiv_comp x hpdiff hmdiff
    have hproj : hsNormSq (DP x) ≤ 4 * hsNormSq (Dm x) := by
      unfold hsNormSq
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      change ‖fderiv ℝ (P ∘ m) x (EuclideanSpace.single i 1)‖ ^ 2 ≤
        4 * ‖Dm x i‖ ^ 2
      rw [hchain, ContinuousLinearMap.comp_apply]
      have hb : ‖fderiv ℝ P (m x) (Dm x i)‖ ≤ 2 * ‖Dm x i‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hD x hxB) (norm_nonneg _))
      nlinarith only [hb, norm_nonneg (fderiv ℝ P (m x) (Dm x i)), norm_nonneg (Dm x i)]
    have hsplit := mul_le_mul_of_nonneg_left (hsNormSq_le_twice_difference (Dm x) (Dw x))
      (by norm_num : (0 : ℝ) ≤ 4)
    exact hproj.trans (hsplit.trans_eq (by ring))
  have hInt := setIntegral_mono_on (hpW.integrable_hsNormSq.mono_set hsub)
    (((herror.mono_set hsub).const_mul 8).add
      ((hw.integrable_hsNormSq.mono_set hsub).const_mul 8)) measurableSet_ball hpoint
  have herrorSub : (∫ x in T, hsNormSq (Dm x - Dw x)) ≤
      ∫ x in B, hsNormSq (Dm x - Dw x) :=
    setIntegral_mono_set herror (Filter.Eventually.of_forall fun _ => hsNormSq_nonneg _)
      (Filter.Eventually.of_forall fun x hx => hsub hx)
  have hgradInt : (∫ x in T, hsNormSq (Dw x)) ≤
      L * (volume : Measure (Domain n)).real T := by
    calc
      _ ≤ ∫ _x in T, L := setIntegral_mono_on (hw.integrable_hsNormSq.mono_set hsub)
        (integrableOn_const measure_ball_ne_top) measurableSet_ball
        (fun x hx => hgrad x (Metric.ball_subset_ball hθquarter hx))
      _ = _ := by rw [setIntegral_const, smul_eq_mul, mul_comm]
  change (∫ x in T, hsNormSq (DP x)) ≤
    ∫ x in T, 8 * hsNormSq (Dm x - Dw x) + 8 * hsNormSq (Dw x) at hInt
  rw [integral_add ((herror.mono_set hsub).const_mul 8)
      ((hw.integrable_hsNormSq.mono_set hsub).const_mul 8),
    integral_const_mul, integral_const_mul] at hInt
  exact hInt.trans (add_le_add (mul_le_mul_of_nonneg_left herrorSub (by norm_num))
    ((mul_le_mul_of_nonneg_left hgradInt (by norm_num)).trans_eq (by ring)))

end HarmonicMaps
end
