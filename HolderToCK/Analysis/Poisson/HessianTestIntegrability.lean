module

public import HolderToCK.Analysis.Poisson.FundamentalIntegrability
public import HolderToCK.Analysis.Poisson.PuncturedIntegrationByParts
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Integrable Hessian pairings for tests vanishing at the origin -/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology

namespace HolderToCK

theorem compactTest_sub_origin_bound {n : ℕ} {φ : Domain n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |φ x - φ 0| ≤ M * ‖x‖ := by
  have hD := hφ.continuous_fderiv one_ne_zero
  obtain ⟨M, hM⟩ := ((hcφ.fderiv ℝ).isCompact_range hD).exists_bound_of_continuousOn
    continuous_id.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ (mem_range_self (0 : Domain n)))
  refine ⟨M, hM0, fun x => ?_⟩
  simpa only [Real.norm_eq_abs, sub_zero] using
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun y (_ : y ∈ (univ : Set (Domain n))) => hφ.differentiable one_ne_zero y)
      (fun y _ => hM _ (mem_range_self y)) convex_univ (mem_univ 0) (mem_univ x)

theorem hessianKernelExpression_testZero_integrable {n : ℕ} (hn : 0 < n)
    (i j : Fin n) {φ : Domain n → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hcφ : HasCompactSupport φ) (hφ0 : φ 0 = 0) :
    Integrable (fun x => hessianKernelExpression i j x * φ x) volume := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨M, hM0, hM⟩ := compactTest_sub_origin_bound hφ hcφ
  have hmeas : Measurable (hessianKernelExpression i j) := by
    exact measurable_const.mul
      ((measurable_const.mul (measurable_norm.pow_const _)).sub
        (((measurable_const.mul
          (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).measurable).mul
          (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).measurable).mul
          (measurable_norm.pow_const _)))
  have hloc : LocallyIntegrable (fun x => hessianKernelExpression i j x * φ x) volume := by
    apply locallyIntegrable_of_norm_le_rpow
      (C := (((n : ℝ) + 1) * (euclideanSphereArea n)⁻¹) * M)
      (α := (n : ℝ) - 1)
      (by simp only [finrank_euclideanSpace, Fintype.card_fin]; omega)
    · simp only [finrank_euclideanSpace, Fintype.card_fin]
      linarith only []
    · filter_upwards [(volume : Measure (Domain n)).ae_ne 0] with x hx
      have hφx : |φ x| ≤ M * ‖x‖ := by simpa only [hφ0, sub_zero] using hM x
      have hC0 : 0 ≤ ((n : ℝ) + 1) * (euclideanSphereArea n)⁻¹ := by
        exact mul_nonneg (by positivity) (inv_nonneg.mpr (euclideanSphereArea_pos hn).le)
      rw [Real.norm_eq_abs, abs_mul]
      calc
        _ ≤ (((n : ℝ) + 1) * (euclideanSphereArea n)⁻¹ * ‖x‖ ^ (-(n : ℝ))) *
            (M * ‖x‖) :=
          mul_le_mul (hessianKernelExpression_bound hn i j x hx) hφx
            (abs_nonneg _) (mul_nonneg hC0 (Real.rpow_nonneg (norm_nonneg _) _))
        _ = _ := by
          have hp : ‖x‖ ^ (-(n : ℝ)) * ‖x‖ = ‖x‖ ^ (-((n : ℝ) - 1)) := by
            rw [← Real.rpow_add_one (norm_ne_zero_iff.mpr hx)]
            congr 1
            ring
          calc
            _ = (((n : ℝ) + 1) * (euclideanSphereArea n)⁻¹) * M *
                (‖x‖ ^ (-(n : ℝ)) * ‖x‖) := by ring
            _ = _ := by rw [hp]
    · exact (hmeas.mul hφ.continuous.measurable).aestronglyMeasurable
  exact (integrableOn_iff_integrable_of_support_subset
    (subset_tsupport (fun x => hessianKernelExpression i j x * φ x))).mp
      (hloc.integrableOn_isCompact
        (by simpa only [Pi.mul_def] using
          (hcφ.mul_left : HasCompactSupport (hessianKernelExpression i j * φ)).isCompact))

theorem hessianKernelExpression_testIntegrableOn_exterior {n : ℕ}
    (i j : Fin n) {φ : Domain n → ℝ} (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x => hessianKernelExpression i j x * φ x)
      (Metric.ball (0 : Domain n) r)ᶜ volume := by
  have hc : ContinuousOn (fun x => hessianKernelExpression i j x * φ x)
      (tsupport φ \ Metric.ball (0 : Domain n) r) := by
    intro x hx
    have hx0 : x ≠ 0 := by
      intro hx0
      exact hx.2 (by rw [hx0]; exact Metric.mem_ball_self hr)
    exact ((hessianKernelExpression_continuousAt i j x hx0).mul hφ.continuousAt).continuousWithinAt
  apply (hc.integrableOn_compact (hcφ.isCompact.diff Metric.isOpen_ball)).of_forall_sdiff_eq_zero
    measurableSet_ball.compl
  intro x hx
  have hxφ : x ∉ tsupport φ := fun h => hx.2 ⟨h, hx.1⟩
  rw [image_eq_zero_of_notMem_tsupport hxφ, mul_zero]

theorem integrable_tendsto_exteriorBall_integral {n : ℕ} (hn : 0 < n)
    {f : Domain n → ℝ} (hf : Integrable f volume) :
    Tendsto (fun r : ℝ => ∫ x in (Metric.ball (0 : Domain n) r)ᶜ, f x)
      (𝓝 0) (𝓝 (∫ x, f x)) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have ht := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝 (0 : ℝ)) (f := f) (fun x => ‖f x‖)
    (Eventually.of_forall (fun r : ℝ => hf.aestronglyMeasurable.indicator measurableSet_ball.compl))
    (Eventually.of_forall (fun r : ℝ => Eventually.of_forall (fun x : Domain n =>
      norm_indicator_le_norm_self (s := (Metric.ball (0 : Domain n) r)ᶜ) (f := f) (a := x))))
    hf.norm ?_
  · simpa only [integral_indicator measurableSet_ball.compl] using ht
  · filter_upwards [(volume : Measure (Domain n)).ae_ne 0] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [Iio_mem_nhds (norm_pos_iff.mpr hx)] with r hr
    rw [indicator_of_mem (show x ∈ (Metric.ball (0 : Domain n) r)ᶜ from
      (by simpa only [mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hr.le))]

theorem normalizedRadialColumn_differentiableAt {n : ℕ} (i : Fin n)
    (x : Domain n) (hx : x ≠ 0) :
    DifferentiableAt ℝ (fun z : Domain n =>
      (euclideanSphereArea n)⁻¹ * ‖z‖ ^ (-(n : ℝ)) * z i) x := by
  exact ((norm_rpow_hasFDerivAt_of_ne_zero _ x hx).differentiableAt.const_mul _).mul
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i).differentiableAt

theorem normalizedRadialColumn_testZero_integrationByParts {n : ℕ} (hn : 2 ≤ n)
    (i j : Fin n) {φ : Domain n → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hcφ : HasCompactSupport φ) (hφ0 : φ 0 = 0) :
    (∫ x, ((euclideanSphereArea n)⁻¹ * ‖x‖ ^ (-(n : ℝ)) * x i) *
      fderiv ℝ φ x (EuclideanSpace.single j 1)) =
      -∫ x, hessianKernelExpression i j x * φ x := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega : 0 < n)
  have hv : EuclideanSpace.single j (1 : ℝ) ≠ (0 : Domain n) :=
    (PiLp.single_eq_zero_iff 2 j).not.mpr one_ne_zero
  have hK := hessianKernelExpression_testZero_integrable (by omega : 0 < n) i j hφ hcφ hφ0
  have hD : Integrable (fun x : Domain n =>
      fderiv ℝ (fun z : Domain n =>
        (euclideanSphereArea n)⁻¹ * ‖z‖ ^ (-(n : ℝ)) * z i) x
          (EuclideanSpace.single j 1) * φ x) volume := by
    apply hK.congr
    filter_upwards [(volume : Measure (Domain n)).ae_ne 0] with x hx
    rw [normalizedRadialColumn_mixedColumn x hx i j, ← hessianKernelExpression_eq]
  have hid := punctured_hasFDerivAt_integrationByParts
    (μ := (volume : Measure (Domain n)))
    (by simp only [finrank_euclideanSpace, Fintype.card_fin]; omega) hv hD
    (normalizedRadialColumn_testIntegrable (by omega : 0 < n) i
      ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      (hcφ.fderiv_apply ℝ _))
    (normalizedRadialColumn_testIntegrable (by omega : 0 < n) i hφ.continuous hcφ)
    (fun x hx => (normalizedRadialColumn_differentiableAt i x hx).hasFDerivAt)
    (fun x => (hφ.differentiable one_ne_zero x).hasFDerivAt)
  rw [hid]
  congr 1
  apply integral_congr_ae
  filter_upwards [(volume : Measure (Domain n)).ae_ne 0] with x hx
  rw [normalizedRadialColumn_mixedColumn x hx i j, ← hessianKernelExpression_eq]

end HolderToCK
end
