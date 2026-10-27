module

public import HarmonicMaps.Analysis.PoissonKernelMass
public import HarmonicMaps.Analysis.PoissonKernelIntegrability
public import HarmonicMaps.Analysis.SphereSurfaceMeasure

/-!
# Boundary control of the Poisson solution

The nonnegative scalar kernel has exact mass one. Its vector integral stays
within any closed norm ball containing the boundary data.
-/

public section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace HarmonicMaps

/-- The canonical Poisson integral obeys every boundary norm bound. -/
theorem poisson_scaledPolar_norm_sub_le_boundary {n q : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (m : Domain n → Ambient q) (hm : ContDiffOn ℝ ∞ m U)
    (c : Ambient q) (M : ℝ)
    (hboundary : ∀ y ∈ Metric.sphere (0 : Domain n) R.val, ‖m y - c‖ ≤ M)
    (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) R.val) :
    ‖((R.val ^ 2 - ‖x‖ ^ 2) /
        ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) •
      (∫ y : Domain n, (‖x - y‖ ^ n)⁻¹ • m y
        ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
          (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere)) - c‖ ≤ M := by
  let μ : Measure (Domain n) :=
    Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
      (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere)
  let k : Domain n → ℝ := fun y => (‖x - y‖ ^ n)⁻¹
  let a : ℝ := (R.val ^ 2 - ‖x‖ ^ 2) /
    ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)
  have hMass : a * (∫ y : Domain n, k y ∂μ) = 1 :=
    poisson_scaledPolar_kernel_mass hn R x hx
  have hxNorm : ‖x‖ < R.val := by
    simpa only [Metric.mem_ball, dist_zero_right] using hx
  have hnPos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hVolume : 0 < (volume : Measure (Domain n)).real (Metric.ball 0 1) := by
    apply ENNReal.toReal_pos
    · exact Metric.isOpen_ball.measure_ne_zero volume (Metric.nonempty_ball.mpr (by norm_num))
    · exact measure_ball_ne_top
  have ha : 0 < a := by
    have hNum : 0 < R.val ^ 2 - ‖x‖ ^ 2 := by
      have hprod := mul_pos (sub_pos.mpr hxNorm)
        (add_pos_of_nonneg_of_pos (norm_nonneg x) R.property)
      nlinarith only [hprod]
    exact div_pos hNum (mul_pos (mul_pos hnPos hVolume) R.property)
  have hk (y : Domain n) : 0 ≤ k y :=
    inv_nonneg.mpr (pow_nonneg (norm_nonneg _) _)
  have hK : Integrable k μ := by
    by_contra hnot
    have hzero : (∫ y : Domain n, k y ∂μ) = 0 := integral_undef hnot
    rw [hzero, mul_zero] at hMass
    norm_num at hMass
  have hmInt := poisson_scaledPolar_integrable R U hU hclosed m hm x hx
  have hcInt := poisson_scaledPolar_integrable R U hU hclosed
    (fun _ : Domain n => c) contDiffOn_const x hx
  have hdiffInt := poisson_scaledPolar_integrable R U hU hclosed
    (fun y => m y - c) (hm.sub contDiffOn_const) x hx
  have hMeasure : μ =
      (Measure.euclideanHausdorffMeasure (n - 1) : Measure (Domain n)).restrict
        (Metric.sphere (0 : Domain n) R.val) :=
    poisson_scaledPolar_eq_euclideanSphereArea hn R
  have hSphere : ∀ᵐ y ∂μ, y ∈ Metric.sphere (0 : Domain n) R.val := by
    rw [hMeasure]
    exact ae_restrict_mem Metric.isClosed_sphere.measurableSet
  have hConstIntegral : a • (∫ y : Domain n, k y • c ∂μ) = c := by
    rw [integral_smul_const, smul_smul, hMass, one_smul]
  have hDiffIntegral :
      (∫ y : Domain n, k y • m y ∂μ) - (∫ y : Domain n, k y • c ∂μ) =
      ∫ y : Domain n, k y • (m y - c) ∂μ := by
    rw [← integral_sub hmInt hcInt]
    simp only [smul_sub]
    rfl
  have hVector : a • (∫ y : Domain n, k y • m y ∂μ) - c =
      a • (∫ y : Domain n, k y • (m y - c) ∂μ) := by
    calc
      _ = a • (∫ y : Domain n, k y • m y ∂μ) -
          a • (∫ y : Domain n, k y • c ∂μ) := by rw [hConstIntegral]
      _ = a • ((∫ y : Domain n, k y • m y ∂μ) -
          (∫ y : Domain n, k y • c ∂μ)) := (smul_sub _ _ _).symm
      _ = _ := by rw [hDiffIntegral]
  have hNormAE : ∀ᵐ y ∂μ, ‖k y • (m y - c)‖ ≤ M * k y := by
    filter_upwards [hSphere] with y hy
    rw [norm_smul, Real.norm_of_nonneg (hk y)]
    calc
      _ ≤ k y * M := mul_le_mul_of_nonneg_left (hboundary y hy) (hk y)
      _ = M * k y := mul_comm _ _
  have hNormInt : ‖∫ y : Domain n, k y • (m y - c) ∂μ‖ ≤
      M * (∫ y : Domain n, k y ∂μ) := by
    calc
      _ ≤ ∫ y : Domain n, ‖k y • (m y - c)‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ y : Domain n, M * k y ∂μ :=
        integral_mono_ae hdiffInt.norm (hK.const_mul M) hNormAE
      _ = _ := by rw [integral_const_mul]
  rw [hVector, norm_smul, Real.norm_of_nonneg ha.le]
  calc
    a * ‖∫ y : Domain n, k y • (m y - c) ∂μ‖ ≤
        a * (M * ∫ y : Domain n, k y ∂μ) :=
      mul_le_mul_of_nonneg_left hNormInt ha.le
    _ = M * (a * ∫ y : Domain n, k y ∂μ) := by ring
    _ = M := by rw [hMass, mul_one]

end HarmonicMaps
end
