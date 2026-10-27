module

public import HarmonicMaps.Analysis.PoissonKernelMass
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Boundary limits of the canonical Poisson integral

The unit-mass identity and actual compact-sphere data control the integral near
a boundary point. Away from that point the reciprocal kernel has a uniform
bound, while its scalar coefficient tends to zero.
-/

public section

open MeasureTheory Set Filter
open scoped ContDiff ENNReal

namespace HarmonicMaps

private theorem boundary_scalar_integrable {n : ℕ} (R : PositiveRadius)
    (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) R.val) :
    Integrable (fun y : Domain n => (‖x - y‖ ^ n)⁻¹)
      (Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
        (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere)) := by
  let c : Ambient 1 := EuclideanSpace.single 0 1
  let L : Ambient 1 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 1 => ℝ) 0
  have hLc : L c = 1 := by
    simp only [L, c, PiLp.proj_apply, EuclideanSpace.single, PiLp.single_apply, ite_true]
  have hVec := poisson_scaledPolar_integrable R univ isOpen_univ (subset_univ _)
    (fun _ : Domain n => c) contDiffOn_const x hx
  simpa only [map_smul, hLc, smul_eq_mul, mul_one] using L.integrable_comp hVec

/-- The literal canonical Poisson integral approaches the prescribed sphere
value along every interior approach path. -/
theorem poisson_scaledPolar_boundary_tendsto {n q : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (m : Domain n → Ambient q) (hm : ContDiffOn ℝ ∞ m U)
    (b : Domain n) (hb : b ∈ Metric.sphere (0 : Domain n) R.val) :
    Filter.Tendsto (fun x : Domain n =>
      ((R.val ^ 2 - ‖x‖ ^ 2) /
        ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) •
        (∫ y : Domain n, (‖x - y‖ ^ n)⁻¹ • m y
          ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
            (ENNReal.ofReal (R.val ^ (n - 1)) •
              (volume : Measure (Domain n)).toSphere)))
      (nhdsWithin b (Metric.ball (0 : Domain n) R.val)) (nhds (m b)) :=
by
  classical
  let ν := ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere
  haveI : IsFiniteMeasure ν :=
    (volume : Measure (Domain n)).toSphere.smul_finite ENNReal.ofReal_ne_top
  let μ : Measure (Domain n) :=
    Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val) ν
  haveI : IsFiniteMeasure μ := ν.isFiniteMeasure_map _
  let d : ℝ := (n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val
  let a : Domain n → ℝ := fun x => (R.val ^ 2 - ‖x‖ ^ 2) / d
  let k : Domain n → Domain n → ℝ := fun x y => (‖x - y‖ ^ n)⁻¹
  let F : Domain n → Ambient q := fun x => a x • ∫ y, k x y • m y ∂μ
  change Tendsto F (nhdsWithin b (Metric.ball (0 : Domain n) R.val)) (nhds (m b))
  have hnPos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hVolume : 0 < (volume : Measure (Domain n)).real (Metric.ball 0 1) := by
    apply ENNReal.toReal_pos
    · exact Metric.isOpen_ball.measure_ne_zero volume (Metric.nonempty_ball.mpr (by norm_num))
    · exact measure_ball_ne_top
  have hd : 0 < d := mul_pos (mul_pos hnPos hVolume) R.property
  have hSphere : ∀ᵐ y ∂μ, y ∈ Metric.sphere (0 : Domain n) R.val := by
    let rad : Metric.sphere (0 : Domain n) 1 → Domain n := fun θ => R.val • θ.val
    have hRad : Continuous rad :=
      (continuous_const : Continuous
        (fun _ : Metric.sphere (0 : Domain n) 1 => R.val)).smul continuous_subtype_val
    change ∀ᵐ y ∂Measure.map rad ν, y ∈ Metric.sphere (0 : Domain n) R.val
    apply (ae_map_iff hRad.measurable.aemeasurable
      (Metric.isClosed_sphere.measurableSet)).mpr
    exact ae_of_all _ (fun θ => by
      have hθ : ‖θ.val‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
      change dist (R.val • θ.val) 0 = R.val
      rw [dist_zero_right, norm_smul, Real.norm_of_nonneg R.property.le, hθ, mul_one])
  have hbU : b ∈ U := hclosed (Metric.sphere_subset_closedBall hb)
  have hmAt : ContinuousAt m b := (hm.contDiffAt (hU.mem_nhds hbU)).continuousAt
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : Domain n) R.val).exists_bound_of_continuousOn
    ((hm.continuousOn.sub continuousOn_const).mono
      (Metric.sphere_subset_closedBall.trans hclosed))
  let M₀ := max M 0
  have hM₀ : 0 ≤ M₀ := le_max_right _ _
  have hBound (y : Domain n) (hy : y ∈ Metric.sphere (0 : Domain n) R.val) :
      ‖m y - m b‖ ≤ M₀ := (hM y hy).trans (le_max_left _ _)
  have hbNorm : ‖b‖ = R.val := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hb
  have haContinuous : Continuous a :=
    ((continuous_const.sub (continuous_norm.pow 2)).div_const d)
  have haZero : a b = 0 := by simp only [a, hbNorm, sub_self, zero_div]
  have haLimit : Tendsto a (nhdsWithin b (Metric.ball (0 : Domain n) R.val)) (nhds 0) :=
    by simpa only [haZero] using (haContinuous.tendsto b).mono_left nhdsWithin_le_nhds
  have hkInt (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) R.val) :
      Integrable (k x) μ := boundary_scalar_integrable R x hx
  have haNonneg (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) R.val) : 0 ≤ a x := by
    have hxNorm : ‖x‖ ≤ R.val := by
      exact le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hx)
    exact div_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg x) hxNorm 2)) hd.le
  have hMass (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) R.val) :
      a x * (∫ y, k x y ∂μ) = 1 := poisson_scaledPolar_kernel_mass hn R x hx
  have hError (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) R.val) :
      F x - m b = a x • ∫ y, k x y • (m y - m b) ∂μ := by
    have hmInt := poisson_scaledPolar_integrable R U hU hclosed m hm x hx
    have hcInt := poisson_scaledPolar_integrable R univ isOpen_univ (subset_univ _)
      (fun _ : Domain n => m b) contDiffOn_const x hx
    let L : ℝ →L[ℝ] Ambient q := (ContinuousLinearMap.id ℝ ℝ).smulRight (m b)
    have hConst := L.integral_comp_comm (hkInt x hx)
    change (∫ y, k x y • m b ∂μ) = (∫ y, k x y ∂μ) • m b at hConst
    have hDifference : (∫ y, k x y • (m y - m b) ∂μ) =
        (∫ y, k x y • m y ∂μ) - (∫ y, k x y ∂μ) • m b := by
      simp_rw [smul_sub]
      rw [integral_sub hmInt hcInt, hConst]
    rw [hDifference, smul_sub, smul_smul, hMass x hx, one_smul]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hHalf : 0 < ε / 2 := half_pos hε
  obtain ⟨δ, hδ, hNear⟩ := Metric.continuousAt_iff.mp hmAt (ε / 2) hHalf
  let D : ℝ := ((δ / 2) ^ n)⁻¹
  have hδHalf : 0 < δ / 2 := half_pos hδ
  have hD : 0 ≤ D := inv_nonneg.mpr (pow_nonneg hδHalf.le n)
  let C : ℝ := (M₀ * D) * μ.real univ
  have hTailLimit : Tendsto (fun x => a x * C)
      (nhdsWithin b (Metric.ball (0 : Domain n) R.val)) (nhds 0) := by
    simpa only [zero_mul] using haLimit.mul_const C
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds b hδHalf),
    (tendsto_order.mp hTailLimit).2 (ε / 2) hHalf] with x hx hxNear hxTail
  have hxDist : dist x b < δ / 2 := hxNear
  have hPointwise : ∀ᵐ y ∂μ,
      ‖k x y • (m y - m b)‖ ≤ (ε / 2) * k x y + M₀ * D := by
    filter_upwards [hSphere] with y hy
    have hk : 0 ≤ k x y := inv_nonneg.mpr (pow_nonneg (norm_nonneg _) n)
    rw [norm_smul, Real.norm_of_nonneg hk]
    by_cases hClose : dist y b < δ
    · have hSmall : ‖m y - m b‖ ≤ ε / 2 := by
        exact le_of_lt (by simpa only [dist_eq_norm] using hNear hClose)
      calc
        k x y * ‖m y - m b‖ ≤ k x y * (ε / 2) := mul_le_mul_of_nonneg_left hSmall hk
        _ ≤ (ε / 2) * k x y + M₀ * D := by
          rw [mul_comm (k x y)]
          exact le_add_of_nonneg_right (mul_nonneg hM₀ hD)
    · have hSep : δ / 2 ≤ ‖x - y‖ := by
        have hTri := dist_triangle y x b
        rw [dist_comm y x, dist_eq_norm x y] at hTri
        have hNot := le_of_not_gt hClose
        linarith only [hTri, hNot, hxDist]
      have hkBound : k x y ≤ D :=
        (inv_le_inv₀ (pow_pos (hδHalf.trans_le hSep) n) (pow_pos hδHalf n)).mpr
          (pow_le_pow_left₀ hδHalf.le hSep n)
      calc
        k x y * ‖m y - m b‖ ≤ k x y * M₀ :=
          mul_le_mul_of_nonneg_left (hBound y hy) hk
        _ ≤ D * M₀ := mul_le_mul_of_nonneg_right hkBound hM₀
        _ ≤ (ε / 2) * k x y + M₀ * D := by
          rw [mul_comm D]
          exact le_add_of_nonneg_left (mul_nonneg hHalf.le hk)
  have hgInt : Integrable (fun y => (ε / 2) * k x y + M₀ * D) μ :=
    ((hkInt x hx).const_mul (ε / 2)).add (integrable_const _)
  have hNorm := norm_integral_le_of_norm_le hgInt hPointwise
  have hIntegral : (∫ y, (ε / 2) * k x y + M₀ * D ∂μ) =
      (ε / 2) * (∫ y, k x y ∂μ) + (M₀ * D) * μ.real univ := by
    rw [integral_add ((hkInt x hx).const_mul _) (integrable_const _)]
    rw [show (fun y => (ε / 2) * k x y) = (fun y => (ε / 2) • k x y) from rfl,
      integral_smul, integral_const]
    simp only [smul_eq_mul]
    ring
  have hFinal : ‖F x - m b‖ ≤ ε / 2 + a x * C := by
    rw [hError x hx, norm_smul, Real.norm_of_nonneg (haNonneg x hx)]
    calc
      _ ≤ a x * (∫ y, (ε / 2) * k x y + M₀ * D ∂μ) :=
        mul_le_mul_of_nonneg_left hNorm (haNonneg x hx)
      _ = ε / 2 + a x * C := by
        rw [hIntegral]
        dsimp only [C]
        calc
          _ = (ε / 2) * (a x * (∫ y, k x y ∂μ)) + a x * ((M₀ * D) * μ.real univ) := by ring
          _ = _ := by rw [hMass x hx, mul_one]
  rw [dist_eq_norm]
  exact hFinal.trans_lt (by linarith only [hxTail])

end HarmonicMaps
end
