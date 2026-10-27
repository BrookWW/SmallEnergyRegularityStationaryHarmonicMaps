module

public import HarmonicMaps.Analysis.PoissonIntegralSmooth
public import HarmonicMaps.Analysis.DirichletClosedBallUniqueness
public import HarmonicMaps.Analysis.PoissonMeasureInvariance
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Unit mass of the literal Poisson kernel at every interior point

Orthogonal invariance makes the constant-data integral radial. On each strict
smaller closed ball its actual sphere data are constant, so harmonic candidate
uniqueness and the outer-radius center normalization determine its value.
-/

public section

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace HarmonicMaps

private theorem scaledPolar_scalar_integrable {n : ℕ} (R : PositiveRadius)
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
  have hScalar := L.integrable_comp hVec
  simpa only [map_smul, hLc, smul_eq_mul, mul_one] using hScalar

private theorem scaledPolar_constant_formula {n q : ℕ} (R : PositiveRadius)
    (c : Ambient q) :
    EqOn (fun x : Domain n =>
      ((R.val ^ 2 - ‖x‖ ^ 2) /
        ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) •
        (∫ y : Domain n, (‖x - y‖ ^ n)⁻¹ • c
          ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
            (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere)))
      (fun x : Domain n =>
        (((R.val ^ 2 - ‖x‖ ^ 2) /
          ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) *
          (∫ y : Domain n, (‖x - y‖ ^ n)⁻¹
            ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
              (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere))) • c)
      (Metric.ball (0 : Domain n) R.val) := by
  intro x hx
  dsimp only
  let L : ℝ →L[ℝ] Ambient q := (ContinuousLinearMap.id ℝ ℝ).smulRight c
  have hInt := scaledPolar_scalar_integrable R x hx
  have hFormula := L.integral_comp_comm hInt
  change (∫ y : Domain n, (‖x - y‖ ^ n)⁻¹ • c ∂_) =
    (∫ y : Domain n, (‖x - y‖ ^ n)⁻¹ ∂_) • c at hFormula
  rw [hFormula, smul_smul]

private theorem scaledPolar_scalar_integral_rotationInvariant {n : ℕ}
    (R : PositiveRadius) (T : Domain n ≃ₗᵢ[ℝ] Domain n) (x : Domain n) :
    (∫ y : Domain n, (‖T x - y‖ ^ n)⁻¹
      ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
        (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere)) =
    (∫ y : Domain n, (‖x - y‖ ^ n)⁻¹
      ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
        (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere)) := by
  let μ : Measure (Domain n) :=
    Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
      (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere)
  have hT : MeasurePreserving T μ μ :=
    ⟨T.continuous.measurable, poisson_scaledPolar_rotationInvariant R T⟩
  have hTransport := hT.integral_comp T.toHomeomorph.measurableEmbedding
    (fun y : Domain n => (‖T x - y‖ ^ n)⁻¹)
  calc
    _ = ∫ y : Domain n, (‖T x - T y‖ ^ n)⁻¹ ∂μ := hTransport.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      rw [← T.map_sub, T.norm_map]

private theorem scaledPolar_constant_radial {n q : ℕ} (R : PositiveRadius)
    (c : Ambient q) (x y : Domain n)
    (hx : x ∈ Metric.ball (0 : Domain n) R.val)
    (hy : y ∈ Metric.ball (0 : Domain n) R.val) (hxy : ‖x‖ = ‖y‖) :
    ((R.val ^ 2 - ‖x‖ ^ 2) /
      ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) •
      (∫ z : Domain n, (‖x - z‖ ^ n)⁻¹ • c
        ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
          (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere)) =
    ((R.val ^ 2 - ‖y‖ ^ 2) /
      ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) •
      (∫ z : Domain n, (‖y - z‖ ^ n)⁻¹ • c
        ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
          (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere)) := by
  have hFormula := scaledPolar_constant_formula (n := n) R c
  have hFx := hFormula hx
  have hFy := hFormula hy
  dsimp only at hFx hFy
  rw [hFx, hFy]
  let T : Domain n ≃ₗᵢ[ℝ] Domain n := (ℝ ∙ (x - y))ᗮ.reflection
  have hTx : T x = y := Submodule.reflection_sub hxy
  have hIntegral := scaledPolar_scalar_integral_rotationInvariant R T x
  rw [hTx] at hIntegral
  rw [hxy, hIntegral]

/-- The literal normalized Poisson kernel has mass one at every point of the
open ball for the exact canonical scaled-polar sphere measure. -/
theorem poisson_scaledPolar_kernel_mass {n : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (x : Domain n)
    (hx : x ∈ Metric.ball (0 : Domain n) R.val) :
    ((R.val ^ 2 - ‖x‖ ^ 2) /
      ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) *
      (∫ y : Domain n, (‖x - y‖ ^ n)⁻¹
        ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
          (ENNReal.ofReal (R.val ^ (n - 1)) •
            (volume : Measure (Domain n)).toSphere)) = 1 := by
  let c : Ambient 1 := EuclideanSpace.single 0 1
  let μ : Measure (Domain n) :=
    Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
      (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere)
  let F : Domain n → Ambient 1 := fun z =>
    ((R.val ^ 2 - ‖z‖ ^ 2) /
      ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) •
      (∫ y : Domain n, (‖z - y‖ ^ n)⁻¹ • c ∂μ)
  have hFormula := scaledPolar_constant_formula (n := n) R c
  have hSmoothHarmonic := poisson_scaledPolar_integral_smooth_harmonic hn R univ isOpen_univ
    (subset_univ _) (fun _ : Domain n => c) contDiffOn_const
  have hSmooth : ContDiffOn ℝ ∞ F (Metric.ball (0 : Domain n) R.val) := hSmoothHarmonic.1
  have hHarmonic : ∀ z ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian F z = 0 :=
    hSmoothHarmonic.2
  have hRadial (z w : Domain n) (hz : z ∈ Metric.ball (0 : Domain n) R.val)
      (hw : w ∈ Metric.ball (0 : Domain n) R.val) (hzw : ‖z‖ = ‖w‖) : F z = F w :=
    scaledPolar_constant_radial R c z w hz hw hzw
  have hxNorm : ‖x‖ < R.val := by
    simpa only [Metric.mem_ball, dist_zero_right] using hx
  let r : ℝ := (‖x‖ + R.val) / 2
  have hr : 0 < r := by
    dsimp only [r]
    linarith only [norm_nonneg x, R.property]
  have hrR : r < R.val := by
    dsimp only [r]
    linarith only [hxNorm]
  have hxSmall : x ∈ Metric.closedBall (0 : Domain n) r := by
    rw [Metric.mem_closedBall, dist_zero_right]
    dsimp only [r]
    linarith only [hxNorm]
  have h0Small : (0 : Domain n) ∈ Metric.closedBall (0 : Domain n) r :=
    Metric.mem_closedBall_self hr.le
  have hClosed : Metric.closedBall (0 : Domain n) r ⊆ Metric.ball (0 : Domain n) R.val :=
    Metric.closedBall_subset_ball hrR
  let i : Fin n := ⟨0, by omega⟩
  let p : Domain n := r • EuclideanSpace.single i 1
  have hp : p ∈ Metric.sphere (0 : Domain n) r := by
    simp only [p, Metric.mem_sphere, dist_zero_right, norm_smul,
      Real.norm_of_nonneg hr.le, PiLp.norm_single, norm_one, mul_one]
  have hpNorm : ‖p‖ = r := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hp
  have hBoundary (z : Domain n) (hz : z ∈ Metric.sphere (0 : Domain n) r) : F z = F p := by
    have hzNorm : ‖z‖ = r := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hz
    exact hRadial z p (hClosed (Metric.sphere_subset_closedBall hz))
      (hClosed (Metric.sphere_subset_closedBall hp)) (hzNorm.trans hpNorm.symm)
  have hUnique := dirichlet_harmonic_unique_closedBall hn ⟨r, hr⟩
    (Metric.ball (0 : Domain n) R.val) Metric.isOpen_ball hClosed F (fun _ => F p)
    hSmooth contDiffOn_const hBoundary
    (fun z hz => hHarmonic z (hClosed (Metric.ball_subset_closedBall hz)))
    (fun _ _ => by simp only [InnerProductSpace.laplacian_const, Pi.zero_apply])
  have hAtZero : F 0 = c := by
    simpa only [F, μ, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] using
      poisson_constant_at_center hn R c
  have hAtX : F x = c := (hUnique hxSmall).trans ((hUnique h0Small).symm.trans hAtZero)
  have hMassVector := (hFormula hx).symm.trans hAtX
  let L : Ambient 1 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 1 => ℝ) 0
  have hLc : L c = 1 := by
    simp only [L, c, PiLp.proj_apply, EuclideanSpace.single, PiLp.single_apply, ite_true]
  have hMass := congrArg L hMassVector
  simpa only [map_smul, hLc, smul_eq_mul, mul_one] using hMass

end HarmonicMaps

end
