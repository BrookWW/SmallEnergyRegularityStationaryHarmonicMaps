module

public import HarmonicMaps.Analysis.CompactParametricIntegral
public import HarmonicMaps.Analysis.PoissonScalarKernel

/-!
# Interior smoothness and harmonicity of the literal ball Poisson integral

The integral uses the radius-scaled canonical polar measure. Joint smoothness
away from the diagonal and compact boundary parameters justify differentiation
under this measure. No boundary convergence or surface-area identification is
asserted here.
-/

public section

open MeasureTheory Set Filter
open scoped ContDiff ENNReal Topology

namespace HarmonicMaps

private theorem poissonIntegral_scaledSphere_mem {n : ℕ} (R : PositiveRadius)
    (θ : Metric.sphere (0 : Domain n) 1) :
    R.val • θ.val ∈ Metric.sphere (0 : Domain n) R.val := by
  have hθ : ‖θ.val‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
  rw [Metric.mem_sphere, dist_zero_right, norm_smul,
    Real.norm_of_nonneg R.property.le, hθ, mul_one]

private theorem poissonIntegral_pairs {n : ℕ} (R : PositiveRadius)
    (U : Set (Domain n)) (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) R.val)
    (θ : Metric.sphere (0 : Domain n) 1) :
    (x, R.val • θ.val) ∈ {p : Domain n × Domain n | p.2 ∈ U ∧ p.1 ≠ p.2} := by
  have hSphere := poissonIntegral_scaledSphere_mem R θ
  refine ⟨hclosed (Metric.sphere_subset_closedBall hSphere), ?_⟩
  change x ≠ R.val • θ.val
  intro heq
  have H : ‖x‖ < R.val := by
    simpa only [Metric.mem_ball, dist_zero_right] using hx
  have hNorm : ‖R.val • θ.val‖ = R.val := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hSphere
  rw [heq, hNorm] at H
  exact (lt_irrefl R.val) H

private theorem poissonIntegral_jointSmooth {n q : ℕ} (R : PositiveRadius)
    (U : Set (Domain n)) (m : Domain n → Ambient q) (hm : ContDiffOn ℝ ∞ m U) :
    ContDiffOn ℝ ∞ (fun p : Domain n × Domain n =>
      (((R.val ^ 2 - ‖p.1‖ ^ 2) /
        ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) *
        (‖p.1 - p.2‖ ^ n)⁻¹) • m p.2)
      {p | p.2 ∈ U ∧ p.1 ≠ p.2} := by
  let D : Set (Domain n × Domain n) := {p | p.2 ∈ U ∧ p.1 ≠ p.2}
  have hc : ContDiffOn ℝ ∞ (fun p : Domain n × Domain n =>
      (R.val ^ 2 - ‖p.1‖ ^ 2) /
        ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) D :=
    (contDiffOn_const.sub (contDiffOn_fst.norm_sq ℝ)).div_const _
  have hInv : ContDiffOn ℝ ∞
      (fun p : Domain n × Domain n => (‖p.1 - p.2‖ ^ n)⁻¹) D := by
    apply ((contDiffOn_fst.sub contDiffOn_snd).norm ℝ
      (fun p hp => sub_ne_zero.mpr hp.2)).pow n |>.inv
    intro p hp
    exact pow_ne_zero n (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hp.2))
  have hData : ContDiffOn ℝ ∞ (fun p : Domain n × Domain n => m p.2) D :=
    hm.comp contDiffOn_snd (fun p hp => hp.1)
  exact (hc.mul hInv).smul hData

private theorem poissonIntegral_vectorKernel_laplacian_zero {n q : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (y : Domain n) (hy : y ∈ Metric.sphere (0 : Domain n) R.val)
    (d : Ambient q) (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) R.val) :
    Laplacian.laplacian (fun z : Domain n =>
      (((R.val ^ 2 - ‖z‖ ^ 2) /
        ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) *
        (‖z - y‖ ^ n)⁻¹) • d) x = 0 := by
  have hxy : x - y ≠ 0 := by
    apply sub_ne_zero.mpr
    intro heq
    have H : ‖x‖ < R.val := by
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    have hNorm : ‖y‖ = R.val := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hy
    rw [heq, hNorm] at H
    exact (lt_irrefl R.val) H
  let K : Domain n → ℝ := fun z =>
    ((R.val ^ 2 - ‖z‖ ^ 2) /
      ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) *
      (‖z - y‖ ^ n)⁻¹
  let L : ℝ →L[ℝ] Ambient q := (ContinuousLinearMap.id ℝ ℝ).smulRight d
  have hc : ContDiffAt ℝ 2 (fun z : Domain n =>
      (R.val ^ 2 - ‖z‖ ^ 2) /
        ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) x :=
    (contDiffAt_const.sub (contDiffAt_id.norm_sq ℝ)).div_const _
  have hInv : ContDiffAt ℝ 2 (fun z : Domain n => (‖z - y‖ ^ n)⁻¹) x :=
    (((contDiffAt_id.sub contDiffAt_const).norm ℝ hxy).pow n).inv
      (pow_ne_zero n (norm_ne_zero_iff.mpr hxy))
  have hK : ContDiffAt ℝ 2 K x := hc.mul hInv
  change Laplacian.laplacian (L ∘ K) x = 0
  rw [hK.laplacian_CLM_comp_left]
  change L (Laplacian.laplacian K x) = 0
  rw [poisson_scalarKernel_laplacian_zero hn R y hy x hx]
  exact L.map_zero

/-- The literal scaled-polar Poisson formula is smooth and has zero native
Laplacian in the open ball for smooth data near the closed ball. -/
theorem poisson_scaledPolar_integral_smooth_harmonic {n q : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (m : Domain n → Ambient q) (hm : ContDiffOn ℝ ∞ m U) :
    ContDiffOn ℝ ∞ (fun x : Domain n =>
      ((R.val ^ 2 - ‖x‖ ^ 2) /
        ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) •
        (∫ y : Domain n, (‖x - y‖ ^ n)⁻¹ • m y
          ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
            (ENNReal.ofReal (R.val ^ (n - 1)) •
              (volume : Measure (Domain n)).toSphere)))
      (Metric.ball (0 : Domain n) R.val) ∧
    ∀ x ∈ Metric.ball (0 : Domain n) R.val,
      Laplacian.laplacian (fun z : Domain n =>
        ((R.val ^ 2 - ‖z‖ ^ 2) /
          ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) •
          (∫ y : Domain n, (‖z - y‖ ^ n)⁻¹ • m y
            ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
              (ENNReal.ofReal (R.val ^ (n - 1)) •
                (volume : Measure (Domain n)).toSphere))) x = 0 := by
  let β : Metric.sphere (0 : Domain n) 1 → Domain n := fun θ => R.val • θ.val
  let μ : Measure (Metric.sphere (0 : Domain n) 1) :=
    ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere
  let c : Domain n → ℝ := fun z => (R.val ^ 2 - ‖z‖ ^ 2) /
    ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)
  let F : Domain n → Ambient q := fun z => c z •
    (∫ y : Domain n, (‖z - y‖ ^ n)⁻¹ • m y ∂Measure.map β μ)
  let J : Domain n × Domain n → Ambient q := fun p =>
    (c p.1 * (‖p.1 - p.2‖ ^ n)⁻¹) • m p.2
  have hβ : Continuous β :=
    (continuous_const : Continuous (fun _ : Metric.sphere (0 : Domain n) 1 => R.val)).smul
      continuous_subtype_val
  have hEq : EqOn F (fun z => ∫ θ, J (z, β θ) ∂μ)
      (Metric.ball (0 : Domain n) R.val) := by
    intro z hz
    have hInt := poisson_scaledPolar_integrable R U hU hclosed m hm z hz
    change c z • (∫ y : Domain n, (‖z - y‖ ^ n)⁻¹ • m y ∂Measure.map β μ) = _
    rw [integral_map hβ.measurable.aemeasurable hInt.aestronglyMeasurable]
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards with θ
    exact smul_smul (c z) ((‖z - β θ‖ ^ n)⁻¹) (m (β θ))
  let D : Set (Domain n × Domain n) := {p | p.2 ∈ U ∧ p.1 ≠ p.2}
  have hD : IsOpen D :=
    (hU.preimage continuous_snd).inter (isOpen_ne_fun continuous_fst continuous_snd)
  have hPairs : ∀ x ∈ Metric.ball (0 : Domain n) R.val,
      ∀ θ : Metric.sphere (0 : Domain n) 1, (x, β θ) ∈ D :=
    poissonIntegral_pairs R U hclosed
  have hJ : ContDiffOn ℝ ∞ J D := poissonIntegral_jointSmooth R U m hm
  letI : IsFiniteMeasure μ :=
    (volume : Measure (Domain n)).toSphere.smul_finite ENNReal.ofReal_ne_top
  have hSmooth := compactParametricIntegral_contDiffOn μ β hβ
    (Metric.ball (0 : Domain n) R.val) Metric.isOpen_ball D hD hPairs J hJ
  change ContDiffOn ℝ ∞ F (Metric.ball (0 : Domain n) R.val) ∧
    ∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian F x = 0
  refine ⟨hSmooth.congr hEq, ?_⟩
  intro x hx
  have hEv : F =ᶠ[𝓝 x] (fun z => ∫ θ, J (z, β θ) ∂μ) := by
    filter_upwards [Metric.isOpen_ball.eventually_mem hx] with z hz
    exact hEq hz
  rw [(InnerProductSpace.laplacian_congr_nhds hEv).eq_of_nhds]
  rw [compactParametricIntegral_laplacian μ β hβ
    (Metric.ball (0 : Domain n) R.val) Metric.isOpen_ball D hD hPairs J hJ x hx]
  have hZero (θ : Metric.sphere (0 : Domain n) 1) :
      Laplacian.laplacian (fun z : Domain n => J (z, β θ)) x = 0 :=
    poissonIntegral_vectorKernel_laplacian_zero hn R (β θ)
      (poissonIntegral_scaledSphere_mem R θ) (m (β θ)) x hx
  calc
    (∫ θ, Laplacian.laplacian (fun z : Domain n => J (z, β θ)) x ∂μ) = ∫ _ : Metric.sphere (0 : Domain n) 1, (0 : Ambient q) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hZero)
    _ = 0 := integral_zero _ _

end HarmonicMaps

end
