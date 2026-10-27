module

public import HarmonicMaps.Analysis.PoissonRotationCovariance
public import HarmonicMaps.Analysis.SmoothSkewRotation
public import HarmonicMaps.Analysis.PoissonClosedBallCompletion

/-!
# Angular derivatives of the canonical Poisson integral

Differentiating an actual orthogonal exponential flow transfers its generator
to the smooth boundary data. The resulting canonical integral supplies the
boundary limit of the actual angular derivative along every interior approach.
-/

public section

open MeasureTheory Set Filter
open scoped ContDiff ENNReal Topology

namespace HarmonicMaps

private theorem poisson_rotationData_hasDerivAt {n q : ℕ}
    (R : PositiveRadius) (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (m : Domain n → Ambient q) (hm : ContDiffOn ℝ ∞ m U)
    (A : Domain n →L[ℝ] Domain n)
    (T : ℝ → Domain n ≃ₗᵢ[ℝ] Domain n)
    (hT0 : T 0 = LinearIsometryEquiv.refl ℝ (Domain n))
    (hT : ContDiff ℝ ∞ (fun p : ℝ × Domain n => T p.1 p.2))
    (hTd : ∀ y : Domain n, HasDerivAt (fun t : ℝ => T t y) (A y) 0)
    (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) R.val) :
    HasDerivAt (fun t : ℝ =>
      ((R.val ^ 2 - ‖x‖ ^ 2) /
        ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) •
        (∫ y : Domain n, (‖x - y‖ ^ n)⁻¹ • m (T t y)
          ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
            (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere)))
      (((R.val ^ 2 - ‖x‖ ^ 2) /
        ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) •
        (∫ y : Domain n, (‖x - y‖ ^ n)⁻¹ • fderiv ℝ m y (A y)
          ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
            (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere))) 0 := by
  let β : Metric.sphere (0 : Domain n) 1 → Domain n := fun θ => R.val • θ.val
  let μ : Measure (Metric.sphere (0 : Domain n) 1) :=
    ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere
  let c : ℝ := (R.val ^ 2 - ‖x‖ ^ 2) /
    ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)
  let J : ℝ × Domain n → Ambient q := fun p =>
    (c * (‖x - p.2‖ ^ n)⁻¹) • m (T p.1 p.2)
  let D : Set (ℝ × Domain n) := {p | p.2 ≠ x ∧ T p.1 p.2 ∈ U}
  have hD : IsOpen D :=
    (isOpen_ne_fun continuous_snd continuous_const).inter (hU.preimage hT.continuous)
  have hβ : Continuous β :=
    (continuous_const : Continuous (fun _ : Metric.sphere (0 : Domain n) 1 => R.val)).smul
      continuous_subtype_val
  have hβsphere (θ : Metric.sphere (0 : Domain n) 1) :
      β θ ∈ Metric.sphere (0 : Domain n) R.val := by
    rw [Metric.mem_sphere, dist_zero_right]
    change ‖R.val • θ.val‖ = R.val
    rw [norm_smul, Real.norm_of_nonneg R.property.le]
    have hθ : ‖θ.val‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
    rw [hθ, mul_one]
  have hPairs : ∀ t ∈ (univ : Set ℝ), ∀ θ : Metric.sphere (0 : Domain n) 1,
      (t, β θ) ∈ D := by
    intro t _ θ
    refine ⟨?_, hclosed (Metric.sphere_subset_closedBall ?_)⟩
    · intro heq
      change β θ = x at heq
      have hxnorm : ‖x‖ < R.val := by
        simpa only [Metric.mem_ball, dist_zero_right] using hx
      have hbnorm : ‖β θ‖ = R.val := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hβsphere θ
      rw [heq] at hbnorm
      exact (lt_irrefl R.val) (hbnorm ▸ hxnorm)
    · rw [Metric.mem_sphere, dist_zero_right, (T t).norm_map]
      simpa only [Metric.mem_sphere, dist_zero_right] using hβsphere θ
  have hJ : ContDiffOn ℝ ∞ J D := by
    have hk : ContDiffOn ℝ ∞ (fun p : ℝ × Domain n => (‖x - p.2‖ ^ n)⁻¹) D := by
      apply ((contDiffOn_const.sub contDiffOn_snd).norm ℝ
        (fun p hp => sub_ne_zero.mpr hp.1.symm)).pow n |>.inv
      intro p hp
      exact pow_ne_zero n (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hp.1.symm))
    exact (contDiffOn_const.mul hk).smul
      (hm.comp hT.contDiffOn (fun p hp => hp.2))
  letI : IsFiniteMeasure μ :=
    (volume : Measure (Domain n)).toSphere.smul_finite ENNReal.ofReal_ne_top
  have hIntegral := compactParametricIntegral_hasFDerivAt μ β hβ univ isOpen_univ
    D hD hPairs J hJ 0 (mem_univ 0)
  let J₁ : ℝ × Domain n → ℝ →L[ℝ] Ambient q := fun p =>
    (fderiv ℝ J p).comp (ContinuousLinearMap.inl ℝ ℝ (Domain n))
  have hJ₁ : ContDiffOn ℝ ∞ J₁ D :=
    (hJ.fderiv_of_isOpen hD (by simp)).clm_comp contDiffOn_const
  have hJ₁continuous : Continuous (fun θ : Metric.sphere (0 : Domain n) 1 => J₁ (0, β θ)) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    exact (hJ₁.continuousOn.continuousAt (hD.mem_nhds (hPairs 0 (mem_univ _) θ))).comp
      (f := fun θ : Metric.sphere (0 : Domain n) 1 => ((0 : ℝ), β θ))
      (continuous_const.prodMk hβ).continuousAt
  have hJ₁int : Integrable (fun θ : Metric.sphere (0 : Domain n) 1 => J₁ (0, β θ)) μ :=
    hJ₁continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hColumn (θ : Metric.sphere (0 : Domain n) 1) :
      J₁ (0, β θ) 1 = (c * (‖x - β θ‖ ^ n)⁻¹) • fderiv ℝ m (β θ) (A (β θ)) := by
    have hyU : β θ ∈ U := hclosed (Metric.sphere_subset_closedBall (hβsphere θ))
    have hmAt : DifferentiableAt ℝ m (β θ) :=
      (hm.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by simp)
    have ht0 : T 0 (β θ) = β θ := by rw [hT0]; rfl
    have hmAt0 : DifferentiableAt ℝ m (T 0 (β θ)) := by rw [ht0]; exact hmAt
    have hData := hmAt0.hasFDerivAt.comp_hasDerivAt 0 (hTd (β θ))
    rw [ht0] at hData
    have hSlice : HasFDerivAt (fun t : ℝ => J (t, β θ)) (J₁ (0, β θ)) 0 := by
      exact ((hJ.contDiffAt (hD.mem_nhds (hPairs 0 (mem_univ _) θ))).differentiableAt
        (by simp)).hasFDerivAt.comp (f := fun t : ℝ => (t, β θ)) (0 : ℝ)
          (hasFDerivAt_prodMk_left (𝕜 := ℝ) (0 : ℝ) (β θ))
    have hTime := hData.const_smul (c * (‖x - β θ‖ ^ n)⁻¹)
    have hTime' := hTime.congr_of_eventuallyEq
      (Eventually.of_forall (fun t : ℝ => (rfl : J (t, β θ) =
        ((c * (‖x - β θ‖ ^ n)⁻¹) • (m ∘ fun s : ℝ => T s (β θ))) t)))
    exact hSlice.hasDerivAt.unique hTime'
  have hDerivative : HasDerivAt (fun t : ℝ => ∫ θ, J (t, β θ) ∂μ)
      (∫ θ, (c * (‖x - β θ‖ ^ n)⁻¹) • fderiv ℝ m (β θ) (A (β θ)) ∂μ) 0 := by
    have h := hIntegral.hasDerivAt
    change HasDerivAt _ ((∫ θ, J₁ (0, β θ) ∂μ) 1) 0 at h
    rw [ContinuousLinearMap.integral_apply hJ₁int] at h
    exact h.congr_deriv (integral_congr_ae (Eventually.of_forall hColumn))
  have hβclosed : Topology.IsClosedEmbedding β :=
    (Homeomorph.smulOfNeZero R.val R.property.ne').isClosedEmbedding.comp
      Metric.isClosed_sphere.isClosedEmbedding_subtypeVal
  have hLeft : (fun t : ℝ => c • (∫ y : Domain n,
      (‖x - y‖ ^ n)⁻¹ • m (T t y) ∂Measure.map β μ)) =
      (fun t : ℝ => ∫ θ, J (t, β θ) ∂μ) := by
    funext t
    rw [hβclosed.integral_map, ← integral_smul]
    apply integral_congr_ae
    filter_upwards with θ
    exact smul_smul c ((‖x - β θ‖ ^ n)⁻¹) (m (T t (β θ)))
  have hRight : c • (∫ y : Domain n, (‖x - y‖ ^ n)⁻¹ • fderiv ℝ m y (A y)
      ∂Measure.map β μ) = ∫ θ,
        (c * (‖x - β θ‖ ^ n)⁻¹) • fderiv ℝ m (β θ) (A (β θ)) ∂μ := by
    rw [hβclosed.integral_map, ← integral_smul]
    apply integral_congr_ae
    filter_upwards with θ
    exact smul_smul c ((‖x - β θ‖ ^ n)⁻¹) _
  change HasDerivAt _ (c • (∫ y : Domain n, (‖x - y‖ ^ n)⁻¹ • fderiv ℝ m y (A y)
    ∂Measure.map β μ)) 0
  rw [hLeft, hRight]
  exact hDerivative

/-- The actual skew-rotation derivative is the canonical integral of the
actual boundary derivative and converges to that derivative at every sphere
point along all interior approaches. -/
theorem poisson_scaledPolar_angularDerivative {n q : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (m : Domain n → Ambient q) (hm : ContDiffOn ℝ ∞ m U)
    (A : Domain n →L[ℝ] Domain n) (hA : star A = -A) :
    let v : Domain n → Ambient q := fun z =>
      ((R.val ^ 2 - ‖z‖ ^ 2) /
        ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) •
        (∫ y : Domain n, (‖z - y‖ ^ n)⁻¹ • m y
          ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
            (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere))
    let g : Domain n → Ambient q := fun y => fderiv ℝ m y (A y)
    ContDiffOn ℝ ∞ g U ∧
    (∀ x ∈ Metric.ball (0 : Domain n) R.val,
      fderiv ℝ v x (A x) =
        ((R.val ^ 2 - ‖x‖ ^ 2) /
          ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) •
          (∫ y : Domain n, (‖x - y‖ ^ n)⁻¹ • g y
            ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
              (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere))) ∧
    ∀ b ∈ Metric.sphere (0 : Domain n) R.val,
      Tendsto (fun x : Domain n => fderiv ℝ v x (A x))
        (nhdsWithin b (Metric.ball (0 : Domain n) R.val)) (nhds (g b)) := by
  let v : Domain n → Ambient q := fun z =>
    ((R.val ^ 2 - ‖z‖ ^ 2) /
      ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) •
      (∫ y : Domain n, (‖z - y‖ ^ n)⁻¹ • m y
        ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
          (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere))
  let g : Domain n → Ambient q := fun y => fderiv ℝ m y (A y)
  have hg : ContDiffOn ℝ ∞ g U :=
    (hm.fderiv_of_isOpen hU (by simp)).clm_apply A.contDiff.contDiffOn
  obtain ⟨T, _, hT0, hT, hTd⟩ := smoothSkewRotation_exists A hA
  have hInterior (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) R.val) :
      fderiv ℝ v x (A x) =
        ((R.val ^ 2 - ‖x‖ ^ 2) /
          ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) •
          (∫ y : Domain n, (‖x - y‖ ^ n)⁻¹ • g y
            ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
              (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere)) := by
    have hv : DifferentiableAt ℝ v x :=
      ((poisson_scaledPolar_integral_smooth_harmonic hn R U hU hclosed m hm).1.contDiffAt
        (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp)
    have ht0 : T 0 x = x := by rw [hT0]; rfl
    have hv0 : DifferentiableAt ℝ v (T 0 x) := by rw [ht0]; exact hv
    have hLeft := hv0.hasFDerivAt.comp_hasDerivAt 0 (hTd x)
    rw [ht0] at hLeft
    have hCov : (fun t : ℝ => v (T t x)) =
        (fun t : ℝ => ((R.val ^ 2 - ‖x‖ ^ 2) /
          ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) •
          (∫ y : Domain n, (‖x - y‖ ^ n)⁻¹ • m (T t y)
            ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
              (ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere))) := by
      funext t
      exact poisson_scaledPolar_rotation_covariance R (T t) m x
    change HasDerivAt (fun t : ℝ => v (T t x)) (fderiv ℝ v x (A x)) 0 at hLeft
    rw [hCov] at hLeft
    exact hLeft.unique (poisson_rotationData_hasDerivAt R U hU hclosed m hm A T hT0 hT hTd x hx)
  refine ⟨hg, hInterior, ?_⟩
  intro b hb
  have hlimit := poisson_scaledPolar_boundary_tendsto hn R U hU hclosed g hg b hb
  apply hlimit.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (hInterior x hx).symm

end HarmonicMaps
end
