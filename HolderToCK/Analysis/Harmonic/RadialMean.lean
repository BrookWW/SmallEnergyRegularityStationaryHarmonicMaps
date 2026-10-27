module

public import HolderToCK.Analysis.Harmonic.SphereMean
public import HarmonicMaps.Analysis.SobolevMollificationGradient

/-! # Radial integration of spherical means

A continuous function with the spherical mean property has the same mean
under every continuous radial weight on a sampling ball. The explicit fixed
mollifier is radial, so smooth harmonic maps are preserved exactly by its
interior convolution.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ContDiff ENNReal

namespace HolderToCK

noncomputable section

theorem radial_kernel_setIntegral_eq_of_sphereMean {n q : ℕ} (hn : 0 < n)
    (a : Domain n) (R : PositiveRadius) (f : Domain n → Ambient q)
    (hf : ContinuousOn f (Metric.closedBall a R.val))
    (κ : ℝ → ℝ) (hκ : Continuous κ)
    (hmean : ∀ r ∈ Ioo (0 : ℝ) R.val,
      (∫ θ : Metric.sphere (0 : Domain n) 1, f (a + r • θ.val)
        ∂(volume : Measure (Domain n)).toSphere) =
      (volume : Measure (Domain n)).toSphere.real univ • f a) :
    (∫ z in Metric.ball a R.val, κ ‖z - a‖ • f z) =
      (∫ z in Metric.ball a R.val, κ ‖z - a‖) • f a := by
  let B := Metric.ball a R.val
  let μ := (volume : Measure (Domain n)).toSphere
  have hK : Continuous (fun z : Domain n => κ ‖z - a‖) :=
    hκ.comp (continuous_id.sub continuous_const).norm
  have hKfi : IntegrableOn (fun z => κ ‖z - a‖ • f z) B :=
    ((hK.continuousOn.smul hf).integrableOn_compact
      (isCompact_closedBall a R.val)).mono_set Metric.ball_subset_closedBall
  have hKi : IntegrableOn (fun z : Domain n => κ ‖z - a‖) B :=
    (hK.continuousOn.integrableOn_compact (isCompact_closedBall a R.val)).mono_set
      Metric.ball_subset_closedBall
  have hnorm (r : ℝ) (hr : 0 < r) (θ : Metric.sphere (0 : Domain n) 1) :
      ‖a + r • θ.val - a‖ = r := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le]
    have hθ : ‖θ.val‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
    rw [hθ, mul_one]
  ext j
  let L : Ambient q →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin q => ℝ) j
  have hLfi : IntegrableOn (fun z => L (κ ‖z - a‖ • f z)) B :=
    L.integrable_comp hKfi
  have hLconst : IntegrableOn (fun z : Domain n => κ ‖z - a‖ * L (f a)) B :=
    hKi.mul_const _
  have hangular (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R.val) :
      (∫ θ : Metric.sphere (0 : Domain n) 1,
        L (κ ‖a + r • θ.val - a‖ • f (a + r • θ.val)) ∂μ) =
      ∫ θ : Metric.sphere (0 : Domain n) 1,
        κ ‖a + r • θ.val - a‖ * L (f a) ∂μ := by
    have hmap : Continuous (fun θ : Metric.sphere (0 : Domain n) 1 =>
        a + r • θ.val) := continuous_const.add
      ((continuous_const : Continuous (fun _ : Metric.sphere (0 : Domain n) 1 => r)).smul
        continuous_subtype_val)
    have hmem (θ : Metric.sphere (0 : Domain n) 1) :
        a + r • θ.val ∈ Metric.closedBall a R.val := by
      rw [Metric.mem_closedBall, dist_eq_norm, hnorm r hr.1 θ]
      exact hr.2.le
    have hcont : Continuous (fun θ : Metric.sphere (0 : Domain n) 1 =>
        f (a + r • θ.val)) := hf.comp_continuous hmap hmem
    have hInt : Integrable (fun θ : Metric.sphere (0 : Domain n) 1 =>
        f (a + r • θ.val)) μ :=
      hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    simp_rw [hnorm r hr.1, map_smul, smul_eq_mul]
    rw [integral_const_mul, L.integral_comp_comm hInt, hmean r hr,
      map_smul, smul_eq_mul, integral_const, smul_eq_mul]
    ring
  have hscalar : (∫ z in B, L (κ ‖z - a‖ • f z)) =
      (∫ z in B, κ ‖z - a‖) * L (f a) := by
    calc
      _ = ∫ r in Ioo (0 : ℝ) R.val, r ^ (n - 1) *
          ∫ θ : Metric.sphere (0 : Domain n) 1,
            L (κ ‖a + r • θ.val - a‖ • f (a + r • θ.val)) ∂μ :=
        integral_ball_eq_polar hn hLfi
      _ = ∫ r in Ioo (0 : ℝ) R.val, r ^ (n - 1) *
          ∫ θ : Metric.sphere (0 : Domain n) 1,
            κ ‖a + r • θ.val - a‖ * L (f a) ∂μ := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro r hr
        dsimp only
        rw [hangular r hr]
      _ = ∫ z in B, κ ‖z - a‖ * L (f a) :=
        (integral_ball_eq_polar hn hLconst).symm
      _ = _ := integral_mul_const _ _
  have hcomm := L.integral_comp_comm hKfi
  calc
    (∫ z in Metric.ball a R.val, κ ‖z - a‖ • f z) j =
        L (∫ z in B, κ ‖z - a‖ • f z) := rfl
    _ = ∫ z in B, L (κ ‖z - a‖ • f z) := hcomm.symm
    _ = (∫ z in B, κ ‖z - a‖) * L (f a) := hscalar
    _ = ((∫ z in Metric.ball a R.val, κ ‖z - a‖) • f a) j := rfl


theorem radial_kernel_convolution_eq_of_sphereMean {n q : ℕ} (hn : 0 < n)
    (a : Domain n) (R : PositiveRadius) (f : Domain n → Ambient q)
    (hf : ContinuousOn f (Metric.closedBall a R.val))
    (κ : ℝ → ℝ) (hκ : Continuous κ) (hκzero : ∀ t, R.val ≤ t → κ t = 0)
    (hmean : ∀ r ∈ Ioo (0 : ℝ) R.val,
      (∫ θ : Metric.sphere (0 : Domain n) 1, f (a + r • θ.val)
        ∂(volume : Measure (Domain n)).toSphere) =
      (volume : Measure (Domain n)).toSphere.real univ • f a) :
    (∫ z, κ ‖z‖ • f (a - z)) = (∫ z : Domain n, κ ‖z‖) • f a := by
  have hzero (z : Domain n) (hz : z ∉ Metric.ball a R.val) : κ ‖z - a‖ = 0 :=
    hκzero _ (by simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hz)
  have hvec : (∫ z in Metric.ball a R.val, κ ‖z - a‖ • f z) =
      ∫ z, κ ‖z - a‖ • f z :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by rw [hzero z hz, zero_smul])
  have hscalar : (∫ z in Metric.ball a R.val, κ ‖z - a‖) =
      ∫ z, κ ‖z - a‖ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  calc
    _ = ∫ z, κ ‖a - z‖ • f z := by
      rw [← integral_sub_left_eq_self (fun z => κ ‖z‖ • f (a - z)) volume a]
      simp only [sub_sub_cancel]
    _ = ∫ z, κ ‖z - a‖ • f z := by simp only [norm_sub_rev]
    _ = (∫ z, κ ‖z - a‖) • f a := by
      rw [← hvec, ← hscalar]
      exact radial_kernel_setIntegral_eq_of_sphereMean hn a R f hf κ hκ hmean
    _ = _ := congrArg (fun c : ℝ => c • f a)
      (integral_sub_right_eq_self (fun z : Domain n => κ ‖z‖) a)

end
end HolderToCK
end
