module

public import HarmonicMaps.Analysis.PoissonDirichletAssembly
public import HarmonicMaps.Analysis.PoissonKernelIntegrability
public import HarmonicMaps.Analysis.BallPolarIntegralNormalization
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Mean value of a smooth Euclidean harmonic map

Poisson uniqueness gives the spherical mean at the center of a ball. Polar
integration then gives the ball mean for every Euclidean center and radius.
-/

public section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace HarmonicMaps

private theorem harmonic_center_sphereMean {n q : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (f : Domain n → Ambient q) (hf : ContDiffOn ℝ ∞ f U)
    (hharm : ∀ x ∈ Metric.ball (0 : Domain n) R.val,
      Laplacian.laplacian f x = 0) :
    f 0 = ((volume : Measure (Domain n)).toSphere.real univ)⁻¹ •
      ∫ θ : Metric.sphere (0 : Domain n) 1, f (R.val • θ.val)
        ∂(volume : Measure (Domain n)).toSphere := by
  obtain ⟨v, hv, hb, w, hwv, hws, hwh, hformula, hwW, hdiff, huniq, hvuniq⟩ :=
    poisson_scaledPolar_dirichlet_assembly hn R U hU hclosed f hf
  have hfw : f 0 = w 0 :=
    huniq f (hf.mono hclosed) (fun _ _ => rfl) hharm
      (Metric.mem_closedBall_self R.property.le)
  have hcenter := hformula 0 (Metric.mem_ball_self R.property)
  have hangular := poisson_scaledPolar_formula_eq_angular hn R U hU hclosed f hf
    0 (Metric.mem_ball_self R.property)
  have hnorm (θ : Metric.sphere (0 : Domain n) 1) :
      ‖(0 : Domain n) - R.val • θ.val‖ = R.val := by
    rw [zero_sub, norm_neg, norm_smul, Real.norm_of_nonneg R.property.le]
    have ht : ‖θ.val‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
    rw [ht, mul_one]
  have hcoeff :
      (R.val ^ 2 * R.val ^ (n - 2) /
        ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1))) *
        (R.val ^ n)⁻¹ =
      ((volume : Measure (Domain n)).toSphere.real univ)⁻¹ := by
    have hnv : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hball : (volume : Measure (Domain n)).real (Metric.ball 0 1) ≠ 0 := by
      apply ne_of_gt
      apply ENNReal.toReal_pos
      · exact Metric.isOpen_ball.measure_ne_zero volume
          (Metric.nonempty_ball.mpr (by norm_num))
      · exact measure_ball_ne_top
    have hexp : n = (n - 2) + 2 := by omega
    have hpow : R.val ^ n = R.val ^ (n - 2) * R.val ^ 2 := by
      conv_lhs => rw [hexp, pow_add]
    rw [(volume : Measure (Domain n)).toSphere_real_apply_univ]
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    rw [hpow]
    field_simp [R.property.ne', hnv, hball]
  calc
    f 0 = w 0 := hfw
    _ = ((R.val ^ 2 - ‖(0 : Domain n)‖ ^ 2) /
        ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) •
        (∫ y : Domain n, (‖(0 : Domain n) - y‖ ^ n)⁻¹ • f y
          ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
            (ENNReal.ofReal (R.val ^ (n - 1)) •
              (volume : Measure (Domain n)).toSphere)) := hcenter
    _ = (((R.val ^ 2 - ‖(0 : Domain n)‖ ^ 2) * R.val ^ (n - 2)) /
        ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1))) •
        (∫ θ : Metric.sphere (0 : Domain n) 1,
          (‖(0 : Domain n) - R.val • θ.val‖ ^ n)⁻¹ • f (R.val • θ.val)
            ∂(volume : Measure (Domain n)).toSphere) := hangular
    _ = _ := by
      simp_rw [hnorm]
      simp only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero,
        integral_smul, smul_smul]
      exact congrArg (fun c : ℝ => c •
        (∫ θ : Metric.sphere (0 : Domain n) 1, f (R.val • θ.val)
          ∂(volume : Measure (Domain n)).toSphere)) hcoeff

private theorem laplacian_comp_add_left {n q : ℕ}
    (a z : Domain n) (f : Domain n → Ambient q) :
    Laplacian.laplacian (fun y => f (a + y)) z =
      Laplacian.laplacian f (a + z) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
      (fun y => f (a + y)) (EuclideanSpace.basisFun (Fin n) ℝ),
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
      f (EuclideanSpace.basisFun (Fin n) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedFDeriv_comp_add_left]

private theorem harmonic_sphereMean {n q : ℕ} (hn : 2 ≤ n)
    (a : Domain n) (R : PositiveRadius) (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall a R.val ⊆ U)
    (f : Domain n → Ambient q) (hf : ContDiffOn ℝ ∞ f U)
    (hharm : ∀ x ∈ Metric.ball a R.val, Laplacian.laplacian f x = 0) :
    f a = ((volume : Measure (Domain n)).toSphere.real univ)⁻¹ •
      ∫ θ : Metric.sphere (0 : Domain n) 1, f (a + R.val • θ.val)
        ∂(volume : Measure (Domain n)).toSphere := by
  let V : Set (Domain n) := (fun z => a + z) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_const.add continuous_id)
  have hclosedV : Metric.closedBall (0 : Domain n) R.val ⊆ V := by
    intro z hz
    apply hclosed
    simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left,
      sub_zero] using hz
  have hg : ContDiffOn ℝ ∞ (fun z : Domain n => f (a + z)) V := by
    apply hf.comp (contDiff_const.add contDiff_id).contDiffOn
    intro z hz
    exact hz
  have hgh : ∀ z ∈ Metric.ball (0 : Domain n) R.val,
      Laplacian.laplacian (fun y => f (a + y)) z = 0 := by
    intro z hz
    rw [laplacian_comp_add_left]
    apply hharm
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
      sub_zero] using hz
  have hmean := harmonic_center_sphereMean hn R V hV hclosedV
    (fun z => f (a + z)) hg hgh
  simpa only [add_zero] using hmean

/-- A smooth harmonic map equals its integral average on every ball whose
closure lies in its smoothness neighborhood. -/
theorem harmonic_ball_meanValue {n q : ℕ} (hn : 2 ≤ n)
    (a : Domain n) (R : PositiveRadius) (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall a R.val ⊆ U)
    (f : Domain n → Ambient q) (hf : ContDiffOn ℝ ∞ f U)
    (hharm : ∀ x ∈ Metric.ball a R.val, Laplacian.laplacian f x = 0) :
    f a = ((volume : Measure (Domain n)).real (Metric.ball a R.val))⁻¹ •
      ∫ x in Metric.ball a R.val, f x := by
  let B : Set (Domain n) := Metric.ball a R.val
  let μ : Measure (Metric.sphere (0 : Domain n) 1) :=
    (volume : Measure (Domain n)).toSphere
  let mass : ℝ := μ.real univ
  have hmasspos : 0 < mass := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hball : 0 < (volume : Measure (Domain n)).real
        (Metric.ball (0 : Domain n) 1) := by
      apply ENNReal.toReal_pos
      · exact Metric.isOpen_ball.measure_ne_zero volume
          (Metric.nonempty_ball.mpr (by norm_num))
      · exact measure_ball_ne_top
    dsimp only [mass, μ]
    rw [(volume : Measure (Domain n)).toSphere_real_apply_univ]
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using mul_pos hnpos hball
  have hmassne : mass ≠ 0 := ne_of_gt hmasspos
  have hB : IntegrableOn f B volume :=
    ((hf.continuousOn.mono hclosed).integrableOn_compact
      (isCompact_closedBall a R.val)).mono_set Metric.ball_subset_closedBall
  have hsphere (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R.val) :
      (∫ θ : Metric.sphere (0 : Domain n) 1, f (a + r • θ.val) ∂μ) =
        mass • f a := by
    have hrR : r < R.val := hr.2
    have hsmall : Metric.closedBall a r ⊆ U :=
      (Metric.closedBall_subset_ball hrR).trans
        (Metric.ball_subset_closedBall.trans hclosed)
    have hsmallHarm : ∀ x ∈ Metric.ball a r,
        Laplacian.laplacian f x = 0 := by
      intro x hx
      exact hharm x (Metric.ball_subset_ball hrR.le hx)
    have hmean := harmonic_sphereMean hn a ⟨r, hr.1⟩ U hU hsmall f hf
      hsmallHarm
    change f a = mass⁻¹ •
      (∫ θ : Metric.sphere (0 : Domain n) 1, f (a + r • θ.val) ∂μ) at hmean
    have h := congrArg (fun v : Ambient q => mass • v) hmean.symm
    simpa only [smul_smul, mul_inv_cancel₀ hmassne, one_smul] using h
  have hIntegral : (∫ x in B, f x) = (volume : Measure (Domain n)).real B • f a := by
    ext j
    let L : Ambient q →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin q => ℝ) j
    have hL : IntegrableOn (fun x => L (f x)) B volume := L.integrable_comp hB
    letI : IsFiniteMeasure (volume.restrict B) :=
      isFiniteMeasure_restrict.mpr measure_ball_ne_top
    have hC : IntegrableOn (fun _ : Domain n => L (f a)) B volume :=
      integrable_const _
    have hAngular (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R.val) :
        (∫ θ : Metric.sphere (0 : Domain n) 1, L (f (a + r • θ.val)) ∂μ) =
          ∫ θ : Metric.sphere (0 : Domain n) 1, L (f a) ∂μ := by
      have hmap : Continuous
          (fun θ : Metric.sphere (0 : Domain n) 1 => a + r • θ.val) :=
        continuous_const.add
          ((continuous_const : Continuous
            (fun _ : Metric.sphere (0 : Domain n) 1 => r)).smul continuous_subtype_val)
      have hmem (θ : Metric.sphere (0 : Domain n) 1) :
          a + r • θ.val ∈ U := by
        apply hclosed
        rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left,
          norm_smul, Real.norm_of_nonneg hr.1.le]
        have hθ : ‖θ.val‖ = 1 := by
          simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
        rw [hθ, mul_one]
        exact hr.2.le
      have hcont : Continuous
          (fun θ : Metric.sphere (0 : Domain n) 1 => f (a + r • θ.val)) := by
        apply continuous_iff_continuousAt.mpr
        intro θ
        exact (hf.contDiffAt (hU.mem_nhds (hmem θ))).continuousAt.comp
          (f := fun θ : Metric.sphere (0 : Domain n) 1 => a + r • θ.val)
          hmap.continuousAt
      have hInt : Integrable
          (fun θ : Metric.sphere (0 : Domain n) 1 => f (a + r • θ.val)) μ :=
        hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      calc
        _ = L (∫ θ : Metric.sphere (0 : Domain n) 1,
            f (a + r • θ.val) ∂μ) := L.integral_comp_comm hInt
        _ = L (mass • f a) := by rw [hsphere r hr]
        _ = mass * L (f a) := by simp
        _ = _ := by rw [integral_const, smul_eq_mul]
    have hpolar := integral_ball_eq_polar (by omega : 0 < n)
      (f := fun x => L (f x)) (a := a) (R := R.val) hL
    have hconstPolar := integral_ball_eq_polar (by omega : 0 < n)
      (f := fun _ : Domain n => L (f a)) (a := a) (R := R.val) hC
    have hscalar : (∫ x in B, L (f x)) =
        (volume : Measure (Domain n)).real B * L (f a) := by
      calc
        (∫ x in B, L (f x)) =
            ∫ r in Ioo (0 : ℝ) R.val, r ^ (n - 1) *
              ∫ θ : Metric.sphere (0 : Domain n) 1,
                L (f (a + r • θ.val)) ∂μ := hpolar
        _ = ∫ r in Ioo (0 : ℝ) R.val, r ^ (n - 1) *
              ∫ θ : Metric.sphere (0 : Domain n) 1, L (f a) ∂μ := by
            apply setIntegral_congr_fun measurableSet_Ioo
            intro r hr
            change r ^ (n - 1) *
              (∫ θ : Metric.sphere (0 : Domain n) 1,
                L (f (a + r • θ.val)) ∂μ) =
              r ^ (n - 1) *
              (∫ θ : Metric.sphere (0 : Domain n) 1, L (f a) ∂μ)
            rw [hAngular r hr]
        _ = ∫ x in B, L (f a) := hconstPolar.symm
        _ = (volume : Measure (Domain n)).real B * L (f a) := by
            rw [setIntegral_const, smul_eq_mul]
    have hcomm : (∫ x in B, L (f x)) = L (∫ x in B, f x) :=
      L.integral_comp_comm hB
    calc
      (∫ x in B, f x) j = L (∫ x in B, f x) := by simp [L]
      _ = ∫ x in B, L (f x) := hcomm.symm
      _ = (volume : Measure (Domain n)).real B * L (f a) := hscalar
      _ = ((volume : Measure (Domain n)).real B • f a) j := by simp [L]
  have hvolpos : 0 < (volume : Measure (Domain n)).real B :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume a R.property).ne'
      measure_ball_ne_top
  have h := congrArg
    (fun v : Ambient q => ((volume : Measure (Domain n)).real B)⁻¹ • v)
    hIntegral
  simpa only [smul_smul, inv_mul_cancel₀ hvolpos.ne', one_smul] using h.symm

end HarmonicMaps
end
