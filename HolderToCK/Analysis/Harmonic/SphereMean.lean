module

public import HarmonicMaps.Analysis.HarmonicBallMeanValue

/-! # Spherical mean of a smooth harmonic map

The canonical angular measure is the polar measure induced by Euclidean
volume. Poisson uniqueness gives the mean at the center, and translation
gives the mean at an arbitrary Euclidean center.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ENNReal ContDiff

namespace HolderToCK

private theorem harmonic_center_sphere_meanValue {n q : ℕ} (hn : 2 ≤ n)
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

theorem harmonic_sphere_meanValue {n q : ℕ} (hn : 2 ≤ n)
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
  have hmean := harmonic_center_sphere_meanValue hn R V hV hclosedV
    (fun z => f (a + z)) hg hgh
  simpa only [add_zero] using hmean


theorem polar_angular_mass_pos {n : ℕ} (hn : 0 < n) :
    0 < (volume : Measure (Domain n)).toSphere.real univ := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hball : 0 < (volume : Measure (Domain n)).real
      (Metric.ball (0 : Domain n) 1) := by
    apply ENNReal.toReal_pos
    · exact Metric.isOpen_ball.measure_ne_zero volume
        (Metric.nonempty_ball.mpr (by norm_num))
    · exact measure_ball_ne_top
  rw [(volume : Measure (Domain n)).toSphere_real_apply_univ]
  simpa only [finrank_euclideanSpace, Fintype.card_fin] using mul_pos hnpos hball


theorem harmonic_sphere_integral_eq {n q : ℕ} (hn : 2 ≤ n)
    (a : Domain n) (R : PositiveRadius) (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall a R.val ⊆ U)
    (f : Domain n → Ambient q) (hf : ContDiffOn ℝ ∞ f U)
    (hharm : ∀ x ∈ Metric.ball a R.val, Laplacian.laplacian f x = 0) :
    (∫ θ : Metric.sphere (0 : Domain n) 1, f (a + R.val • θ.val)
      ∂(volume : Measure (Domain n)).toSphere) =
      (volume : Measure (Domain n)).toSphere.real univ • f a := by
  have h := harmonic_sphere_meanValue hn a R U hU hclosed f hf hharm
  have hmass := (polar_angular_mass_pos (by omega : 0 < n)).ne'
  have heq := congrArg (fun v : Ambient q =>
    (volume : Measure (Domain n)).toSphere.real univ • v) h.symm
  simpa only [smul_smul, mul_inv_cancel₀ hmass, one_smul] using heq

end HolderToCK
end
