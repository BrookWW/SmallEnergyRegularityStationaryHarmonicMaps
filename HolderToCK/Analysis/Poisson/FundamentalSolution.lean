module

public import HolderToCK.Analysis.Poisson.RadialHessian
public import HolderToCK.Foundation.BallVolume
public import HarmonicMaps.Analysis.SphereSurfaceMeasure
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! # Fundamental solution and its derivatives on the punctured carrier

The sphere area is the mass of the canonical Euclidean polar sphere measure.
The fundamental solution is defined only at nonzero points. Ambient power and
logarithmic expressions are used to state its local derivatives there.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology

namespace HolderToCK

@[expose] noncomputable def euclideanSphereArea (n : ℕ) : ℝ :=
  (volume : Measure (Domain n)).toSphere.real univ

theorem euclideanSphereArea_eq (n : ℕ) :
    euclideanSphereArea n = (n : ℝ) * volume.real (Metric.ball (0 : Domain n) 1) := by
  rw [euclideanSphereArea, Measure.toSphere_real_apply_univ]
  simp only [finrank_euclideanSpace, Fintype.card_fin]

theorem euclideanSphereArea_pos {n : ℕ} (hn : 0 < n) :
    0 < euclideanSphereArea n := by
  rw [euclideanSphereArea_eq]
  exact mul_pos (Nat.cast_pos.mpr hn) (ball_volume_real_pos 0 one_pos)

theorem euclideanSphereArea_two : euclideanSphereArea 2 = 2 * Real.pi := by
  rw [euclideanSphereArea_eq, measureReal_def, EuclideanSpace.volume_ball_fin_two]
  norm_num [Real.pi_nonneg]

@[expose] noncomputable def fundamentalPowerExpression {n : ℕ} (z : Domain n) : ℝ :=
  ((2 - (n : ℝ)) * euclideanSphereArea n)⁻¹ *
    (‖z‖ ^ 2) ^ ((2 - (n : ℝ)) / 2)

@[expose] noncomputable def fundamentalLogExpression (z : Domain 2) : ℝ :=
  (2 * Real.pi)⁻¹ * Real.log ‖z‖

@[expose] noncomputable def fundamentalSolution (n : ℕ) (_hn : 2 ≤ n)
    (z : {z : Domain n // z ≠ 0}) : ℝ :=
  if n = 2 then (2 * Real.pi)⁻¹ * Real.log ‖z.val‖
  else ((2 - (n : ℝ)) * euclideanSphereArea n)⁻¹ * ‖z.val‖ ^ (2 - (n : ℝ))

@[expose] noncomputable def fundamentalHessianKernel {n : ℕ}
    (i j : Fin n) (z : {z : Domain n // z ≠ 0}) : ℝ :=
  (euclideanSphereArea n)⁻¹ *
    ((if i = j then 1 else 0) * ‖z.val‖ ^ (-(n : ℝ)) -
      (n : ℝ) * z.val i * z.val j * ‖z.val‖ ^ (-(n : ℝ) - 2))

theorem fundamentalSolution_power {n : ℕ} (hn : 3 ≤ n)
    (z : {z : Domain n // z ≠ 0}) :
    fundamentalSolution n (by omega) z = fundamentalPowerExpression z.val := by
  rw [fundamentalSolution, if_neg (by omega), fundamentalPowerExpression]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  ring

theorem fundamentalSolution_log (z : {z : Domain 2 // z ≠ 0}) :
    fundamentalSolution 2 (by omega) z = fundamentalLogExpression z.val := by
  simp only [fundamentalSolution, if_true, fundamentalLogExpression]

theorem normSq_real_rpow {E : Type*} [SeminormedAddCommGroup E] (x : E) (a : ℝ) :
    (‖x‖ ^ 2) ^ a = ‖x‖ ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  norm_num

theorem fundamentalPower_contDiffAt {n : ℕ} (x : Domain n) (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ fundamentalPowerExpression x := by
  exact contDiffAt_const.mul (by
    simpa only [sub_zero] using normSq_rpow_contDiffAt (0 : Domain n)
      ((2 - (n : ℝ)) / 2) x hx)

theorem fundamentalPower_hasFDerivAt {n : ℕ} (hn : 3 ≤ n)
    (x : Domain n) (hx : x ≠ 0) :
    HasFDerivAt fundamentalPowerExpression
      (((euclideanSphereArea n)⁻¹ * ‖x‖ ^ (-(n : ℝ))) • innerSL ℝ x) x := by
  have hd := (normSq_rpow_hasFDerivAt (0 : Domain n)
    ((2 - (n : ℝ)) / 2) x hx).const_mul
      (((2 - (n : ℝ)) * euclideanSphereArea n)⁻¹)
  simp only [sub_zero] at hd
  rw [smul_smul, normSq_real_rpow,
    show 2 * ((2 - (n : ℝ)) / 2 - 1) = -(n : ℝ) by ring] at hd
  have hnz : 2 - (n : ℝ) ≠ 0 := by
    have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith only [hn']
  have hs := (euclideanSphereArea_pos (by omega : 0 < n)).ne'
  have hc : ((2 - (n : ℝ)) * euclideanSphereArea n)⁻¹ *
      (2 * ((2 - (n : ℝ)) / 2) * ‖x‖ ^ (-(n : ℝ))) =
      (euclideanSphereArea n)⁻¹ * ‖x‖ ^ (-(n : ℝ)) := by
    field_simp
  rw [hc] at hd
  exact hd

theorem fundamentalPower_column {n : ℕ} (hn : 3 ≤ n)
    (x : Domain n) (hx : x ≠ 0) (i : Fin n) :
    fderiv ℝ fundamentalPowerExpression x (EuclideanSpace.single i 1) =
      (euclideanSphereArea n)⁻¹ * ‖x‖ ^ (-(n : ℝ)) * x i := by
  rw [(fundamentalPower_hasFDerivAt hn x hx).fderiv]
  simp only [smul_apply, innerSL_apply_apply, EuclideanSpace.inner_single_right,
    one_mul, conj_trivial, smul_eq_mul]

theorem fundamentalLog_eq_normSq (z : Domain 2) :
    fundamentalLogExpression z = (4 * Real.pi)⁻¹ * Real.log (‖z‖ ^ 2) := by
  rw [fundamentalLogExpression, Real.log_pow]
  norm_num
  ring

theorem fundamentalLog_contDiffAt (x : Domain 2) (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ fundamentalLogExpression x := by
  have heq : fundamentalLogExpression =
      (fun z : Domain 2 => (4 * Real.pi)⁻¹ * Real.log (‖z‖ ^ 2)) :=
    funext fundamentalLog_eq_normSq
  rw [heq]
  exact contDiffAt_const.mul (by
    simpa only [sub_zero] using normSq_log_contDiffAt (0 : Domain 2) x hx)

theorem fundamentalLog_hasFDerivAt (x : Domain 2) (hx : x ≠ 0) :
    HasFDerivAt fundamentalLogExpression
      (((euclideanSphereArea 2)⁻¹ * ‖x‖ ^ (-(2 : ℝ))) • innerSL ℝ x) x := by
  have hd := (normSq_log_hasFDerivAt (0 : Domain 2) x hx).const_mul ((4 * Real.pi)⁻¹)
  simp only [sub_zero, smul_smul] at hd
  have heq : fundamentalLogExpression =
      (fun z : Domain 2 => (4 * Real.pi)⁻¹ * Real.log (‖z‖ ^ 2)) :=
    funext fundamentalLog_eq_normSq
  rw [← heq] at hd
  rw [euclideanSphereArea_two]
  have hc : (4 * Real.pi)⁻¹ * (2 * (‖x‖ ^ 2)⁻¹) =
      (2 * Real.pi)⁻¹ * ‖x‖ ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg (norm_nonneg x), Real.rpow_two]
    ring
  rw [hc] at hd
  exact hd

theorem fundamentalLog_column (x : Domain 2) (hx : x ≠ 0) (i : Fin 2) :
    fderiv ℝ fundamentalLogExpression x (EuclideanSpace.single i 1) =
      (euclideanSphereArea 2)⁻¹ * ‖x‖ ^ (-(2 : ℝ)) * x i := by
  rw [(fundamentalLog_hasFDerivAt x hx).fderiv]
  simp only [smul_apply, innerSL_apply_apply, EuclideanSpace.inner_single_right,
    one_mul, conj_trivial, smul_eq_mul]

theorem normalizedRadialColumn_mixedColumn {n : ℕ} (x : Domain n) (hx : x ≠ 0)
    (i j : Fin n) :
    fderiv ℝ (fun z : Domain n =>
      (euclideanSphereArea n)⁻¹ * ‖z‖ ^ (-(n : ℝ)) * z i) x
        (EuclideanSpace.single j 1) = fundamentalHessianKernel i j ⟨x, hx⟩ := by
  have hcoord := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i).hasFDerivAt
    (x := x)
  have hscalar := ((normSq_rpow_hasFDerivAt (0 : Domain n) (-(n : ℝ) / 2) x hx).const_mul
    (euclideanSphereArea n)⁻¹).mul hcoord
  simp only [sub_zero, Pi.mul_def, PiLp.proj_apply] at hscalar
  have heq : (fun z : Domain n => (euclideanSphereArea n)⁻¹ * ‖z‖ ^ (-(n : ℝ)) * z i) =
      (fun z : Domain n => (euclideanSphereArea n)⁻¹ *
        (‖z‖ ^ 2) ^ (-(n : ℝ) / 2) * z i) := by
    funext z
    rw [normSq_real_rpow, show 2 * (-(n : ℝ) / 2) = -(n : ℝ) by ring]
  rw [heq, hscalar.fderiv]
  simp only [smul_apply, add_apply, smul_eq_mul,
    PiLp.proj_apply, EuclideanSpace.single, PiLp.single_apply,
    innerSL_apply_apply, EuclideanSpace.inner_single_right, one_mul, conj_trivial,
    fundamentalHessianKernel]
  rw [normSq_real_rpow, normSq_real_rpow,
    show 2 * (-(n : ℝ) / 2 - 1) = -(n : ℝ) - 2 by ring,
    show 2 * (-(n : ℝ) / 2) = -(n : ℝ) by ring]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    ring
  · simp only [hij, ite_false]
    ring

theorem fundamentalPower_mixedColumns {n : ℕ} (hn : 3 ≤ n)
    (x : Domain n) (hx : x ≠ 0) (i j : Fin n) :
    fderiv ℝ (fun z : Domain n => fderiv ℝ fundamentalPowerExpression z
      (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1) =
      fundamentalHessianKernel i j ⟨x, hx⟩ := by
  have heq : (fun z : Domain n => fderiv ℝ fundamentalPowerExpression z
      (EuclideanSpace.single i 1)) =ᶠ[𝓝 x]
      (fun z => (euclideanSphereArea n)⁻¹ * ‖z‖ ^ (-(n : ℝ)) * z i) := by
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hx] with z hz
    exact fundamentalPower_column hn z hz i
  rw [heq.fderiv_eq]
  exact normalizedRadialColumn_mixedColumn x hx i j

theorem fundamentalLog_mixedColumns (x : Domain 2) (hx : x ≠ 0) (i j : Fin 2) :
    fderiv ℝ (fun z : Domain 2 => fderiv ℝ fundamentalLogExpression z
      (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1) =
      fundamentalHessianKernel i j ⟨x, hx⟩ := by
  have heq : (fun z : Domain 2 => fderiv ℝ fundamentalLogExpression z
      (EuclideanSpace.single i 1)) =ᶠ[𝓝 x]
      (fun z => (euclideanSphereArea 2)⁻¹ * ‖z‖ ^ (-(2 : ℝ)) * z i) := by
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hx] with z hz
    exact fundamentalLog_column z hz i
  rw [heq.fderiv_eq]
  exact normalizedRadialColumn_mixedColumn x hx i j

theorem radialFlux_normalization {n : ℕ} (hn : 0 < n) (R : PositiveRadius) :
    (∫ θ : Metric.sphere (0 : Domain n) 1,
      ((euclideanSphereArea n)⁻¹ * ‖R.val • θ.val‖ ^ (-(n : ℝ))) *
        inner ℝ (R.val • θ.val) θ.val
      ∂(ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere)) = 1 := by
  have hθnorm (θ : Metric.sphere (0 : Domain n) 1) : ‖θ.val‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
  have heq : (fun θ : Metric.sphere (0 : Domain n) 1 =>
      ((euclideanSphereArea n)⁻¹ * ‖R.val • θ.val‖ ^ (-(n : ℝ))) *
        inner ℝ (R.val • θ.val) θ.val) =
      (fun _ => (euclideanSphereArea n)⁻¹ * R.val ^ (-(n : ℝ)) * R.val) := by
    funext θ
    rw [norm_smul, Real.norm_of_nonneg R.property.le, hθnorm, mul_one,
      real_inner_smul_left, real_inner_self_eq_norm_sq, hθnorm, one_pow, mul_one]
  rw [heq, integral_const, smul_eq_mul, measureReal_def, Measure.smul_apply,
    smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg R.property.le _)]
  change R.val ^ (n - 1) * euclideanSphereArea n *
    ((euclideanSphereArea n)⁻¹ * R.val ^ (-(n : ℝ)) * R.val) = 1
  rw [Real.rpow_neg R.property.le, Real.rpow_natCast]
  have hpow : R.val ^ n = R.val ^ (n - 1) * R.val := by
    conv_lhs => rw [← Nat.sub_add_cancel hn, pow_succ]
  rw [hpow]
  have hS := (euclideanSphereArea_pos hn).ne'
  field_simp [pow_ne_zero _ R.property.ne', R.property.ne']

theorem fundamentalPower_flux {n : ℕ} (hn : 3 ≤ n) (R : PositiveRadius) :
    (∫ θ : Metric.sphere (0 : Domain n) 1,
      fderiv ℝ fundamentalPowerExpression (R.val • θ.val) θ.val
      ∂(ENNReal.ofReal (R.val ^ (n - 1)) • (volume : Measure (Domain n)).toSphere)) = 1 := by
  have heq : (fun θ : Metric.sphere (0 : Domain n) 1 =>
      fderiv ℝ fundamentalPowerExpression (R.val • θ.val) θ.val) =
      (fun θ => ((euclideanSphereArea n)⁻¹ * ‖R.val • θ.val‖ ^ (-(n : ℝ))) *
        inner ℝ (R.val • θ.val) θ.val) := by
    funext θ
    have hθ : θ.val ≠ 0 := by
      intro hz
      simpa only [hz, Metric.mem_sphere, dist_self, zero_ne_one] using θ.property
    rw [(fundamentalPower_hasFDerivAt hn _ (smul_ne_zero R.property.ne' hθ)).fderiv]
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  rw [heq]
  exact radialFlux_normalization (by omega) R

theorem fundamentalLog_flux (R : PositiveRadius) :
    (∫ θ : Metric.sphere (0 : Domain 2) 1,
      fderiv ℝ fundamentalLogExpression (R.val • θ.val) θ.val
      ∂(ENNReal.ofReal R.val • (volume : Measure (Domain 2)).toSphere)) = 1 := by
  have heq : (fun θ : Metric.sphere (0 : Domain 2) 1 =>
      fderiv ℝ fundamentalLogExpression (R.val • θ.val) θ.val) =
      (fun θ => ((euclideanSphereArea 2)⁻¹ * ‖R.val • θ.val‖ ^ (-(2 : ℝ))) *
        inner ℝ (R.val • θ.val) θ.val) := by
    funext θ
    have hθ : θ.val ≠ 0 := by
      intro hz
      simpa only [hz, Metric.mem_sphere, dist_self, zero_ne_one] using θ.property
    rw [(fundamentalLog_hasFDerivAt _ (smul_ne_zero R.property.ne' hθ)).fderiv]
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  rw [heq]
  simpa only [Nat.reduceSub, pow_one, Nat.cast_ofNat] using
    radialFlux_normalization (n := 2) (by omega) R

end HolderToCK
end
