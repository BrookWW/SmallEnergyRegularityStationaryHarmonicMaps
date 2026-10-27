module

public import HarmonicMaps.Analysis.PoissonKernelIntegrability
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Harmonicity of the literal scalar ball kernel

The first and second derivatives are computed at actual nonsingular interior
points. The Euclidean orthonormal trace and the sphere identity give the
Laplacian cancellation for the literal normalized scalar kernel.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology BigOperators

namespace HarmonicMaps

private theorem normSq_shift_hasFDerivAt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (y x : E) :
    HasFDerivAt (fun z : E => ‖z - y‖ ^ 2) (2 • innerSL ℝ (x - y)) x := by
  simpa only [ContinuousLinearMap.comp_id, id_eq] using
    ((hasFDerivAt_id x).sub_const y).norm_sq

private theorem normSq_rpow_contDiffAt {n : ℕ} (y : Domain n) (p : ℝ)
    (x : Domain n) (hxy : x ≠ y) :
    ContDiffAt ℝ ∞ (fun z : Domain n => (‖z - y‖ ^ 2) ^ (p)) x := by
  have hnz : ‖x - y‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))
  exact ((contDiff_norm_sq ℝ).contDiffAt.comp x
    (contDiffAt_id.sub contDiffAt_const)).rpow_const_of_ne hnz

private theorem normSq_rpow_hasFDerivAt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (y : E) (p : ℝ) (x : E) (hxy : x ≠ y) :
    HasFDerivAt (fun z : E => (‖z - y‖ ^ 2) ^ (p))
      ((2 * p * (‖x - y‖ ^ 2) ^ (p - 1)) • innerSL ℝ (x - y)) x := by
  have hnz : ‖x - y‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))
  convert (normSq_shift_hasFDerivAt y x).rpow_const (p := p) (Or.inl hnz) using 1
  ext v
  simp only [smul_apply, two_smul, add_apply, smul_eq_mul]
  ring

private theorem normSq_rpow_column {n : ℕ} (y : Domain n) (p : ℝ)
    (x : Domain n) (hxy : x ≠ y) (i : Fin n) :
    fderiv ℝ (fun z : Domain n => (‖z - y‖ ^ 2) ^ (p)) x
      (EuclideanSpace.single i 1) =
      2 * p * (‖x - y‖ ^ 2) ^ (p - 1) * (x - y) i := by
  rw [(normSq_rpow_hasFDerivAt y p x hxy).fderiv]
  simp only [smul_apply, innerSL_apply_apply, EuclideanSpace.inner_single_right,
    one_mul, conj_trivial, smul_eq_mul]

private theorem normSq_rpow_secondColumn {n : ℕ} (y : Domain n) (p : ℝ)
    (x : Domain n) (hxy : x ≠ y) (i : Fin n) :
    fderiv ℝ (fun z : Domain n =>
      fderiv ℝ (fun w : Domain n => (‖w - y‖ ^ 2) ^ (p)) z
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) =
      4 * p * (p - 1) * (‖x - y‖ ^ 2) ^ (p - 2) * ((x - y) i) ^ 2 +
        2 * p * (‖x - y‖ ^ 2) ^ (p - 1) := by
  have hcoord := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const y)
  simp only [Function.comp_def, PiLp.proj_apply, id_eq] at hcoord
  have hscalar := ((normSq_rpow_hasFDerivAt y (p - 1) x hxy).const_mul (2 * p)).mul hcoord
  have heq : (fun z : Domain n =>
      fderiv ℝ (fun w : Domain n => (‖w - y‖ ^ 2) ^ (p)) z
        (EuclideanSpace.single i 1)) =ᶠ[𝓝 x]
      (fun z : Domain n => 2 * p * (‖z - y‖ ^ 2) ^ (p - 1) * (z - y) i) := by
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hxy] with z hz
    exact normSq_rpow_column y p z hz i
  have hdf := hscalar.fderiv
  simp only [Pi.mul_def] at hdf
  rw [heq.fderiv_eq, hdf]
  simp only [smul_apply, add_apply, smul_eq_mul, ContinuousLinearMap.comp_id, PiLp.proj_apply,
    EuclideanSpace.single, PiLp.single_apply, ite_true, innerSL_apply_apply,
    EuclideanSpace.inner_single_right, one_mul, conj_trivial]
  rw [show p - 1 - 1 = p - 2 by ring]
  ring

private theorem scalar_laplacian_coordinateSum {n : ℕ} (f : Domain n → ℝ)
    (x : Domain n) (hf : ContDiffAt ℝ ∞ f x) :
    Laplacian.laplacian f x = ∑ i : Fin n,
      fderiv ℝ (fun z => fderiv ℝ f z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin n) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  rw [EuclideanSpace.basisFun_apply, iteratedFDeriv_two_apply,
    fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, fderiv_const_apply,
    ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]

private theorem normSq_rpow_laplacian {n : ℕ} (y : Domain n) (p : ℝ)
    (x : Domain n) (hxy : x ≠ y) :
    Laplacian.laplacian (fun z : Domain n => (‖z - y‖ ^ 2) ^ (p)) x =
      2 * p * ((n : ℝ) + 2 * p - 2) * (‖x - y‖ ^ 2) ^ (p - 1) := by
  rw [scalar_laplacian_coordinateSum _ x (normSq_rpow_contDiffAt y p x hxy)]
  simp_rw [normSq_rpow_secondColumn y p x hxy]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← EuclideanSpace.real_norm_sq_eq]
  have ht : 0 < ‖x - y‖ ^ 2 := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) _
  have heq : (‖x - y‖ ^ 2) ^ (p - 2) * (‖x - y‖ ^ 2) =
      (‖x - y‖ ^ 2) ^ (p - 1) := by
    rw [show p - 2 = (p - 1) - 1 by ring, Real.rpow_sub_one ht.ne', div_mul_cancel₀ _ ht.ne']
  calc
    _ = 4 * p * (p - 1) *
        ((‖x - y‖ ^ 2) ^ (p - 2) * (‖x - y‖ ^ 2)) +
          (n : ℝ) * (2 * p * (‖x - y‖ ^ 2) ^ (p - 1)) := by ring
    _ = _ := by rw [heq]; ring

private theorem scalar_secondColumn_mul {n : ℕ} (f g : Domain n → ℝ)
    (x : Domain n) (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (i : Fin n) :
    fderiv ℝ (fun z => fderiv ℝ (fun w => f w * g w) z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) =
      f x * fderiv ℝ (fun z => fderiv ℝ g z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) +
      2 * fderiv ℝ f x (EuclideanSpace.single i 1) * fderiv ℝ g x (EuclideanSpace.single i 1) +
      g x * fderiv ℝ (fun z => fderiv ℝ f z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) := by
  have hfx : DifferentiableAt ℝ f x := hf.differentiableAt (by simp)
  have hgx : DifferentiableAt ℝ g x := hg.differentiableAt (by simp)
  have hdf : DifferentiableAt ℝ (fun z => fderiv ℝ f z (EuclideanSpace.single i 1)) x :=
    ((hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).clm_apply
      (differentiableAt_const _)
  have hdg : DifferentiableAt ℝ (fun z => fderiv ℝ g z (EuclideanSpace.single i 1)) x :=
    ((hg.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).clm_apply
      (differentiableAt_const _)
  have hfnear : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ f z :=
    ((hf.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)).eventually (by simp)).mono
      fun _ hz => hz.differentiableAt one_ne_zero
  have hgnear : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ g z :=
    ((hg.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)).eventually (by simp)).mono
      fun _ hz => hz.differentiableAt one_ne_zero
  have heq : (fun z => fderiv ℝ (fun w => f w * g w) z (EuclideanSpace.single i 1)) =ᶠ[𝓝 x]
      (fun z => f z * fderiv ℝ g z (EuclideanSpace.single i 1) +
        g z * fderiv ℝ f z (EuclideanSpace.single i 1)) := by
    filter_upwards [hfnear, hgnear] with z hzf hzg
    rw [fderiv_fun_mul hzf hzg]
    simp only [add_apply, smul_apply, smul_eq_mul]
  have hsecond := ((hfx.hasFDerivAt.mul hdg.hasFDerivAt).add
    (hgx.hasFDerivAt.mul hdf.hasFDerivAt)).fderiv
  simp only [Pi.add_def, Pi.mul_def] at hsecond
  rw [heq.fderiv_eq, hsecond]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

private theorem scalar_laplacian_mul {n : ℕ} (f g : Domain n → ℝ)
    (x : Domain n) (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) :
    Laplacian.laplacian (fun z => f z * g z) x =
      f x * Laplacian.laplacian g x +
        2 * ∑ i : Fin n, fderiv ℝ f x (EuclideanSpace.single i 1) *
          fderiv ℝ g x (EuclideanSpace.single i 1) +
        g x * Laplacian.laplacian f x := by
  rw [scalar_laplacian_coordinateSum _ x (hf.mul hg)]
  simp_rw [scalar_secondColumn_mul f g x hf hg]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [scalar_laplacian_coordinateSum f x hf, scalar_laplacian_coordinateSum g x hg]
  congr 1
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem sourceNumerator_column {n : ℕ} (R : ℝ) (x : Domain n) (i : Fin n) :
    fderiv ℝ (fun z : Domain n => R ^ 2 - ‖z‖ ^ 2) x (EuclideanSpace.single i 1) =
      -2 * x i := by
  have hd : DifferentiableAt ℝ (fun z : Domain n => ‖z‖ ^ 2) x :=
    ((contDiff_norm_sq ℝ (n := 1)).differentiable one_ne_zero).differentiableAt
  rw [fderiv_fun_sub (differentiableAt_const _) hd, fderiv_const_apply, fderiv_norm_sq_apply]
  simp only [sub_apply, zero_apply, two_smul, add_apply, innerSL_apply_apply,
    EuclideanSpace.inner_single_right, one_mul, conj_trivial]
  ring

private theorem sourceNumerator_secondColumn {n : ℕ} (R : ℝ) (x : Domain n) (i : Fin n) :
    fderiv ℝ (fun z => fderiv ℝ (fun w : Domain n => R ^ 2 - ‖w‖ ^ 2) z
      (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) = -2 := by
  have heq : (fun z => fderiv ℝ (fun w : Domain n => R ^ 2 - ‖w‖ ^ 2) z
      (EuclideanSpace.single i 1)) = (fun z : Domain n => -2 * z i) :=
    funext (fun z => sourceNumerator_column R z i)
  have hp := ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i).hasFDerivAt (x := x)).const_mul
    (-2 : ℝ)
  simp only [PiLp.proj_apply] at hp
  rw [heq, hp.fderiv]
  simp only [smul_apply, smul_eq_mul, PiLp.proj_apply,
    EuclideanSpace.single, PiLp.single_apply, ite_true, mul_one]

private theorem sourceNumerator_laplacian {n : ℕ} (R : ℝ) (x : Domain n) :
    Laplacian.laplacian (fun z : Domain n => R ^ 2 - ‖z‖ ^ 2) x = -2 * (n : ℝ) := by
  have hs : ContDiffAt ℝ ∞ (fun z : Domain n => R ^ 2 - ‖z‖ ^ 2) x :=
    contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt
  rw [scalar_laplacian_coordinateSum _ x hs]
  simp_rw [sourceNumerator_secondColumn R x]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private theorem inverseNormPow_eq_normSq_rpow {n : ℕ} (y z : Domain n) :
    (‖z - y‖ ^ n)⁻¹ = (‖z - y‖ ^ 2) ^ (-(n : ℝ) / 2) := by
  calc
    (‖z - y‖ ^ n)⁻¹ = ‖z - y‖ ^ (-(n : ℝ)) := by
      rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
    _ = ‖z - y‖ ^ ((2 : ℝ) * (-(n : ℝ) / 2)) := by congr 1; ring
    _ = (‖z - y‖ ^ 2) ^ (-(n : ℝ) / 2) := by
      rw [Real.rpow_mul (norm_nonneg _), Real.rpow_two]

private theorem scalar_ballKernel_rpow_laplacian {n : ℕ} (R : ℝ) (y : Domain n)
    (hy : ‖y‖ = R) (x : Domain n) (hxy : x ≠ y) :
    Laplacian.laplacian (fun z : Domain n =>
      (R ^ 2 - ‖z‖ ^ 2) * (‖z - y‖ ^ 2) ^ (-(n : ℝ) / 2)) x = 0 := by
  let p : ℝ := -(n : ℝ) / 2
  have hA : ContDiffAt ℝ ∞ (fun z : Domain n => R ^ 2 - ‖z‖ ^ 2) x :=
    contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt
  have hF := normSq_rpow_contDiffAt y p x hxy
  change Laplacian.laplacian (fun z : Domain n =>
    (R ^ 2 - ‖z‖ ^ 2) * (‖z - y‖ ^ 2) ^ p) x = 0
  rw [scalar_laplacian_mul _ _ x hA hF, sourceNumerator_laplacian,
    normSq_rpow_laplacian y p x hxy]
  have hcross : (∑ i : Fin n,
      fderiv ℝ (fun z : Domain n => R ^ 2 - ‖z‖ ^ 2) x (EuclideanSpace.single i 1) *
        fderiv ℝ (fun z : Domain n => (‖z - y‖ ^ 2) ^ p) x (EuclideanSpace.single i 1)) =
      -4 * p * (‖x - y‖ ^ 2) ^ (p - 1) * inner ℝ x (x - y) := by
    simp_rw [sourceNumerator_column, normSq_rpow_column y p x hxy]
    have heq (i : Fin n) : (-2 * x i) *
        (2 * p * (‖x - y‖ ^ 2) ^ (p - 1) * (x - y) i) =
        (-4 * p * (‖x - y‖ ^ 2) ^ (p - 1)) * (x i * (x - y) i) := by ring
    simp_rw [heq]
    rw [← Finset.mul_sum]
    congr 1
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have ht : 0 < ‖x - y‖ ^ 2 := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) _
  have hpower : (‖x - y‖ ^ 2) ^ p = (‖x - y‖ ^ 2) ^ (p - 1) * (‖x - y‖ ^ 2) := by
    rw [Real.rpow_sub_one ht.ne', div_mul_cancel₀ _ ht.ne']
  have hgeo : R ^ 2 - ‖x‖ ^ 2 + 2 * inner ℝ x (x - y) = ‖x - y‖ ^ 2 := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq, norm_sub_sq_real, hy]
    ring
  have hcoefficient : 2 * p * ((n : ℝ) + 2 * p - 2) = 2 * (n : ℝ) := by
    dsimp only [p]
    ring
  rw [hcross, hpower, hcoefficient]
  calc
    _ = 2 * (n : ℝ) * (‖x - y‖ ^ 2) ^ (p - 1) *
        (R ^ 2 - ‖x‖ ^ 2 + 2 * inner ℝ x (x - y) - ‖x - y‖ ^ 2) := by
      dsimp only [p]
      ring
    _ = 0 := by rw [hgeo, sub_self, mul_zero]

/-- The literal normalized scalar Poisson kernel has zero native Euclidean
Laplacian at every actual interior evaluation point and boundary pole. -/
theorem poisson_scalarKernel_laplacian_zero {n : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (y : Domain n)
    (hy : y ∈ Metric.sphere (0 : Domain n) R.val)
    (x : Domain n) (hx : x ∈ Metric.ball (0 : Domain n) R.val) :
    Laplacian.laplacian (fun z : Domain n =>
      ((R.val ^ 2 - ‖z‖ ^ 2) /
        ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) *
        (‖z - y‖ ^ n)⁻¹) x = 0 := by
  have hynorm : ‖y‖ = R.val := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hy
  have hxnorm : ‖x‖ < R.val := by
    simpa only [Metric.mem_ball, dist_zero_right] using hx
  have hxy : x ≠ y := by
    intro heq
    rw [heq, hynorm] at hxnorm
    exact (lt_irrefl R.val) hxnorm
  let B : ℝ := (n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hvolume : 0 < (volume : Measure (Domain n)).real (Metric.ball 0 1) := by
    apply ENNReal.toReal_pos
    · exact Metric.isOpen_ball.measure_ne_zero volume (Metric.nonempty_ball.mpr (by norm_num))
    · exact measure_ball_ne_top
  have hB : 0 < B := mul_pos (mul_pos hnpos hvolume) R.property
  have hformula : (fun z : Domain n =>
      ((R.val ^ 2 - ‖z‖ ^ 2) / B) * (‖z - y‖ ^ n)⁻¹) =
      B⁻¹ • (fun z : Domain n =>
        (R.val ^ 2 - ‖z‖ ^ 2) * (‖z - y‖ ^ 2) ^ (-(n : ℝ) / 2)) := by
    funext z
    rw [inverseNormPow_eq_normSq_rpow]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [hB.ne']
  have hs : ContDiffAt ℝ ∞ (fun z : Domain n =>
      (R.val ^ 2 - ‖z‖ ^ 2) * (‖z - y‖ ^ 2) ^ (-(n : ℝ) / 2)) x :=
    (contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt).mul
      (normSq_rpow_contDiffAt y (-(n : ℝ) / 2) x hxy)
  have hs2 : ContDiffAt ℝ 2 (fun z : Domain n =>
      (R.val ^ 2 - ‖z‖ ^ 2) * (‖z - y‖ ^ 2) ^ (-(n : ℝ) / 2)) x :=
    hs.of_le (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) from WithTop.coe_le_coe.mpr le_top)
  change Laplacian.laplacian (fun z : Domain n =>
    ((R.val ^ 2 - ‖z‖ ^ 2) / B) * (‖z - y‖ ^ n)⁻¹) x = 0
  rw [hformula, InnerProductSpace.laplacian_smul B⁻¹ hs2,
    scalar_ballKernel_rpow_laplacian R.val y hynorm x hxy, smul_zero]

end HarmonicMaps
