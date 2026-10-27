module

public import HolderToCK.Analysis.Poisson.RadialLogDerivatives

/-! # Actual mixed Hessian columns of the nonsingular radial kernels

Both power and logarithmic expressions have the exact Kronecker diagonal
term and coordinate-product term. These are pointwise derivative identities;
the distributional point-evaluation term remains a separate source obligation.
-/

public section
open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology
namespace HolderToCK

theorem normSq_rpow_mixedColumns {n : ℕ} (y : Domain n) (p : ℝ)
    (x : Domain n) (hxy : x ≠ y) (i j : Fin n) :
    fderiv ℝ (fun z : Domain n =>
      fderiv ℝ (fun w : Domain n => (‖w - y‖ ^ 2) ^ (p)) z
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1) =
      4 * p * (p - 1) * (‖x - y‖ ^ 2) ^ (p - 2) * (x - y) i * (x - y) j +
        2 * p * (‖x - y‖ ^ 2) ^ (p - 1) * (if i = j then 1 else 0) := by
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
    EuclideanSpace.single, PiLp.single_apply, innerSL_apply_apply,
    EuclideanSpace.inner_single_right, one_mul, conj_trivial]
  rw [show p - 1 - 1 = p - 2 by ring]
  ring

theorem normSq_log_mixedColumns {n : ℕ} (y x : Domain n) (hxy : x ≠ y) (i j : Fin n) :
    fderiv ℝ (fun z : Domain n =>
      fderiv ℝ (fun w : Domain n => Real.log (‖w - y‖ ^ 2)) z
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1) =
      -4 * (‖x - y‖ ^ 2) ^ (-2 : ℝ) * (x - y) i * (x - y) j +
        2 * (‖x - y‖ ^ 2)⁻¹ * (if i = j then 1 else 0) := by
  have hcoord := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℝ) i).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const y)
  simp only [Function.comp_def, PiLp.proj_apply, id_eq] at hcoord
  have hscalar := ((normSq_rpow_hasFDerivAt y (-1) x hxy).const_mul 2).mul hcoord
  have heq : (fun z : Domain n =>
      fderiv ℝ (fun w : Domain n => Real.log (‖w - y‖ ^ 2)) z (EuclideanSpace.single i 1))
      =ᶠ[𝓝 x] (fun z : Domain n => 2 * (‖z - y‖ ^ 2) ^ (-1 : ℝ) * (z - y) i) := by
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hxy] with z hz
    rw [normSq_log_column y z hz i, Real.rpow_neg_one]
  have hdf := hscalar.fderiv
  simp only [Pi.mul_def] at hdf
  rw [heq.fderiv_eq, hdf]
  simp only [smul_apply, add_apply, smul_eq_mul, ContinuousLinearMap.comp_id, PiLp.proj_apply,
    EuclideanSpace.single, PiLp.single_apply, innerSL_apply_apply,
    EuclideanSpace.inner_single_right, one_mul, conj_trivial]
  norm_num only
  rw [Real.rpow_neg_one]
  ring

theorem normSq_homogeneous_power_harmonic {n : ℕ} (y x : Domain n) (hxy : x ≠ y) :
    Laplacian.laplacian (fun z : Domain n => (‖z - y‖ ^ 2) ^ ((2 - (n : ℝ)) / 2)) x = 0 := by
  rw [normSq_rpow_laplacian y _ x hxy,
    show (n : ℝ) + 2 * ((2 - (n : ℝ)) / 2) - 2 = 0 by ring, mul_zero, zero_mul]

theorem normSq_log_harmonic_two_dimensional (y x : Domain 2) (hxy : x ≠ y) :
    Laplacian.laplacian (fun z : Domain 2 => Real.log (‖z - y‖ ^ 2)) x = 0 := by
  rw [normSq_log_laplacian y x hxy]
  norm_num

end HolderToCK
end
