module

public import HolderToCK.Analysis.Poisson.RadialPowerDerivatives
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Logarithmic radial derivatives at nonsingular points

The squared-distance logarithm supplies the two-dimensional fundamental
solution calculation. Every derivative is evaluated away from its actual
singular point; no source kernel value at that point is specified.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology

namespace HolderToCK

theorem normSq_log_contDiffAt {n : ℕ} (y x : Domain n) (hxy : x ≠ y) :
    ContDiffAt ℝ ∞ (fun z : Domain n => Real.log (‖z - y‖ ^ 2)) x := by
  have hnz : ‖x - y‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))
  exact ((contDiff_norm_sq ℝ).contDiffAt.comp x
    (contDiffAt_id.sub contDiffAt_const)).log hnz

theorem normSq_log_hasFDerivAt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (y x : E) (hxy : x ≠ y) :
    HasFDerivAt (fun z : E => Real.log (‖z - y‖ ^ 2))
      ((2 * (‖x - y‖ ^ 2)⁻¹) • innerSL ℝ (x - y)) x := by
  have hnz : ‖x - y‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))
  convert (normSq_shift_hasFDerivAt y x).log hnz using 1
  ext v
  simp only [smul_apply, two_smul, add_apply, smul_eq_mul]
  ring

theorem normSq_log_column {n : ℕ} (y x : Domain n) (hxy : x ≠ y) (i : Fin n) :
    fderiv ℝ (fun z : Domain n => Real.log (‖z - y‖ ^ 2)) x
      (EuclideanSpace.single i 1) = 2 * (‖x - y‖ ^ 2)⁻¹ * (x - y) i := by
  rw [(normSq_log_hasFDerivAt y x hxy).fderiv]
  simp only [smul_apply, innerSL_apply_apply, EuclideanSpace.inner_single_right,
    one_mul, conj_trivial, smul_eq_mul]

theorem normSq_log_secondColumn {n : ℕ} (y x : Domain n) (hxy : x ≠ y) (i : Fin n) :
    fderiv ℝ (fun z : Domain n =>
      fderiv ℝ (fun w : Domain n => Real.log (‖w - y‖ ^ 2)) z
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) =
      -4 * (‖x - y‖ ^ 2) ^ (-2 : ℝ) * ((x - y) i) ^ 2 + 2 * (‖x - y‖ ^ 2)⁻¹ := by
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
    EuclideanSpace.single, PiLp.single_apply, ite_true, innerSL_apply_apply,
    EuclideanSpace.inner_single_right, one_mul, conj_trivial]
  norm_num only
  rw [Real.rpow_neg_one]
  ring

theorem normSq_log_laplacian {n : ℕ} (y x : Domain n) (hxy : x ≠ y) :
    Laplacian.laplacian (fun z : Domain n => Real.log (‖z - y‖ ^ 2)) x =
      2 * ((n : ℝ) - 2) * (‖x - y‖ ^ 2)⁻¹ := by
  rw [scalar_laplacian_coordinateSum _ x (normSq_log_contDiffAt y x hxy)]
  simp_rw [normSq_log_secondColumn y x hxy]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← EuclideanSpace.real_norm_sq_eq]
  have hs : 0 < ‖x - y‖ ^ 2 := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) _
  have hpower : (‖x - y‖ ^ 2) ^ (-2 : ℝ) * (‖x - y‖ ^ 2) = (‖x - y‖ ^ 2)⁻¹ := by
    rw [show (-2 : ℝ) = -1 - 1 by norm_num, Real.rpow_sub_one hs.ne',
      div_mul_cancel₀ _ hs.ne', Real.rpow_neg_one]
  calc
    _ = -4 * ((‖x - y‖ ^ 2) ^ (-2 : ℝ) * (‖x - y‖ ^ 2)) +
        (n : ℝ) * (2 * (‖x - y‖ ^ 2)⁻¹) := by ring
    _ = _ := by rw [hpower]; ring

end HolderToCK
end
