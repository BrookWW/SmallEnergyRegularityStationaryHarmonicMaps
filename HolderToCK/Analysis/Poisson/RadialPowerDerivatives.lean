module

public import HarmonicMaps.Sobolev
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Radial power derivatives away from the actual singular point

The literal squared-distance power has explicit first and second coordinate
columns and an orthonormal Laplacian trace. No value of a fundamental solution
at the singular point is defined here.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology

namespace HolderToCK

theorem normSq_shift_hasFDerivAt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (y x : E) :
    HasFDerivAt (fun z : E => ‖z - y‖ ^ 2) (2 • innerSL ℝ (x - y)) x := by
  simpa only [ContinuousLinearMap.comp_id, id_eq] using
    ((hasFDerivAt_id x).sub_const y).norm_sq

theorem normSq_rpow_contDiffAt {n : ℕ} (y : Domain n) (p : ℝ)
    (x : Domain n) (hxy : x ≠ y) :
    ContDiffAt ℝ ∞ (fun z : Domain n => (‖z - y‖ ^ 2) ^ (p)) x := by
  have hnz : ‖x - y‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))
  exact ((contDiff_norm_sq ℝ).contDiffAt.comp x
    (contDiffAt_id.sub contDiffAt_const)).rpow_const_of_ne hnz

theorem normSq_rpow_hasFDerivAt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (y : E) (p : ℝ) (x : E) (hxy : x ≠ y) :
    HasFDerivAt (fun z : E => (‖z - y‖ ^ 2) ^ (p))
      ((2 * p * (‖x - y‖ ^ 2) ^ (p - 1)) • innerSL ℝ (x - y)) x := by
  have hnz : ‖x - y‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))
  convert (normSq_shift_hasFDerivAt y x).rpow_const (p := p) (Or.inl hnz) using 1
  ext v
  simp only [smul_apply, two_smul, add_apply, smul_eq_mul]
  ring

theorem normSq_rpow_column {n : ℕ} (y : Domain n) (p : ℝ)
    (x : Domain n) (hxy : x ≠ y) (i : Fin n) :
    fderiv ℝ (fun z : Domain n => (‖z - y‖ ^ 2) ^ (p)) x
      (EuclideanSpace.single i 1) =
      2 * p * (‖x - y‖ ^ 2) ^ (p - 1) * (x - y) i := by
  rw [(normSq_rpow_hasFDerivAt y p x hxy).fderiv]
  simp only [smul_apply, innerSL_apply_apply, EuclideanSpace.inner_single_right,
    one_mul, conj_trivial, smul_eq_mul]

theorem normSq_rpow_secondColumn {n : ℕ} (y : Domain n) (p : ℝ)
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

theorem scalar_laplacian_coordinateSum {n : ℕ} (f : Domain n → ℝ)
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

theorem normSq_rpow_laplacian {n : ℕ} (y : Domain n) (p : ℝ)
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

end HolderToCK
end
