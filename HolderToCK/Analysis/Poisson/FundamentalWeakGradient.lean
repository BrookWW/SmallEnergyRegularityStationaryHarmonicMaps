module

public import HolderToCK.Analysis.Poisson.FundamentalIntegrability
public import HolderToCK.Analysis.Poisson.PuncturedIntegrationByParts
public import Mathlib.Analysis.InnerProductSpace.Laplacian

/-! # Weak first derivatives and the Laplacian pairing of radial primitives -/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology BigOperators

namespace HolderToCK

theorem scalarLaplacian_eq_coordinateSum {n : ℕ} (f : Domain n → ℝ)
    (x : Domain n) (hf : ContDiffAt ℝ 2 f x) :
    Laplacian.laplacian f x = ∑ i : Fin n,
      fderiv ℝ (fun z => fderiv ℝ f z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin n) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  rw [EuclideanSpace.basisFun_apply, iteratedFDeriv_two_apply,
    fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, fderiv_const_apply,
    ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]

private theorem radialPrimitive_testDerivative {n : ℕ} (hn : 2 ≤ n)
    {f : Domain n → ℝ} (hfI : LocallyIntegrable f volume)
    (hf : ∀ x ≠ 0, HasFDerivAt f
      (((euclideanSphereArea n)⁻¹ * ‖x‖ ^ (-(n : ℝ))) • innerSL ℝ x) x)
    {ψ : Domain n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) (i : Fin n) :
    (∫ x, f x * fderiv ℝ ψ x (EuclideanSpace.single i 1)) =
      -∫ x, ((euclideanSphereArea n)⁻¹ * ‖x‖ ^ (-(n : ℝ)) * x i) * ψ x := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega : 0 < n)
  have hv : EuclideanSpace.single i (1 : ℝ) ≠ (0 : Domain n) :=
    (PiLp.single_eq_zero_iff 2 i).not.mpr one_ne_zero
  have htestI := hfI.integrable_smul_right_of_hasCompactSupport hψ.continuous hcψ
  have hdtestI : Integrable (fun x => f x *
      fderiv ℝ ψ x (EuclideanSpace.single i 1)) volume :=
    hfI.integrable_smul_right_of_hasCompactSupport
      ((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const) (hcψ.fderiv_apply ℝ _)
  have hgradI := normalizedRadialColumn_testIntegrable (by omega : 0 < n) i hψ.continuous hcψ
  have hid := punctured_hasFDerivAt_integrationByParts
    (μ := (volume : Measure (Domain n)))
    (by simpa only [finrank_euclideanSpace, Fintype.card_fin] using hn) hv
    (f' := fun x => ((euclideanSphereArea n)⁻¹ * ‖x‖ ^ (-(n : ℝ))) • innerSL ℝ x)
    (g' := fderiv ℝ ψ) ?_ hdtestI htestI hf
    (fun x => (hψ.differentiable one_ne_zero x).hasFDerivAt)
  · simpa only [smul_apply, innerSL_apply_apply, EuclideanSpace.inner_single_right,
      one_mul, conj_trivial, smul_eq_mul] using hid
  · simpa only [smul_apply, innerSL_apply_apply, EuclideanSpace.inner_single_right,
      one_mul, conj_trivial, smul_eq_mul] using hgradI

theorem fundamentalPower_testDerivative {n : ℕ} (hn : 3 ≤ n)
    {ψ : Domain n → ℝ} (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) (i : Fin n) :
    (∫ x, fundamentalPowerExpression x * fderiv ℝ ψ x (EuclideanSpace.single i 1)) =
      -∫ x, ((euclideanSphereArea n)⁻¹ * ‖x‖ ^ (-(n : ℝ)) * x i) * ψ x :=
  radialPrimitive_testDerivative (by omega) (fundamentalPower_locallyIntegrable hn)
    (fundamentalPower_hasFDerivAt hn) hψ hcψ i

theorem fundamentalLog_testDerivative
    {ψ : Domain 2 → ℝ} (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) (i : Fin 2) :
    (∫ x, fundamentalLogExpression x * fderiv ℝ ψ x (EuclideanSpace.single i 1)) =
      -∫ x, ((euclideanSphereArea 2)⁻¹ * ‖x‖ ^ (-(2 : ℝ)) * x i) * ψ x :=
  radialPrimitive_testDerivative (by omega) fundamentalLog_locallyIntegrable
    fundamentalLog_hasFDerivAt hψ hcψ i

private theorem linearMap_apply_coordinates {n : ℕ} (L : Domain n →L[ℝ] ℝ)
    (x : Domain n) :
    L x = ∑ i : Fin n, x i * L (EuclideanSpace.single i 1) := by
  have hx := (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x
  conv_lhs => rw [← hx, map_sum]
  simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply,
    map_smul, smul_eq_mul]

private theorem radialPrimitive_laplacianPairing {n : ℕ} (hn : 2 ≤ n)
    {f : Domain n → ℝ} (hfI : LocallyIntegrable f volume)
    (hf : ∀ x ≠ 0, HasFDerivAt f
      (((euclideanSphereArea n)⁻¹ * ‖x‖ ^ (-(n : ℝ))) • innerSL ℝ x) x)
    {φ : Domain n → ℝ} (hφ : ContDiff ℝ 2 φ) (hcφ : HasCompactSupport φ) :
    (∫ x, f x * Laplacian.laplacian φ x) =
      -∫ x, (euclideanSphereArea n)⁻¹ * ‖x‖ ^ (-(n : ℝ)) * fderiv ℝ φ x x := by
  have hcol (i : Fin n) : ContDiff ℝ 1
      (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hsecI (i : Fin n) : Integrable (fun x => f x *
      fderiv ℝ (fun z => fderiv ℝ φ z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1)) volume :=
    hfI.integrable_smul_right_of_hasCompactSupport
      (((hcol i).continuous_fderiv one_ne_zero).clm_apply continuous_const)
      ((hcφ.fderiv_apply ℝ _).fderiv_apply ℝ _)
  have hgradI (i : Fin n) : Integrable (fun x =>
      ((euclideanSphereArea n)⁻¹ * ‖x‖ ^ (-(n : ℝ)) * x i) *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) volume :=
    normalizedRadialColumn_testIntegrable (by omega : 0 < n) i
      ((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const)
      (hcφ.fderiv_apply ℝ _)
  calc
    _ = ∫ x, ∑ i : Fin n, f x *
        fderiv ℝ (fun z => fderiv ℝ φ z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [scalarLaplacian_eq_coordinateSum φ x hφ.contDiffAt, Finset.mul_sum]
    _ = ∑ i : Fin n, ∫ x, f x *
        fderiv ℝ (fun z => fderiv ℝ φ z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1) := integral_finsetSum Finset.univ (fun i _ => hsecI i)
    _ = ∑ i : Fin n, -(∫ x,
        ((euclideanSphereArea n)⁻¹ * ‖x‖ ^ (-(n : ℝ)) * x i) *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact radialPrimitive_testDerivative hn hfI hf (hcol i) (hcφ.fderiv_apply ℝ _) i
    _ = -∫ x, ∑ i : Fin n,
        ((euclideanSphereArea n)⁻¹ * ‖x‖ ^ (-(n : ℝ)) * x i) *
          fderiv ℝ φ x (EuclideanSpace.single i 1) := by
      rw [Finset.sum_neg_distrib, ← integral_finsetSum Finset.univ (fun i _ => hgradI i)]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      rw [linearMap_apply_coordinates, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem fundamentalPower_laplacianPairing {n : ℕ} (hn : 3 ≤ n)
    {φ : Domain n → ℝ} (hφ : ContDiff ℝ 2 φ) (hcφ : HasCompactSupport φ) :
    (∫ x, fundamentalPowerExpression x * Laplacian.laplacian φ x) =
      -∫ x, (euclideanSphereArea n)⁻¹ * ‖x‖ ^ (-(n : ℝ)) * fderiv ℝ φ x x :=
  radialPrimitive_laplacianPairing (by omega) (fundamentalPower_locallyIntegrable hn)
    (fundamentalPower_hasFDerivAt hn) hφ hcφ

theorem fundamentalLog_laplacianPairing
    {φ : Domain 2 → ℝ} (hφ : ContDiff ℝ 2 φ) (hcφ : HasCompactSupport φ) :
    (∫ x, fundamentalLogExpression x * Laplacian.laplacian φ x) =
      -∫ x, (euclideanSphereArea 2)⁻¹ * ‖x‖ ^ (-(2 : ℝ)) * fderiv ℝ φ x x :=
  radialPrimitive_laplacianPairing (by omega) fundamentalLog_locallyIntegrable
    fundamentalLog_hasFDerivAt hφ hcφ

end HolderToCK
end
