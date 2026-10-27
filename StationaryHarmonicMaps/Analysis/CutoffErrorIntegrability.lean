module

public import StationaryHarmonicMaps.Analysis.ExpandedCutoffErrorBound
public import StationaryHarmonicMaps.Analysis.HSProductIntegrals
public import StationaryHarmonicMaps.Analysis.CutoffErrorSupport

/-!
# Actual measurability and finite-measure integrals of the expanded cutoff error

The native smooth scalar Laplacian is continuous. Actual L² columns and
orthogonality then produce the four-term error's measurability and L¹
integrability, with each HS product integral retained in the bound.
-/

public section

open HarmonicMaps MeasureTheory Filter Set
open scoped ContDiff

namespace StationaryHarmonicMaps.Analysis

/-- A smooth scalar cutoff has a continuous native Laplacian. -/
theorem continuous_laplacian_of_contDiff {n : ℕ} {χ : Domain n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) : Continuous (Laplacian.laplacian χ) := by
  let dχ (i : Fin n) (x : Domain n) := fderiv ℝ χ x (EuclideanSpace.single i 1)
  have hdχ (i : Fin n) : ContDiff ℝ ∞ (dχ i) :=
    (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have heq (x : Domain n) : Laplacian.laplacian χ x =
      ∑ i : Fin n, fderiv ℝ (dχ i) x (EuclideanSpace.single i 1) := by
    have hdf : ContDiff ℝ ∞ (fderiv ℝ χ) := hχ.fderiv_right (m := ∞) (by simp)
    have hd : DifferentiableAt ℝ (fderiv ℝ χ) x := hdf.differentiable (by simp) x
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis χ
      (EuclideanSpace.basisFun (Fin n) ℝ)]
    apply Finset.sum_congr rfl
    intro i _hi
    dsimp only [dχ]
    rw [EuclideanSpace.basisFun_apply, iteratedFDeriv_two_apply,
      fderiv_clm_apply hd (differentiableAt_const _)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, fderiv_const_apply,
      ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
  have heqfun : Laplacian.laplacian χ =
      (fun x => ∑ i : Fin n, fderiv ℝ (dχ i) x (EuclideanSpace.single i 1)) := funext heq
  rw [heqfun]
  exact continuous_finsetSum _ (fun i _ =>
    ((hdχ i).continuous_fderiv (by simp)).clm_apply continuous_const)

/-- The same literal expanded error is a.e. strongly measurable from its actual coefficient data. -/
theorem aestronglyMeasurable_expanded_cutoff_error {n m q : ℕ} {μ : Measure (Domain n)}
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (p : Domain n → Ambient m) (dp z : Domain n → Gradient n m)
    (w : Domain n → Ambient q) (v : Domain n → Gradient n q)
    (hp : AEStronglyMeasurable p μ)
    (hdp : ∀ i, AEStronglyMeasurable (fun x => dp x i) μ)
    (hz : ∀ i, AEStronglyMeasurable (fun x => z x i) μ)
    (hw : AEStronglyMeasurable w μ)
    (hv : ∀ i, AEStronglyMeasurable (fun x => v x i) μ)
    (χ : Domain n → ℝ) (hχ : ContDiff ℝ ∞ χ) :
    AEStronglyMeasurable (fun x =>
      (∑ i : Fin n, fderiv ℝ χ x (EuclideanSpace.single i 1) • star (R (dp x i)) (w x)) +
      (2 : ℝ) • (∑ i : Fin n, fderiv ℝ χ x (EuclideanSpace.single i 1) • star (R (p x)) (v x i)) +
      Laplacian.laplacian χ x • star (R (p x)) (w x) +
      ∑ i : Fin n, fderiv ℝ χ x (EuclideanSpace.single i 1) • R (z x i) (star (R (p x)) (w x))) μ := by
  have hstar : Continuous (star : (Ambient q →L[ℝ] Ambient q) → (Ambient q →L[ℝ] Ambient q)) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Ambient q) (F := Ambient q)).continuous
  have hP := hstar.comp_aestronglyMeasurable (R.continuous.comp_aestronglyMeasurable hp)
  have happly (A : Domain n → Ambient q →L[ℝ] Ambient q)
      (a : Domain n → Ambient q) (hA : AEStronglyMeasurable A μ)
      (ha : AEStronglyMeasurable a μ) : AEStronglyMeasurable (fun x => A x (a x)) μ :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hA.prodMk ha)
  have hdχ (i : Fin n) : AEStronglyMeasurable
      (fun x => fderiv ℝ χ x (EuclideanSpace.single i 1)) μ :=
    ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable
  have hfirst := Finset.aestronglyMeasurable_fun_sum Finset.univ (fun i _ =>
    (hdχ i).smul (happly _ _
      (hstar.comp_aestronglyMeasurable (R.continuous.comp_aestronglyMeasurable (hdp i))) hw))
  have hsecond := Finset.aestronglyMeasurable_fun_sum Finset.univ (fun i _ =>
    (hdχ i).smul (happly _ _ hP (hv i)))
  have hthird := (continuous_laplacian_of_contDiff hχ).aestronglyMeasurable.smul (happly _ _ hP hw)
  have hfourth := Finset.aestronglyMeasurable_fun_sum Finset.univ (fun i _ =>
    (hdχ i).smul (happly _ _ (R.continuous.comp_aestronglyMeasurable (hz i)) (happly _ _ hP hw)))
  exact ((hfirst.add (hsecond.const_smul (2 : ℝ))).add hthird).add hfourth

/-- Actual L² data and orthogonality give L¹ of the literal error and its raw HS integral bound. -/
theorem integrable_expanded_cutoff_error_of_L2 {n m q : ℕ} {μ : Measure (Domain n)}
    [IsFiniteMeasure μ]
    (R : Ambient m →L[ℝ] (Ambient q →L[ℝ] Ambient q))
    (p : Domain n → Ambient m) (dp z : Domain n → Gradient n m)
    (w : Domain n → Ambient q) (v : Domain n → Gradient n q)
    (hp : MemLp p 2 μ) (hdp : ∀ i, MemLp (fun x => dp x i) 2 μ)
    (hz : ∀ i, MemLp (fun x => z x i) 2 μ) (hw : MemLp w 2 μ)
    (hv : ∀ i, MemLp (fun x => v x i) 2 μ)
    (horth : ∀ᵐ x ∂μ, star (R (p x)) * R (p x) = 1)
    (χ : Domain n → ℝ) (hχ : ContDiff ℝ ∞ χ) {B K : ℝ} (hB : 0 ≤ B)
    (hdχ : ∀ x i, |fderiv ℝ χ x (EuclideanSpace.single i 1)| ≤ B)
    (hKχ : ∀ x, |Laplacian.laplacian χ x| ≤ K) :
    let e (x : Domain n) :=
      (∑ i : Fin n, fderiv ℝ χ x (EuclideanSpace.single i 1) • star (R (dp x i)) (w x)) +
      (2 : ℝ) • (∑ i : Fin n, fderiv ℝ χ x (EuclideanSpace.single i 1) • star (R (p x)) (v x i)) +
      Laplacian.laplacian χ x • star (R (p x)) (w x) +
      ∑ i : Fin n, fderiv ℝ χ x (EuclideanSpace.single i 1) • R (z x i) (star (R (p x)) (w x))
    Integrable e μ ∧
      (∫ x, ‖e x‖ ∂μ) ≤ B * Real.sqrt (n : ℝ) *
        (‖R‖ * (∫ x, Real.sqrt (hsNormSq (dp x)) * ‖w x‖ ∂μ) +
          2 * (∫ x, Real.sqrt (hsNormSq (v x)) ∂μ) +
          ‖R‖ * (∫ x, Real.sqrt (hsNormSq (z x)) * ‖w x‖ ∂μ)) +
        K * ∫ x, ‖w x‖ ∂μ := by
  dsimp only
  let e (x : Domain n) :=
    (∑ i : Fin n, fderiv ℝ χ x (EuclideanSpace.single i 1) • star (R (dp x i)) (w x)) +
    (2 : ℝ) • (∑ i : Fin n, fderiv ℝ χ x (EuclideanSpace.single i 1) • star (R (p x)) (v x i)) +
    Laplacian.laplacian χ x • star (R (p x)) (w x) +
    ∑ i : Fin n, fderiv ℝ χ x (EuclideanSpace.single i 1) • R (z x i) (star (R (p x)) (w x))
  let H (x : Domain n) := B * Real.sqrt (n : ℝ) *
    (‖R‖ * (Real.sqrt (hsNormSq (dp x)) * ‖w x‖) +
      2 * Real.sqrt (hsNormSq (v x)) + ‖R‖ * (Real.sqrt (hsNormSq (z x)) * ‖w x‖)) + K * ‖w x‖
  have h1 := (integral_hs_mul_norm_le dp w hdp hw).1.const_mul ‖R‖
  have h2 := (integral_hs_le_sqrt_measure_mul_energy v hv).1.const_mul 2
  have h3 := (integral_hs_mul_norm_le z w hz hw).1.const_mul ‖R‖
  have h4 := ((hw.integrable (by norm_num)).norm).const_mul K
  have h12 : Integrable (fun x => ‖R‖ * (Real.sqrt (hsNormSq (dp x)) * ‖w x‖) +
      2 * Real.sqrt (hsNormSq (v x))) μ := h1.add h2
  have h123 : Integrable (fun x => ‖R‖ * (Real.sqrt (hsNormSq (dp x)) * ‖w x‖) +
      2 * Real.sqrt (hsNormSq (v x)) + ‖R‖ * (Real.sqrt (hsNormSq (z x)) * ‖w x‖)) μ := h12.add h3
  have hscaled : Integrable (fun x => B * Real.sqrt (n : ℝ) *
      (‖R‖ * (Real.sqrt (hsNormSq (dp x)) * ‖w x‖) +
        2 * Real.sqrt (hsNormSq (v x)) + ‖R‖ * (Real.sqrt (hsNormSq (z x)) * ‖w x‖))) μ :=
    h123.const_mul _
  have hH : Integrable H μ := hscaled.add h4
  have hpoint : ∀ᵐ x ∂μ, ‖e x‖ ≤ H x := by
    filter_upwards [horth] with x hx
    have h := expanded_cutoff_error_norm_le_hs (R (p x)) hx R (dp x) (z x) (v x) (w x)
      (fun i => fderiv ℝ χ x (EuclideanSpace.single i 1)) (Laplacian.laplacian χ x)
      hB (hdχ x) (hKχ x)
    simpa only [e, H, mul_assoc] using h
  have hmeas := aestronglyMeasurable_expanded_cutoff_error R p dp z w v
    hp.aestronglyMeasurable (fun i => (hdp i).aestronglyMeasurable)
    (fun i => (hz i).aestronglyMeasurable) hw.aestronglyMeasurable
    (fun i => (hv i).aestronglyMeasurable) χ hχ
  have heInt : Integrable e μ := hH.mono' hmeas hpoint
  refine ⟨heInt, ?_⟩
  calc
    _ ≤ ∫ x, H x ∂μ := integral_mono_ae heInt.norm hH hpoint
    _ = _ := by
      dsimp only [H]
      rw [integral_add hscaled h4,
        integral_const_mul, integral_add h12 h3, integral_add h1 h2,
        integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]

end StationaryHarmonicMaps.Analysis

end
