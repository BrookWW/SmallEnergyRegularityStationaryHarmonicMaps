module

public import HarmonicMaps.Analysis.VariableMollificationLimit

/-!
# Sobolev estimates for the source variable smoothing

The literal variable average is a bounded linear Sobolev operator on the
source outer ball. Its original-gradient tensor average is the weak
gradient, with the exact whole-ball and shell square bounds.
-/

public section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace HarmonicMaps

/-- The source derivative majorant gives the exact numerical shell factor. -/
theorem variableMollification_shell_factor_le {L : ℝ} (hL0 : 0 ≤ L) (hL : L ≤ 1 / 4) :
    (1 + L) ^ 2 / (1 - L) ≤ (25 / 12 : ℝ) := by
  have hpos : 0 < 1 - L := by linarith only [hL]
  have hsq : (1 + L) ^ 2 ≤ (5 / 4 : ℝ) ^ 2 :=
    (sq_le_sq₀ (by linarith only [hL0]) (by norm_num)).mpr (by linarith only [hL])
  apply (div_le_iff₀ hpos).mpr
  nlinarith only [hsq, hL]

/-- Complete variable smoothing on the actual finite Sobolev space.
Every sampling and product integral is genuine. The literal averaged tensor
uses the original weak columns, and the two plateaux retain their exact
source behavior. -/
theorem variableMollification_sobolev_estimates {n q : ℕ}
    {s : Domain n → ℝ} {theta delta hbar L : ℝ}
    (hdelta : 0 < delta) (htheta : delta < theta)
    (hhalf : theta + 2 * delta < 1 / 2) (hs : ContDiff ℝ ∞ s)
    (hradial : ∀ x z : Domain n, ‖x‖ = ‖z‖ → s x = s z)
    (hvalues : ∀ x, 0 ≤ s x ∧ s x ≤ hbar)
    (hplateau : ∀ x ∈ Metric.ball (0 : Domain n) theta, s x = hbar)
    (hoff : ∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), s x = 0)
    (hhbar : hbar ≤ delta) (hDs : ∀ x, ‖fderiv ℝ s x‖ ≤ L) (hL : L ≤ 1 / 4)
    (f : Domain n → Ambient q) (Df : Domain n → Gradient n q)
    (hf : MemW12 (ballDomain (0 : Domain n) (theta + 2 * delta)) f Df) :
    let U := Metric.ball (0 : Domain n) (theta + 2 * delta)
    let A := Metric.ball (0 : Domain n) (theta + delta) \ Metric.closedBall 0 theta
    let Aplus := Metric.ball (0 : Domain n) (theta + 2 * delta) \ Metric.closedBall 0 (theta - delta)
    let B := fun x y : Domain n =>
      ContinuousLinearMap.id ℝ (Domain n) - (fderiv ℝ s x).smulRight y
    let G := fun x y (i : Fin n) => ∑ j : Fin n,
      (B x y (EuclideanSpace.single i 1)) j • Df (x - s x • y) j
    let T := fun x : Domain n => ∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • f (x - s x • y)
    let DT := fun x (i : Fin n) => ∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • G x y i
    MemW12 (ballDomain (0 : Domain n) (theta + 2 * delta)) T DT ∧
    (∀ x ∈ U, IntegrableOn (fun y => fixedMollifierKernel n y • f (x - s x • y))
      (Metric.ball (0 : Domain n) 1) volume) ∧
    (∀ x ∈ U, ∀ i : Fin n, IntegrableOn (fun y => fixedMollifierKernel n y • G x y i)
      (Metric.ball (0 : Domain n) 1) volume) ∧
    Integrable (fun p : Domain n × Domain n =>
      fixedMollifierKernel n p.2 • f (p.1 - s p.1 • p.2))
        ((volume.restrict U).prod (volume.restrict (Metric.ball (0 : Domain n) 1))) ∧
    (∀ i : Fin n, Integrable (fun p : Domain n × Domain n =>
      fixedMollifierKernel n p.2 • G p.1 p.2 i)
        ((volume.restrict U).prod (volume.restrict (Metric.ball (0 : Domain n) 1)))) ∧
    Integrable (fun p : Domain n × Domain n =>
      fixedMollifierKernel n p.2 * ‖f (p.1 - s p.1 • p.2)‖ ^ 2)
        ((volume.restrict U).prod (volume.restrict (Metric.ball (0 : Domain n) 1))) ∧
    Integrable (fun p : Domain n × Domain n =>
      fixedMollifierKernel n p.2 * hsNormSq (G p.1 p.2))
        ((volume.restrict U).prod (volume.restrict (Metric.ball (0 : Domain n) 1))) ∧
    (∫ x in U, ‖T x‖ ^ 2) ≤ (1 - L)⁻¹ * ∫ z in U, ‖f z‖ ^ 2 ∧
    (∫ x in U, hsNormSq (DT x)) ≤
      ((1 + L) ^ 2 / (1 - L)) * ∫ z in U, hsNormSq (Df z) ∧
    (∫ x in A, hsNormSq (DT x)) ≤
      ((1 + L) ^ 2 / (1 - L)) * ∫ z in Aplus, hsNormSq (Df z) ∧
    (∫ x in A, hsNormSq (DT x)) ≤ (25 / 12 : ℝ) * ∫ z in Aplus, hsNormSq (Df z) ∧
    (∀ x ∈ U, s x = 0 → T x = f x) ∧
    (∀ a : ℝ, ∀ x ∈ U,
      (∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • (a • f (x - s x • y))) = a • T x) ∧
    ∀ (g : Domain n → Ambient q) (Dg : Domain n → Gradient n q),
      MemW12 (ballDomain (0 : Domain n) (theta + 2 * delta)) g Dg →
      ∀ x ∈ U, (∫ y in Metric.ball (0 : Domain n) 1,
        fixedMollifierKernel n y • (f (x - s x • y) + g (x - s x • y))) =
          T x + (∫ y in Metric.ball (0 : Domain n) 1,
            fixedMollifierKernel n y • g (x - s x • y)) := by
  let U := Metric.ball (0 : Domain n) (theta + 2 * delta)
  let A := Metric.ball (0 : Domain n) (theta + delta) \ Metric.closedBall 0 theta
  let Aplus := Metric.ball (0 : Domain n) (theta + 2 * delta) \ Metric.closedBall 0 (theta - delta)
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr measure_ball_ne_top
  letI : IsFiniteMeasure (volume.restrict Aplus) := isFiniteMeasure_restrict.mpr
    (ne_top_of_le_ne_top measure_ball_ne_top (measure_mono sdiff_subset))
  have hL0 : 0 ≤ L := (norm_nonneg (fderiv ℝ s (0 : Domain n))).trans (hDs 0)
  have hK : 0 ≤ (1 - L)⁻¹ := inv_nonneg.mpr (by linarith only [hL])
  have hboundU (y : Domain n) (hy : y ∈ Metric.ball 0 1) :=
    (variableShift_map_restrict_le hdelta htheta hhalf hs hradial hvalues hplateau hoff
      hhbar hDs hL y hy).1
  have hboundA (y : Domain n) (hy : y ∈ Metric.ball 0 1) :=
    (variableShift_map_restrict_le hdelta htheta hhalf hs hradial hvalues hplateau hoff
      hhbar hDs hL y hy).2
  have hMap := variableMollification_map_bounds hs hK hboundU hf.2.1
  have hTensorU := variableMollification_tensor_bounds hs hDs hK hboundU hf.2.2
  have hDfAplus (i : Fin n) : MemLp (fun x => Df x i) 2 (volume.restrict Aplus) :=
    (hf.2.2 i).mono_measure (Measure.restrict_mono sdiff_subset le_rfl)
  have hTensorA := variableMollification_tensor_bounds hs hDs hK hboundA hDfAplus
  have hW := hf.variableMollification hdelta htheta hhalf hs hradial hvalues hplateau
    hoff hhbar hDs hL
  refine ⟨hW, ?_, ?_, hMap.1, hTensorU.1, hMap.2.1, hTensorU.2.1,
    hMap.2.2.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x _
    exact variableMollification_weighted_sampling_integrable hvalues hhbar hoff hf.integrable_ball x
  · intro x _ i
    exact variableMollification_tensor_integrable hvalues hhbar hoff hf.column_integrable_ball x i
  · rw [div_eq_mul_inv]
    exact hTensorU.2.2.2
  · rw [div_eq_mul_inv]
    exact hTensorA.2.2.2
  · have hShell : (∫ x in A,
        hsNormSq (fun i => ∫ y in Metric.ball (0 : Domain n) 1, fixedMollifierKernel n y •
          ∑ j : Fin n, ((ContinuousLinearMap.id ℝ (Domain n) -
            (fderiv ℝ s x).smulRight y) (EuclideanSpace.single i 1)) j • Df (x - s x • y) j)) ≤
        ((1 + L) ^ 2 / (1 - L)) * ∫ z in Aplus, hsNormSq (Df z) := by
      rw [div_eq_mul_inv]
      exact hTensorA.2.2.2
    exact hShell.trans (mul_le_mul_of_nonneg_right
      (variableMollification_shell_factor_le hL0 hL)
      (integral_nonneg (fun z => hsNormSq_nonneg (Df z))))
  · intro x _ hx
    exact variableMollification_eq_of_zero s f hx
  · intro a x _
    exact variableMollification_smul s f a x
  · intro g Dg hg x _
    exact variableMollification_add hvalues hhbar hoff hf.integrable_ball hg.integrable_ball x

/-- Both weak-test pairings for the actual variable average and its original
tensor columns are integrable on the source ball. -/
theorem variableMollification_pairings_integrable {n q : ℕ}
    {s : Domain n → ℝ} {theta delta hbar L : ℝ}
    (hdelta : 0 < delta) (htheta : delta < theta)
    (hhalf : theta + 2 * delta < 1 / 2) (hs : ContDiff ℝ ∞ s)
    (hradial : ∀ x z : Domain n, ‖x‖ = ‖z‖ → s x = s z)
    (hvalues : ∀ x, 0 ≤ s x ∧ s x ≤ hbar)
    (hplateau : ∀ x ∈ Metric.ball (0 : Domain n) theta, s x = hbar)
    (hoff : ∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), s x = 0)
    (hhbar : hbar ≤ delta) (hDs : ∀ x, ‖fderiv ℝ s x‖ ≤ L) (hL : L ≤ 1 / 4)
    {f : Domain n → Ambient q} {Df : Domain n → Gradient n q}
    (hf : MemW12 (ballDomain (0 : Domain n) (theta + 2 * delta)) f Df)
    (i : Fin n) (φ : Domain n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Metric.ball (0 : Domain n) (theta + 2 * delta)) :
    let T := fun x : Domain n => ∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • f (x - s x • y)
    let DT := fun x (i : Fin n) => ∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • ∑ j : Fin n,
        ((ContinuousLinearMap.id ℝ (Domain n) - (fderiv ℝ s x).smulRight y)
          (EuclideanSpace.single i 1)) j • Df (x - s x • y) j
    IntegrableOn (fun x => coordinateDerivative φ hφ i x • T x)
        (Metric.ball (0 : Domain n) (theta + 2 * delta)) volume ∧
    IntegrableOn (fun x => φ x • DT x i)
        (Metric.ball (0 : Domain n) (theta + 2 * delta)) volume := by
  have hW := hf.variableMollification hdelta htheta hhalf hs hradial hvalues hplateau
    hoff hhbar hDs hL
  exact ⟨hW.1.integrable_test_derivative i hφ hcφ hsφ,
    hW.1.integrable_test_gradient i hφ hcφ hsφ⟩

end HarmonicMaps
