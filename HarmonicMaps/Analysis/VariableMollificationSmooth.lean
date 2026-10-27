module

public import HarmonicMaps.Analysis.VariableMollificationSampling
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiation of variable smoothing on its actual open domain

Compact sampling images inside the source domain bound the actual derivative
integrand on a common parameter neighborhood. Differentiation under the
integral therefore applies to locally smooth input maps.
-/

public section

open MeasureTheory Filter Set
open scoped ContDiff Topology

namespace HarmonicMaps

/-- Local smooth input and closed-ball sampling give the genuine differential
of the literal variable average. The sampling premise is discharged by the
source cutoff geometry in the source-facing theorem. -/
theorem variableMollification_hasFDerivAt_of_sampling {n q : ℕ}
    {s : Domain n → ℝ} {R : ℝ} (hs : ContDiff ℝ ∞ s)
    {f : Domain n → Ambient q} (hf : ContDiffOn ℝ ∞ f (Metric.ball 0 R))
    (hsample : ∀ x ∈ Metric.ball (0 : Domain n) R,
      ∀ y ∈ Metric.closedBall (0 : Domain n) 1, variableShift s y x ∈ Metric.ball 0 R)
    {x : Domain n} (hx : x ∈ Metric.ball 0 R) :
    IntegrableOn (fun y => fixedMollifierKernel n y • f (variableShift s y x))
        (Metric.ball (0 : Domain n) 1) volume ∧
    IntegrableOn (fun y => fixedMollifierKernel n y •
      ((fderiv ℝ f (variableShift s y x)).comp
        (ContinuousLinearMap.id ℝ (Domain n) - (fderiv ℝ s x).smulRight y)))
        (Metric.ball (0 : Domain n) 1) volume ∧
    HasFDerivAt (fun x => ∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • f (variableShift s y x))
      (∫ y in Metric.ball (0 : Domain n) 1, fixedMollifierKernel n y •
        ((fderiv ℝ f (variableShift s y x)).comp
          (ContinuousLinearMap.id ℝ (Domain n) - (fderiv ℝ s x).smulRight y))) x := by
  let U := Metric.ball (0 : Domain n) R
  let V := Metric.closedBall (0 : Domain n) 1
  let P := fun p : Domain n × Domain n => variableShift s p.2 p.1
  let B := fun p : Domain n × Domain n =>
    ContinuousLinearMap.id ℝ (Domain n) - (fderiv ℝ s p.1).smulRight p.2
  let H := fun z y : Domain n => fixedMollifierKernel n y • f (variableShift s y z)
  let DH := fun z y : Domain n => fixedMollifierKernel n y •
    ((fderiv ℝ f (variableShift s y z)).comp (B (z, y)))
  have hP : Continuous P := by
    dsimp only [P, variableShift]
    fun_prop
  have hB : Continuous B := by
    exact continuous_const.sub
      (((ContinuousLinearMap.smulRightL ℝ (Domain n) (Domain n)).continuous.comp
        ((hs.continuous_fderiv (by simp)).comp continuous_fst)).clm_apply continuous_snd)
  have hdf : ∀ z ∈ U, DifferentiableAt ℝ f z := by
    intro z hz
    exact ((hf z hz).contDiffAt (Metric.isOpen_ball.mem_nhds hz)).differentiableAt (by simp)
  have hcdf : ContinuousOn (fderiv ℝ f) U := by
    intro z hz
    exact (((hf z hz).contDiffAt (Metric.isOpen_ball.mem_nhds hz)).continuousAt_fderiv
      (by simp)).continuousWithinAt
  have hHy (z : Domain n) (hz : z ∈ U) : ContinuousOn (H z) V := by
    exact (fixedMollifierKernel_contDiff n).continuous.continuousOn.smul
      (hf.continuousOn.comp
        (hP.comp (continuous_const.prodMk continuous_id)).continuousOn (hsample z hz))
  have hDHy (z : Domain n) (hz : z ∈ U) : ContinuousOn (DH z) V := by
    exact (fixedMollifierKernel_contDiff n).continuous.continuousOn.smul
      ((hcdf.comp (hP.comp (continuous_const.prodMk continuous_id)).continuousOn
        (hsample z hz)).clm_comp
          (hB.comp (continuous_const.prodMk continuous_id)).continuousOn)
  have hiH (z : Domain n) (hz : z ∈ U) :
      IntegrableOn (H z) (Metric.ball (0 : Domain n) 1) volume :=
    ((hHy z hz).integrableOn_compact (isCompact_closedBall _ _)).mono_set
      Metric.ball_subset_closedBall
  have hiDH (z : Domain n) (hz : z ∈ U) :
      IntegrableOn (DH z) (Metric.ball (0 : Domain n) 1) volume :=
    ((hDHy z hz).integrableOn_compact (isCompact_closedBall _ _)).mono_set
      Metric.ball_subset_closedBall
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (Metric.isOpen_ball.mem_nhds hx)
  let K := Metric.closedBall x (r / 2) ×ˢ V
  have hK : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hKsample : MapsTo P K U := by
    intro p hp
    exact hsample p.1 (hball (Metric.closedBall_subset_ball (by linarith only [hr]) hp.1))
      p.2 hp.2
  have hKDH : ContinuousOn (fun p : Domain n × Domain n => DH p.1 p.2) K := by
    exact ((fixedMollifierKernel_contDiff n).continuous.comp continuous_snd).continuousOn.smul
      ((hcdf.comp hP.continuousOn hKsample).clm_comp hB.continuousOn)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hKDH
  letI : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Domain n) 1)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  refine ⟨hiH x hx, hiDH x hx, ?_⟩
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := H) (F' := DH) (s := Metric.ball x (r / 2)) (bound := fun _ => C)
      (Metric.ball_mem_nhds _ (by linarith only [hr]))
  · filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
    exact (hiH z hz).aestronglyMeasurable
  · exact hiH x hx
  · exact (hiDH x hx).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_ball] with y hy z hz
    exact hC (z, y) ⟨Metric.ball_subset_closedBall hz, Metric.ball_subset_closedBall hy⟩
  · exact integrable_const C
  · filter_upwards [ae_restrict_mem measurableSet_ball] with y hy z hz
    have hzU : z ∈ U := hball
      (Metric.closedBall_subset_ball (by linarith only [hr]) (Metric.ball_subset_closedBall hz))
    exact ((hdf _ (hsample z hzU y (Metric.ball_subset_closedBall hy))).hasFDerivAt.comp z
      (hasFDerivAt_variableShift ((hs.differentiable (by simp)) z) y)).const_smul
        (fixedMollifierKernel n y)

/- The source-facing scope retains every cutoff assumption. -/
/-- The complete source cutoff data give the actual local smooth-input
differential formula and both actual averaging integrabilities. -/
theorem variableMollification_smooth_formula {n q : ℕ}
    {s : Domain n → ℝ} {theta delta hbar L : ℝ}
    (_hdelta : 0 < delta) (_htheta : delta < theta)
    (_hhalf : theta + 2 * delta < 1 / 2) (hs : ContDiff ℝ ∞ s)
    (_hradial : ∀ x z : Domain n, ‖x‖ = ‖z‖ → s x = s z)
    (hvalues : ∀ x, 0 ≤ s x ∧ s x ≤ hbar)
    (_hplateau : ∀ x ∈ Metric.ball (0 : Domain n) theta, s x = hbar)
    (hoff : ∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), s x = 0)
    (hhbar : hbar ≤ delta) (_hDs : ∀ x, ‖fderiv ℝ s x‖ ≤ L) (_hL : L ≤ 1 / 4)
    (f : Domain n → Ambient q)
    (hf : ContDiffOn ℝ ∞ f (Metric.ball (0 : Domain n) (theta + 2 * delta))) :
    let U := Metric.ball (0 : Domain n) (theta + 2 * delta)
    let B := fun x y : Domain n =>
      ContinuousLinearMap.id ℝ (Domain n) - (fderiv ℝ s x).smulRight y
    let T := fun x : Domain n => ∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • f (x - s x • y)
    (∀ x ∈ U, IntegrableOn (fun y => fixedMollifierKernel n y • f (x - s x • y))
      (Metric.ball (0 : Domain n) 1) volume) ∧
    (∀ x ∈ U, IntegrableOn (fun y => fixedMollifierKernel n y •
      ((fderiv ℝ f (x - s x • y)).comp (B x y)))
        (Metric.ball (0 : Domain n) 1) volume) ∧
    ∀ x ∈ U, HasFDerivAt T
      (∫ y in Metric.ball (0 : Domain n) 1, fixedMollifierKernel n y •
        ((fderiv ℝ f (x - s x • y)).comp (B x y))) x := by
  have hpoint (x : Domain n) (hx : x ∈ Metric.ball 0 (theta + 2 * delta)) :=
    variableMollification_hasFDerivAt_of_sampling hs hf
      (fun z hz y hy => variableShift_mem_outerBall_of_mem_closedBall hvalues hhbar hoff hz hy) hx
  exact ⟨fun x hx => (hpoint x hx).1, fun x hx => (hpoint x hx).2.1,
    fun x hx => (hpoint x hx).2.2⟩

/-- The genuine smooth differential has the source tensor factor in each
column, with the actual classical columns of the same input map. -/
theorem variableMollification_smooth_column {n q : ℕ}
    {s : Domain n → ℝ} {theta delta hbar L : ℝ}
    (hdelta : 0 < delta) (htheta : delta < theta)
    (hhalf : theta + 2 * delta < 1 / 2) (hs : ContDiff ℝ ∞ s)
    (hradial : ∀ x z : Domain n, ‖x‖ = ‖z‖ → s x = s z)
    (hvalues : ∀ x, 0 ≤ s x ∧ s x ≤ hbar)
    (hplateau : ∀ x ∈ Metric.ball (0 : Domain n) theta, s x = hbar)
    (hoff : ∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), s x = 0)
    (hhbar : hbar ≤ delta) (hDs : ∀ x, ‖fderiv ℝ s x‖ ≤ L) (hL : L ≤ 1 / 4)
    (f : Domain n → Ambient q)
    (hf : ContDiffOn ℝ ∞ f (Metric.ball (0 : Domain n) (theta + 2 * delta)))
    {x : Domain n} (hx : x ∈ Metric.ball 0 (theta + 2 * delta)) (i : Fin n) :
    fderiv ℝ (fun x : Domain n => ∫ y in Metric.ball (0 : Domain n) 1,
      fixedMollifierKernel n y • f (x - s x • y)) x (EuclideanSpace.single i 1) =
      ∫ y in Metric.ball (0 : Domain n) 1, fixedMollifierKernel n y •
        ∑ j : Fin n, ((ContinuousLinearMap.id ℝ (Domain n) -
          (fderiv ℝ s x).smulRight y) (EuclideanSpace.single i 1)) j •
          fderiv ℝ f (x - s x • y) (EuclideanSpace.single j 1) := by
  obtain ⟨_, hDI, hD⟩ := variableMollification_smooth_formula hdelta htheta hhalf hs hradial
    hvalues hplateau hoff hhbar hDs hL f hf
  rw [(hD x hx).fderiv, ContinuousLinearMap.integral_apply (hDI x hx)]
  apply setIntegral_congr_fun measurableSet_ball
  intro y _
  change fixedMollifierKernel n y •
    (fderiv ℝ f (x - s x • y))
      ((ContinuousLinearMap.id ℝ (Domain n) - (fderiv ℝ s x).smulRight y)
        (EuclideanSpace.single i 1)) = _
  rw [domain_clm_apply_eq_sum_columns]

end HarmonicMaps
