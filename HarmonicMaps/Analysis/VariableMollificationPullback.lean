module

public import HarmonicMaps.Analysis.VariableShiftDiffeomorphism
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Sharp restricted-measure bounds for variable translations

The forward variable translation pushes restricted volume to at most
`(1-L)⁻¹` times restricted volume. The exact source ball and shell estimates
follow from the actual Jacobian lower bound and the proved domain mappings.
-/

public section

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace HarmonicMaps

/-- The determinant of a domain endomorphism agrees with the matrix of its
actual columns in the standard Euclidean basis, including dimension zero. -/
theorem domain_clm_det_eq_matrix_det {n : ℕ} (B : Domain n →L[ℝ] Domain n) :
    B.det = Matrix.det (fun i j : Fin n => (B (EuclideanSpace.single j 1)) i) := by
  rw [ContinuousLinearMap.det,
    ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
  congr 1

/-- A positive lower bound for the genuine Jacobian of an injective
differentiable map gives a sharp restricted pushforward bound. -/
theorem map_restrict_le_inv_det_of_differentiable {n : ℕ}
    {F : Domain n → Domain n} {S T : Set (Domain n)} {d : ℝ}
    (hF : Differentiable ℝ F) (hinj : Function.Injective F)
    (hS : MeasurableSet S) (hd : 0 < d)
    (hdet : ∀ x ∈ S, d ≤ |(fderiv ℝ F x).det|) (hmaps : MapsTo F S T) :
    Measure.map F (volume.restrict S) ≤ ENNReal.ofReal d⁻¹ • volume.restrict T := by
  refine Measure.le_iff.mpr ?_
  intro V hV
  rw [Measure.map_apply hF.continuous.measurable hV,
    Measure.restrict_apply (hF.continuous.measurable hV),
    Measure.smul_apply, Measure.restrict_apply hV, smul_eq_mul,
    ENNReal.ofReal_inv_of_pos hd]
  have hpre : MeasurableSet (F ⁻¹' V ∩ S) :=
    (hF.continuous.measurable hV).inter hS
  have hJac : ENNReal.ofReal d * volume (F ⁻¹' V ∩ S) ≤
      volume (F '' (F ⁻¹' V ∩ S)) := by
    calc
      ENNReal.ofReal d * volume (F ⁻¹' V ∩ S) =
          ∫⁻ _ in F ⁻¹' V ∩ S, ENNReal.ofReal d := by
        rw [lintegral_const, Measure.restrict_apply_univ]
      _ ≤ ∫⁻ x in F ⁻¹' V ∩ S, ENNReal.ofReal |(fderiv ℝ F x).det| := by
        apply setLIntegral_mono' hpre
        intro x hx
        exact ENNReal.ofReal_le_ofReal (hdet x hx.2)
      _ = volume (F '' (F ⁻¹' V ∩ S)) :=
        lintegral_abs_det_fderiv_eq_addHaar_image volume hpre
          (fun x _ => (hF x).hasFDerivAt.hasFDerivWithinAt) hinj.injOn
  have hsubset : F '' (F ⁻¹' V ∩ S) ⊆ V ∩ T := by
    rintro z ⟨x, hx, rfl⟩
    exact ⟨hx.1, hmaps hx.2⟩
  have hbound := mul_le_mul_right (hJac.trans (measure_mono hsubset))
    (ENNReal.ofReal d)⁻¹
  simpa only [ENNReal.inv_mul_cancel_left (ENNReal.ofReal_ne_zero_iff.mpr hd)
    ENNReal.ofReal_ne_top] using hbound

/-- The complete source cutoff assumptions give both sharp forward
pushforward estimates. Nonnegativity of `L` follows from the derivative bound. -/
theorem variableShift_map_restrict_le {n : ℕ} {s : Domain n → ℝ}
    {theta delta hbar L : ℝ}
    (hdelta : 0 < delta) (htheta : delta < theta)
    (hhalf : theta + 2 * delta < 1 / 2)
    (hs : ContDiff ℝ ∞ s)
    (hradial : ∀ x z : Domain n, ‖x‖ = ‖z‖ → s x = s z)
    (hvalues : ∀ x, 0 ≤ s x ∧ s x ≤ hbar)
    (hplateau : ∀ x ∈ Metric.ball (0 : Domain n) theta, s x = hbar)
    (hoff : ∀ x ∉ Metric.ball (0 : Domain n) (theta + delta), s x = 0)
    (hhbar : hbar ≤ delta) (hDs : ∀ x, ‖fderiv ℝ s x‖ ≤ L)
    (hL : L ≤ 1 / 4) (y : Domain n) (hy : y ∈ Metric.ball 0 1) :
    Measure.map (variableShift s y)
        (volume.restrict (Metric.ball 0 (theta + 2 * delta))) ≤
      ENNReal.ofReal (1 - L)⁻¹ • volume.restrict (Metric.ball 0 (theta + 2 * delta)) ∧
    Measure.map (variableShift s y)
        (volume.restrict (Metric.ball 0 (theta + delta) \ Metric.closedBall 0 theta)) ≤
      ENNReal.ofReal (1 - L)⁻¹ •
        volume.restrict (Metric.ball 0 (theta + 2 * delta) \
          Metric.closedBall 0 (theta - delta)) := by
  have hL0 : 0 ≤ L := (norm_nonneg (fderiv ℝ s (0 : Domain n))).trans (hDs 0)
  obtain ⟨hforward, _, _, hJac, hpos, _, _, _, _, hinverse, _, houter, _, hshell, _⟩ :=
    variableShift_diffeomorphism hdelta htheta hhalf hs hradial hvalues hplateau
      hoff hhbar hDs hL0 hL y hy
  obtain ⟨g, hg, _⟩ := hinverse
  have hinj : Function.Injective (variableShift s y) := by
    intro x z hxz
    rw [← hg.2.1 x, ← hg.2.1 z, hxz]
  have hdet : ∀ x, 1 - L ≤ |(fderiv ℝ (variableShift s y) x).det| := by
    intro x
    rw [domain_clm_det_eq_matrix_det]
    exact (hJac x).trans (le_abs_self _)
  have hU : MapsTo (variableShift s y) (Metric.ball 0 (theta + 2 * delta))
      (Metric.ball 0 (theta + 2 * delta)) := by
    intro x hx
    rw [← houter]
    exact mem_image_of_mem _ hx
  exact ⟨map_restrict_le_inv_det_of_differentiable
      (hforward.differentiable (by simp)) hinj measurableSet_ball
      hpos (fun x _ => hdet x) hU,
    map_restrict_le_inv_det_of_differentiable
      (hforward.differentiable (by simp)) hinj
      (measurableSet_ball.diff measurableSet_closedBall)
      hpos (fun x _ => hdet x) hshell⟩

end HarmonicMaps
