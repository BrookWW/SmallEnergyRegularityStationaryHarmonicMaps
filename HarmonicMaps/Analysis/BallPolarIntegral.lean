module

public import HarmonicMaps.Analysis.RadialIntegrabilityPolar
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Polar representations of ball integrals

The angular measure is the canonical polar measure `volume.toSphere`.
All change-of-variables and Fubini steps use actual integrability.
-/

public section

open MeasureTheory Set
open scoped BigOperators

namespace HarmonicMaps

/-- An integrable function remains integrable in translated polar coordinates. -/
theorem integrable_polar_coordinates {n : ℕ} {f : Domain n → ℝ}
    (hf : Integrable f volume) (a : Domain n) :
    Integrable (fun p : Metric.sphere (0 : Domain n) 1 × Ioi (0 : ℝ) =>
      f (a + p.2.val • p.1.val))
      ((volume : Measure (Domain n)).toSphere.prod (Measure.volumeIoiPow (n - 1))) := by
  have ht := hf.comp_add_left a
  have hs : Integrable
      ((fun x : Domain n => f (a + x)) ∘ (↑) : ({(0 : Domain n)}ᶜ : Set (Domain n)) → ℝ)
      ((volume : Measure (Domain n)).comap
        (Subtype.val : ({(0 : Domain n)}ᶜ : Set (Domain n)) → Domain n)) :=
    (integrableOn_iff_comap_subtypeVal (measurableSet_singleton (0 : Domain n)).compl).mp
      ht.integrableOn
  have hm := (volume : Measure (Domain n)).measurePreserving_homeomorphUnitSphereProd
  have hh := (hm.integrable_comp_emb (Homeomorph.measurableEmbedding _)
    (g := fun p => f (a + ((homeomorphUnitSphereProd (Domain n)).symm p).val))).mp
    (by simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using hs)
  simpa only [homeomorphUnitSphereProd_symm_apply_coe, finrank_euclideanSpace,
    Fintype.card_fin] using hh

/-- Integration in translated polar coordinates, with the exact Jacobian. -/
theorem integral_eq_polar {n : ℕ} (hn : 0 < n) {f : Domain n → ℝ}
    (hf : Integrable f volume) (a : Domain n) :
    (∫ x, f x) = ∫ r in Ioi (0 : ℝ), r ^ (n - 1) *
      ∫ θ : Metric.sphere (0 : Domain n) 1, f (a + r • θ.val)
        ∂(volume : Measure (Domain n)).toSphere := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hm := (volume : Measure (Domain n)).measurePreserving_homeomorphUnitSphereProd
  calc
    (∫ x, f x) = ∫ x : Domain n, f (a + x) := (integral_add_left_eq_self f a).symm
    _ = ∫ x : ({(0 : Domain n)}ᶜ : Set (Domain n)), f (a + x.val)
        ∂((volume : Measure (Domain n)).comap (↑)) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl
        (fun x : Domain n => f (a + x)),
        restrict_compl_singleton]
    _ = ∫ p : Metric.sphere (0 : Domain n) 1 × Ioi (0 : ℝ),
        f (a + p.2.val • p.1.val)
        ∂((volume : Measure (Domain n)).toSphere.prod (Measure.volumeIoiPow (n - 1))) := by
      have he := hm.integral_comp (Homeomorph.measurableEmbedding _)
        (fun p => f (a + ((homeomorphUnitSphereProd (Domain n)).symm p).val))
      simpa only [Homeomorph.symm_apply_apply, homeomorphUnitSphereProd_symm_apply_coe,
        finrank_euclideanSpace, Fintype.card_fin] using he
    _ = ∫ r : Ioi (0 : ℝ), (∫ θ : Metric.sphere (0 : Domain n) 1,
        f (a + r.val • θ.val) ∂(volume : Measure (Domain n)).toSphere)
        ∂Measure.volumeIoiPow (n - 1) := integral_prod_symm _ (integrable_polar_coordinates hf a)
    _ = _ := by
      simp only [Measure.volumeIoiPow, ENNReal.ofReal]
      rw [integral_withDensity_eq_integral_smul]
      · rw [integral_subtype_comap measurableSet_Ioi
          (fun r : ℝ => Real.toNNReal (r ^ (n - 1)) •
            ∫ θ : Metric.sphere (0 : Domain n) 1, f (a + r • θ.val)
              ∂(volume : Measure (Domain n)).toSphere)]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        dsimp only
        rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hr.le _), smul_eq_mul]
      · exact (measurable_subtype_coe.pow_const _).real_toNNReal

/-- The open ball integral equals its polar integral on the exact radius range. -/
theorem integral_ball_eq_polar {n : ℕ} (hn : 0 < n)
    {f : Domain n → ℝ} {a : Domain n} {R : ℝ}
    (hf : IntegrableOn f (Metric.ball a R) volume) :
    (∫ x in Metric.ball a R, f x) =
      ∫ r in Ioo (0 : ℝ) R, r ^ (n - 1) *
        ∫ θ : Metric.sphere (0 : Domain n) 1, f (a + r • θ.val)
          ∂(volume : Measure (Domain n)).toSphere := by
  have hg : Integrable ((Metric.ball a R).indicator f) volume :=
    (integrable_indicator_iff Metric.isOpen_ball.measurableSet).mpr hf
  rw [← integral_indicator Metric.isOpen_ball.measurableSet, integral_eq_polar hn hg a]
  calc
    _ = ∫ r in Ioi (0 : ℝ), (Iio R).indicator (fun r => r ^ (n - 1) *
        ∫ θ : Metric.sphere (0 : Domain n) 1, f (a + r • θ.val)
          ∂(volume : Measure (Domain n)).toSphere) r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      have hdist (θ : Metric.sphere (0 : Domain n) 1) : dist (a + r • θ.val) a = r := by
        rw [dist_eq_norm_sub, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le]
        have hθ : ‖θ.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
        rw [hθ, mul_one]
      by_cases hrR : r < R
      · rw [indicator_of_mem (show r ∈ Iio R from hrR)]
        apply congrArg (fun z : ℝ => r ^ (n - 1) * z)
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun θ => indicator_of_mem
          (by rwa [Metric.mem_ball, hdist]) f
      · rw [indicator_of_notMem (show r ∉ Iio R from hrR)]
        have he : (fun θ : Metric.sphere (0 : Domain n) 1 =>
            (Metric.ball a R).indicator f (a + r • θ.val)) = fun _ => 0 := by
          funext θ
          exact indicator_of_notMem (by rwa [Metric.mem_ball, hdist]) f
        rw [he, integral_zero, mul_zero]
    _ = _ := by rw [setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio]

end HarmonicMaps
