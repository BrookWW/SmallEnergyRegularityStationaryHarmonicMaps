module

public import HarmonicMaps.Analysis.BallPolarIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Absolute continuity and derivatives of ball integrals

The actual ball integral is represented by a primitive of its integrable
polar boundary density. This gives absolute continuity through both endpoints
and the radius derivative almost everywhere in the interior.
-/

public section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace HarmonicMaps

/-- Polar representation on every radius in a closed interval, including its
zero and outer endpoints. -/
theorem integral_ball_eq_intervalIntegral_polar {n : ℕ} (hn : 0 < n)
    {f : Domain n → ℝ} {a : Domain n} {R r : ℝ}
    (hf : IntegrableOn f (Metric.ball a R) volume) (hr : r ∈ Icc 0 R) :
    (∫ x in Metric.ball a r, f x) = ∫ t in (0 : ℝ)..r, t ^ (n - 1) *
      ∫ θ : Metric.sphere (0 : Domain n) 1, f (a + t • θ.val)
        ∂(volume : Measure (Domain n)).toSphere := by
  rw [integral_ball_eq_polar hn (hf.mono_set (Metric.ball_subset_ball hr.2)),
    intervalIntegral.integral_of_le hr.1, integral_Ioc_eq_integral_Ioo]

private theorem absolutelyContinuous_congrOn {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (he : EqOn f g (uIcc a b)) :
    AbsolutelyContinuousOnInterval g a b := by
  apply hf.congr'
  have hm : ∀ᶠ E in AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
      𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b),
      E ∈ AbsolutelyContinuousOnInterval.disjWithin a b :=
    (eventually_principal.mpr (fun _ h => h)).filter_mono inf_le_right
  filter_upwards [hm] with E hE
  apply Finset.sum_congr rfl
  intro i hi
  rw [he (hE.1 i hi).1, he (hE.1 i hi).2]

/-- The genuine ball integral is absolutely continuous on the whole closed
radius interval for every L1 density, without a nonnegativity assumption. -/
theorem absolutelyContinuousOnInterval_integral_ball {n : ℕ} (hn : 0 < n)
    {f : Domain n → ℝ} {a : Domain n} {R : ℝ} (hR : 0 ≤ R)
    (hf : IntegrableOn f (Metric.ball a R) volume) :
    AbsolutelyContinuousOnInterval (fun r => ∫ x in Metric.ball a r, f x) 0 R := by
  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le hR).mpr
    (integrableOn_polar_boundary_density hn hf)
  have hac := hi.absolutelyContinuousOnInterval_intervalIntegral
    (show (0 : ℝ) ∈ uIcc 0 R from left_mem_uIcc)
  apply absolutelyContinuous_congrOn hac
  intro r hr
  rw [uIcc_of_le hR] at hr
  exact (integral_ball_eq_intervalIntegral_polar hn hf hr).symm

/-- Almost every interior radius differentiates the actual ball integral to
its polar boundary density with the exact Jacobian. -/
theorem ae_hasDerivAt_integral_ball {n : ℕ} (hn : 0 < n)
    {f : Domain n → ℝ} {a : Domain n} {R : ℝ} (hR : 0 ≤ R)
    (hf : IntegrableOn f (Metric.ball a R) volume) :
    ∀ᵐ r : ℝ, r ∈ Ioo 0 R →
      HasDerivAt (fun t => ∫ x in Metric.ball a t, f x)
        (r ^ (n - 1) * ∫ θ : Metric.sphere (0 : Domain n) 1,
          f (a + r • θ.val) ∂(volume : Measure (Domain n)).toSphere) r := by
  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le hR).mpr
    (integrableOn_polar_boundary_density hn hf)
  filter_upwards [hi.ae_hasDerivAt_integral] with r hr
  intro hrR
  have hd := hr (by simpa only [uIcc_of_le hR] using (show r ∈ Icc 0 R from ⟨hrR.1.le, hrR.2.le⟩)) 0 left_mem_uIcc
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hrR.1 hrR.2] with t ht
  exact integral_ball_eq_intervalIntegral_polar hn hf ⟨ht.1.le, ht.2.le⟩

end HarmonicMaps
